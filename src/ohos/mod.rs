use std::borrow::Cow;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc, Mutex, OnceLock};

use super::WebViewAttributes;
use crate::{
  custom_protocol_workaround, Error, PageLoadEvent, Rect, RequestAsyncResponder, Result, RGBA,
};
use cookie::Cookie;
use http::{Request, Response, Uri};
use openharmony_ability::MainThreadStatus;
use openharmony_ability_plugin_webview::{
  Either, WebviewCallbacksBuilder, WebviewClient, WebviewCreateRequest,
  WebviewDownloadStartResponse, WebviewHandle, WebviewHttpsInterceptResponse,
  WebviewInitializationScript, WebviewJavascriptProxyBuilder, WebviewPdfConfig, WebviewProtocol,
  WebviewProtocolOptions, WebviewStyle,
};

/// Re-exported so the runtime layer (`tauri-runtime-wry`) can register the
/// WebView bridge plugin on the `OpenHarmonyApp` during OHOS app setup.
/// `WebviewClient::create` is a bridge call routed through this plugin; without
/// registering it, `create` fails with "not installed for '<module>'".
pub use openharmony_ability_plugin_webview::WebviewBridgePlugin;

/// Sets up the synchronous webview-cookie bridge (`ohos.webview-cookie`) used
/// by main-thread `cookies_for_url` calls: registers the plugin on the app and
/// caches the app handle for the sync calls. Call once during OHOS app setup —
/// mirrors `tray_icon::set_ohos_app`.
///
/// The ArkTS counterpart (`WebviewCookiePlugin`) must be present in the host
/// Ability's `bridgePlugins` list; without it the main-thread cookie fetch
/// fails with an explicit bridge error (no silent empty results).
///
/// Registration errors are not propagated: on failure this logs via
/// `log::error!` and returns normally (same swallow semantics as
/// `tray_icon::set_ohos_app`). A swallowed failure then surfaces as an
/// explicit `Err` from the first main-thread `cookies_for_url` call
/// ("webview cookie sync app not set — the embedding runtime must call
/// wry::set_ohos_app during setup"), never as silent empty results.
/// Calling this twice is harmless: the second registration attempt is
/// rejected by the bridge registry and only logged; the first
/// registration stays in effect.
pub fn set_ohos_app(app: openharmony_ability::OpenHarmonyApp) {
  if let Err(e) = openharmony_ability_plugin_webview::set_cookie_sync_app(&app) {
    log::error!(
      "[wry] failed to set up the webview-cookie sync bridge: {}",
      e
    );
  }
}

/// #198 (design D6): the display virtual-pixel ratio (vp) used to convert
/// window physical coordinates into ArkUI vp units for webview geometry
/// (`create` child bounds and [`InnerWebView::set_bounds`]). Thin wrapper over
/// the ability binding `openharmony_ability::virtual_pixel_ratio` (which
/// already falls back to 1.0 on a <=0/absent binding); this second guard keeps
/// the f32->f64 widening total so geometry conversion never divides by zero or
/// NaN. The live ratio is device-real: the OHOS desktop reference device
/// reports vp = 1.9, so physical px is divided by vp before it reaches ArkUI
/// vp units. Where the binding is absent (host builds and unit tests) the
/// fallback is 1.0 -- there the division is an identity and UT numbers stay
/// bit-identical. That 1.0 is the code's stub for the absent-binding case,
/// not a measured figure; the only measured device figure quoted here is the
/// reference device's vp = 1.9.
pub(crate) fn vp_ratio_sanitized(vp: f64) -> f64 {
  if vp.is_finite() && vp > 0.0 {
    vp
  } else {
    1.0
  }
}

pub(crate) fn virtual_pixel_ratio() -> f64 {
  vp_ratio_sanitized(openharmony_ability::virtual_pixel_ratio() as f64)
}

/// #198: the physical->ArkUI-vp conversion applied to webview geometry
/// positions, through `dpi`'s `to_logical` (a `Physical` input is divided by
/// `vp`; a `Logical` input is an identity). A named fn keeps the
/// vp=1-identity / vp=2-halving contract unit-testable without a live
/// display binding.
///
/// Gate F6 (PR#26 review round 2): a `Physical` component carrying the
/// [`I32_MIN_SENTINEL`] is screened BEFORE the division. The ArkTS render
/// layer receives logical values and identifies unset components by exact
/// equality with the sentinel; a blind `x / vp` would destroy that exact
/// value (i32::MIN / 1.9 != i32::MIN) and the sentinel would be applied as a
/// real position. A sentinel component therefore maps 1:1 onto the sentinel
/// logical value - the cache merge ([`merge_bounds_into_cache`]) and the
/// ArkTS side then judge the identical value. `Logical` inputs need no
/// screening: `to_logical` is an identity there, so a sentinel component
/// already reaches the render layer untouched.
pub(crate) fn geometry_to_logical_vp(value: dpi::Position, vp: f64) -> (f64, f64) {
  let (raw_x, raw_y) = position_components(value);
  let (x, y): (f64, f64) = value.to_logical::<f64>(vp).into();
  (
    if raw_x == I32_MIN_SENTINEL {
      I32_MIN_SENTINEL
    } else {
      x
    },
    if raw_y == I32_MIN_SENTINEL {
      I32_MIN_SENTINEL
    } else {
      y
    },
  )
}

/// Same conversion for geometry sizes ([`dpi::Size`]).
///
/// No sentinel arm here (Gate F6 doc note): the sentinel is `i32::MIN`
/// widened to f64, and a `PhysicalSize` component is a `u32` widened to f64,
/// so it can never equal the negative sentinel - the vp division cannot
/// destroy one. A `LogicalSize` sentinel pair passes through `to_logical`
/// unchanged.
pub(crate) fn size_to_logical_vp(value: dpi::Size, vp: f64) -> (f64, f64) {
  value.to_logical::<f64>(vp).into()
}

// --- ability-F6: sentinel-safe bounds cache merge --------------------------------

/// The "component not set by this call" sentinel of the cross-repo OHOS wire
/// contract (tauri-runtime-wry `OHOS_BOUNDS_UNSET`, issue
/// Eulogizethesun/tauri#241): `i32::MIN` widened to f64. tauri-runtime-wry
/// sends it as a LOGICAL whole-axis pair (`ohos_unspecified_position` /
/// `ohos_unspecified_size`) so the exact value reaches the ArkTS render layer,
/// which skips sentinel components and applies only the set ones.
const I32_MIN_SENTINEL: f64 = i32::MIN as f64;

/// Raw (x, y) components of a `dpi::Position` with NO logical/physical
/// conversion; sentinel screening must compare the caller's own units.
fn position_components(p: dpi::Position) -> (f64, f64) {
  match p {
    dpi::Position::Physical(v) => (f64::from(v.x), f64::from(v.y)),
    dpi::Position::Logical(v) => (v.x, v.y),
  }
}

/// Raw (width, height) components of a `dpi::Size` with NO logical/physical
/// conversion.
fn size_components(s: dpi::Size) -> (f64, f64) {
  match s {
    dpi::Size::Physical(v) => (f64::from(v.width), f64::from(v.height)),
    dpi::Size::Logical(v) => (v.width, v.height),
  }
}

/// ability-F6: the cache write of [`InnerWebView::set_bounds`]. A request
/// carrying the [`I32_MIN_SENTINEL`] in a component is a partial update for
/// that component ("this component is not set"); writing it into the public
/// bounds cache would hand `bounds()` readers -2147483648.0 as a real
/// position/size.
///
/// Gate F5 (PR#26 review round 2): the merge is per COMPONENT, matching the
/// ArkTS render layer's granularity (it skips sentinel components and
/// applies only the set ones). Whether a single-component sentinel can
/// arrive splits by input surface. The internal producers -
/// tauri-runtime-wry's own construction sites - never emit a
/// single-component sentinel: the `SetSize` and `SetPosition` construction
/// sites send whole-axis sentinel pairs (`SetSize` rides
/// `ohos_unspecified_position()`, `SetPosition` rides
/// `ohos_unspecified_size()`, issue Eulogizethesun/tauri#241) while the
/// auto-resize re-apply leg sends all-real components (every rate times the
/// new window size, zero sentinels); no internal site hand-mixes a
/// single-component sentinel. But the public `set_bounds`
/// surface - a direct-wry consumer, or an application author whose request
/// passes through tauri core unchanged - can hand-craft a mixed partial such
/// as `Position::Logical(i32::MIN, 100.0)` today. Such a request is
/// REACHABLE input, not a hypothetical: per the wire contract (`i32::MIN` =
/// this component unset) a deliberate hand-crafted mix is a legal request,
/// so the per-component merge handles reachable input rather than being
/// purely defensive. Second-hop disclosure (review round 5): that legality
/// and this merge hold at the wry hop; the same input, relayed through
/// tauri core, also reaches runtime-wry's `WebviewMessage::SetBounds`
/// rate-cache write, which does NOT screen sentinels - it writes all four
/// rates (`x_rate`/`y_rate`/`width_rate`/`height_rate`) unconditionally for
/// a webview holding a rate cache, whereas the `SetSize` arm writes only
/// the width/height rates and the `SetPosition` arm only the x/y rates (the
/// sentinel component is not written). A hand-mixed sentinel therefore puts
/// `i32::MIN`-derived garbage values into that rate cache (only for a
/// webview holding a rate cache: on OHOS that is one created with explicit
/// bounds AND auto_resize armed at create; runtime arming never creates a
/// holder there because the `SetAutoResize` enable leg is a no-op on OHOS -
/// only desktop's enable leg re-derives rates from the live bounds), and the
/// next `TaoWindowEvent::Resized` fires the
/// auto-resize re-apply leg, which multiplies the garbage rates by the new
/// window size into a full real `Rect` and re-sends it - applied as usual.
/// The consequence is bounded and recoverable (any later real `set_bounds`
/// overwrites the rates), and the trigger requires an application author to
/// deliberately hand-craft `i32::MIN` components (pathological input); the
/// wry-side bounds-cache read-back invariant is unaffected. That second-hop
/// screening gap is a disclosed cross-repo limitation (issue
/// Eulogizethesun/tauri#241), not a defensive failure of this merge. Future
/// per-axis protocol growth is a further motive for the same behavior; the
/// F5 UT exists to pin this formula's correctness for that input class, not
/// to describe a production defect.
/// Per-component updates stay within one dpi variant
/// (a variant switch would mix units without a scale factor); a cross-variant
/// axis is only replaced when ALL of its components are set, otherwise the
/// cached axis is kept wholesale (conservative, the pre-F5 whole-axis
/// behavior).
///
/// The dispatched `PendingOp::SetBounds` is unaffected either way: the wire
/// carries the vp-converted request and the ArkTS render layer does its own
/// sentinel skipping; this merge only governs the read-back bookkeeping.
fn merge_bounds_into_cache(cache: &mut Rect, incoming: Rect) {
  let (ix, iy) = position_components(incoming.position);
  let x_set = ix != I32_MIN_SENTINEL;
  let y_set = iy != I32_MIN_SENTINEL;
  match (&mut cache.position, incoming.position) {
    // Same-variant: true per-component merge - the units are comparable.
    (dpi::Position::Logical(c), dpi::Position::Logical(i)) => {
      if x_set {
        c.x = i.x;
      }
      if y_set {
        c.y = i.y;
      }
    }
    // Physical positions are i32 pairs, so the (negative) sentinel CAN ride
    // here; the screening above governs each component independently.
    (dpi::Position::Physical(c), dpi::Position::Physical(i)) => {
      if x_set {
        c.x = i.x;
      }
      if y_set {
        c.y = i.y;
      }
    }
    // Cross-variant: only a full-axis replace is unit-safe; a cross-variant
    // mixed partial keeps the cached axis wholesale.
    (cached, incoming) => {
      if x_set && y_set {
        *cached = incoming;
      }
    }
  }
  let (iw, ih) = size_components(incoming.size);
  let w_set = iw != I32_MIN_SENTINEL;
  let h_set = ih != I32_MIN_SENTINEL;
  match (&mut cache.size, incoming.size) {
    (dpi::Size::Logical(c), dpi::Size::Logical(i)) => {
      if w_set {
        c.width = i.width;
      }
      if h_set {
        c.height = i.height;
      }
    }
    // A PhysicalSize component is u32 widened to f64 and can never equal the
    // negative sentinel, so this arm is always a full replace.
    (dpi::Size::Physical(c), dpi::Size::Physical(i)) => {
      if w_set {
        c.width = i.width;
      }
      if h_set {
        c.height = i.height;
      }
    }
    (cached, incoming) => {
      if w_set && h_set {
        *cached = incoming;
      }
    }
  }
}

/// #189: the disposal idempotence fence shared by `dispose_child` and `Drop`.
/// Returns `true` exactly once per webview -- the first caller wins and owes
/// the `Remove` dispatch; every later call (including a double Drop) is a
/// no-op. Main and child webviews share this path: the old `is_child` gate
/// that let main webviews leak their ArkTS component is gone.
fn dispose_once(disposed: &AtomicBool) -> bool {
  !disposed.swap(true, Ordering::SeqCst)
}

// --- #192: url() three-state main-thread sync refresh ---------------------------

/// Refreshes `cache` from the live controller URL through the `ohos.webview-url`
/// main-thread sync bridge (ArkTS `getUrlSync`). Runs ONLY on the NAPI main
/// thread -- the MainThreadSync bridge contract (`with_main_thread_bridge` is a
/// re-entrant direct call, so there is no timeout construct on this path at
/// all: zero recv_timeout, zero block_on). Any failure -- sync app not
/// registered, main-thread Env gone, bridge error -- keeps the cached value
/// with a debug log: `url()` never fails just because the sync bridge does.
fn refresh_url_cache_from_bridge(webview_id: &str, cache: &Mutex<String>) {
  match openharmony_ability_plugin_webview::webview_url_on_main_thread(webview_id) {
    Ok(url) => *cache.lock().unwrap() = url,
    Err(e) => log::debug!("[wry] url(): main-thread sync bridge failed, keeping cached url: {e}"),
  }
}

/// #192 (design D4): three-state router behind [`InnerWebView::url`], mirroring
/// the `cookies_for_url` main-thread classification:
///
/// 1. **Main** -- the async bridge is unusable on the main thread (its TSFN
///    response needs this very thread to pump), so the URL is refreshed
///    synchronously through the dedicated `ohos.webview-url` MainThreadSync
///    plugin and written back to the cache. This closes the stale-cache gap
///    after SPA pushState navigation, which the page-begin/end event cache
///    never observes.
/// 2. **Worker** -- zero bridge traffic: return the cache (prefilled with the
///    initial URL at creation, updated by page events).
/// 3. **Uninitialized** (render entry not yet run) -- thread classification is
///    impossible, so no bridge call is safe either way: return the cache.
///
/// No path blocks: the only bridge touch is the re-entrant MainThreadSync
/// direct call on the main thread.
fn url_with_main_thread_refresh(
  status: MainThreadStatus,
  webview_id: &str,
  cache: &Mutex<String>,
) -> Result<String> {
  match status {
    MainThreadStatus::Main => refresh_url_cache_from_bridge(webview_id, cache),
    MainThreadStatus::Worker | MainThreadStatus::Uninitialized => {}
  }
  Ok(cache.lock().unwrap().clone())
}

/// Configuration for PDF generation. All fields are optional; when a field is
/// `None` the ArkTS side falls back to its defaults (A4 8.27×11.69in, zero
/// margins, background printing on). Provided values are forwarded through the
/// bridge (`WebviewPdfConfig`) and mapped per-field into ArkWeb's
/// `PdfConfiguration` (width/height in inches) — see WebviewPlugin.ets
/// `createPdf`. `scale` is forwarded into `PdfConfiguration.scale` (ArkTS
/// side, #233; the system field is @since 20) instead of being dropped.
pub struct PdfConfig {
  pub width: Option<f64>,
  pub height: Option<f64>,
  pub margin_top: Option<f64>,
  pub margin_bottom: Option<f64>,
  pub margin_left: Option<f64>,
  pub margin_right: Option<f64>,
  pub scale: Option<f64>,
  pub should_print_background: Option<bool>,
}

use crate::util::Counter;

/// Re-export of `openharmony_ability_plugin_webview::WebviewHandle` for use in wry's public API.
pub type OhosWebviewHandle = WebviewHandle;

static COUNTER: Counter = Counter::new();

// ─── SendSyncBox: unsafe wrapper for non-Send wry handlers ──────────────────────

/// Wrapper that makes any `T` `Send + Sync`.
///
/// **SAFETY**: The wrapped callback is only ever invoked from the NAPI main thread
/// (bridge reverse-event callbacks). The wry handler API (`Box<dyn Fn...>`) doesn't
/// require `Send`, but in practice all handlers are `Send` (they use `Arc`, `String`,
/// channels). The bridge callback registry requires `Send + Sync + 'static`, so we
/// wrap the handlers to satisfy the type system. This follows the same pattern as
/// Android's `UnsafeIpc` / `UnsafeTitleHandler` wrappers.
struct SendSyncBox<T>(T);
unsafe impl<T> Send for SendSyncBox<T> {}
unsafe impl<T> Sync for SendSyncBox<T> {}

// ─── BridgeExecutor ──────────────────────────────────────────────────────────────

/// Background tokio runtime for spawning async bridge calls (fire-and-forget).
///
/// `WebviewHandle` methods are `async`. wry's public API is synchronous and cannot
/// `.await`. `BridgeExecutor` wraps a `tokio::runtime::Handle` from a dedicated
/// background thread (`ohos-wry-bridge-rt`) that drives a current-thread runtime.
/// Calling `spawn(future)` sends the future to that background thread to be polled.
/// The TSFN NonBlocking call inside the bridge returns immediately; the ArkTS callback
/// runs on the main thread — no deadlock.
#[derive(Clone)]
pub(crate) struct BridgeExecutor {
  handle: tokio::runtime::Handle,
  // Gate F5: the dedicated pump thread is retained so spawn sites can
  // synchronously detect a dead bridge runtime: that thread is the only
  // poller of the futures this executor enqueues.
  pump_thread: Arc<Mutex<std::thread::JoinHandle<()>>>,
}

impl BridgeExecutor {
  fn new() -> Self {
    // Shared across all webviews: one background thread + runtime for the whole
    // process, instead of one per webview (each InnerWebView used to spawn its
    // own `ohos-wry-bridge-rt` thread). `BridgeExecutor` is `Clone` and the
    // underlying handle is thread-safe, so all webviews multiplex the same
    // runtime.
    //
    // Thread classification for sync-vs-async dispatch lives in
    // `cookies_for_url` via openharmony-ability's render-entry signal
    // (`main_thread_status`), NOT here. The old design captured "the thread
    // that first constructed this executor" as the main thread — an unproven
    // assumption that misclassified direct-wry embedders building their first
    // webview on a worker, which was then misrecorded as main forever
    // (issue #145).
    static SHARED: OnceLock<BridgeExecutor> = OnceLock::new();
    SHARED.get_or_init(|| Self::new_exclusive()).clone()
  }

  fn new_exclusive() -> Self {
    let runtime = tokio::runtime::Builder::new_current_thread()
      .enable_all()
      .build()
      .expect("Failed to create wry bridge runtime");
    let handle = runtime.handle().clone();
    let pump_thread = std::thread::Builder::new()
      .name("ohos-wry-bridge-rt".into())
      .spawn(move || runtime.block_on(std::future::pending::<()>()))
      .expect("Failed to spawn wry bridge runtime thread");
    Self {
      handle,
      pump_thread: Arc::new(Mutex::new(pump_thread)),
    }
  }

  /// Gate F5: synchronous liveness probe for the bridge runtime. The pump
  /// thread is the only poller of spawned futures; once it has terminated
  /// (panic or return), every future enqueued from then on is never polled.
  /// `JoinHandle::is_finished` is a snapshot: a thread that dies right after
  /// this check is the disclosed residual gap (see `open_devtools`).
  pub(crate) fn pump_thread_alive(&self) -> bool {
    !self.pump_thread.lock().unwrap().is_finished()
  }

  /// Spawn a fire-and-forget bridge call. The result is ignored.
  ///
  /// Gate F5: this cannot report an enqueue failure: tokio 1.x
  /// `Handle::spawn` never fails the enqueue (a task bound onto a dead
  /// runtime is simply never polled, and no error surfaces). The two effects
  /// guarded against that silent loss are:
  /// - the devtools open intent - the process's execution point that
  ///   must not be lost: its dispatch sites consult
  ///   [`BridgeExecutor::pump_thread_alive`] (the ready-branch open right
  ///   after spawning, the pre-handshake queue arm before enqueueing) and
  ///   release the intent on a dead pump, and the create drain releases it
  ///   when its replay could never be polled;
  /// - the `set_bounds` cache write, skipped on a dead pump so `bounds()`
  ///   never reports set_bounds geometry the render layer never applied
  ///   (the create-time seed write is the disclosed exception - it seeds
  ///   the cache with the builder bounds before any application exists;
  ///   see the two MAIN creation rows on `WebView::bounds` whose cache
  ///   does not reflect applied geometry - the default placeholder row
  ///   and the requested-but-never-applied row; the second disclosed
  ///   exception: while the creation handshake is pending, a live pump
  ///   takes the queue arm (dispatch_or_queue_op queues the op and
  ///   returns Ok without applying it) yet the cache write still records
  ///   the request, so `bounds()` reports requested-but-not-yet-applied
  ///   geometry until the handshake completes and the queue drains).
  ///
  /// Every other op sent through here (eval, zoom, set_visible, focus,
  /// load_url, print, ...) stays silently lost on a dead pump - the
  /// disclosed bridge-dead surface, deliberately left as is (PR#26 review
  /// round 2, F3).
  pub(crate) fn spawn<F>(&self, future: F)
  where
    F: std::future::Future<Output = ()> + Send + 'static,
  {
    self.handle.spawn(future);
  }
}

// ─── PendingOp ───────────────────────────────────────────────────────────────────

/// Operations queued before `WebviewClient::create()` completes (delayed attach).
/// These are replayed in order once the handle is ready.
enum PendingOp {
  LoadUrl(String),
  LoadUrlWithHeaders(String, std::collections::BTreeMap<String, String>),
  LoadHtml(String),
  Reload,
  Zoom(f64),
  SetBackgroundColor(String),
  SetVisible(bool),
  SetBounds(f64, f64, f64, f64),
  Focus,
  ClearAllBrowsingData,
  SetCookie(String, String),
  Print(String),
  Eval(String, Option<Box<dyn Fn(String) + Send + 'static>>),
  CreatePdf(
    String,
    Option<WebviewPdfConfig>,
    Option<Box<dyn Fn(bool) + Send + 'static>>,
  ),
  Remove,
  /// #195: queued open_devtools -- `setWebDebuggingAccess(true)` issued while
  /// create was still pending, replayed by the create drain once the handshake
  /// completes. Only the open intent is queued (design D5); the process-level
  /// [`DEVTOOLS_ENABLED`] flag keeps repeat opens idempotent.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  SetDevtools,
}

impl PendingOp {
  async fn execute(self, handle: &WebviewHandle) {
    match self {
      PendingOp::LoadUrl(url) => {
        if let Err(e) = handle.load_url(url).await {
          log::warn!("[wry] pending load_url failed: {}", e);
        }
      }
      PendingOp::LoadUrlWithHeaders(url, headers) => {
        if let Err(e) = handle.load_url_with_headers(url, headers).await {
          log::warn!("[wry] pending load_url_with_headers failed: {}", e);
        }
      }
      PendingOp::LoadHtml(html) => {
        if let Err(e) = handle.load_html(html).await {
          log::warn!("[wry] pending load_html failed: {}", e);
        }
      }
      PendingOp::Reload => {
        if let Err(e) = handle.reload().await {
          log::warn!("[wry] pending reload failed: {}", e);
        }
      }
      PendingOp::Zoom(scale) => {
        if let Err(e) = handle.set_zoom(scale).await {
          log::warn!("[wry] pending set_zoom failed: {}", e);
        }
      }
      PendingOp::SetBackgroundColor(color) => {
        if let Err(e) = handle.set_background_color(color).await {
          log::warn!("[wry] pending set_background_color failed: {}", e);
        }
      }
      PendingOp::SetVisible(visible) => {
        if let Err(e) = handle.set_visible(visible).await {
          log::warn!("[wry] pending set_visible failed: {}", e);
        }
      }
      PendingOp::SetBounds(x, y, w, h) => {
        if let Err(e) = handle.set_bounds(x, y, w, h).await {
          log::warn!("[wry] pending set_bounds failed: {}", e);
        }
      }
      PendingOp::Focus => {
        if let Err(e) = handle.focus().await {
          log::warn!("[wry] pending focus failed: {}", e);
        }
      }
      PendingOp::ClearAllBrowsingData => {
        if let Err(e) = handle.clear_all_browsing_data().await {
          log::warn!("[wry] pending clear_all_browsing_data failed: {}", e);
        }
      }
      PendingOp::SetCookie(url, value) => {
        if let Err(e) = handle.set_cookie(url, value).await {
          log::warn!("[wry] pending set_cookie failed: {}", e);
        }
      }
      PendingOp::Print(path) => {
        if let Err(e) = handle.create_pdf(&path, None).await {
          log::warn!("[wry] pending create_pdf failed: {}", e);
        } else if let Err(e) = handle.print(&path).await {
          log::warn!("[wry] pending print failed: {}", e);
        }
      }
      PendingOp::Eval(js, callback) => {
        let result = handle.evaluate_script(js).await;
        if let Err(e) = &result {
          log::warn!("[wry] pending evaluate_script failed: {}", e);
        }
        // #194: the callback is invoked for both outcomes -- an eval failure
        // settles with the literal "null" instead of leaving the awaiting
        // promise pending forever.
        if let Some(cb) = callback {
          cb(eval_callback_payload(&result));
        }
      }
      PendingOp::CreatePdf(path, config, callback) => {
        let result = handle.create_pdf(&path, config).await;
        let success = result.is_ok();
        if let Some(cb) = callback {
          cb(success);
        }
      }
      PendingOp::Remove => {
        if let Err(e) = handle.remove().await {
          log::warn!("[wry] pending remove failed: {}", e);
        }
      }
      #[cfg(any(debug_assertions, feature = "devtools"))]
      PendingOp::SetDevtools => {
        // #195 replay: the open intent was recorded before the handshake; the
        // process-level DEVTOOLS_ENABLED flag was already set at the call
        // site, so this only needs the runtime channel.
        if let Err(e) = handle.set_web_debugging_access(true).await {
          // W26-4: this queued op is consumed either way -- it can never be
          // retried -- so a failed replay must release the intent. Leaving it
          // latched would make the idempotence gate swallow every later
          // open_devtools in this process (same policy as
          // `failed_create_cleanup` for never-replayable queued opens).
          devtools_open_failed("queued open_devtools replay", &e);
        }
      }
    }
  }
}

/// #195: process-level "devtools enabled" intent. ArkWeb
/// `setWebDebuggingAccess` is a process-static API, so the intent is recorded
/// here at the call site -- even while create is still pending and the runtime
/// channel is unreachable -- and kept in sync on close. It is also the
/// idempotence fence: an already-enabled flag means a prior open is queued
/// (or applied), so repeat opens dispatch nothing new.
///
/// W26-4: because the flag doubles as the idempotence fence, every dead or
/// failed open path releases it again -- a dead queue
/// ([`queue_pre_handshake_open`]), a failed create
/// ([`failed_create_cleanup`]), a failed replay (`PendingOp::SetDevtools`)
/// and a failed ready-branch dispatch ([`devtools_open_failed`]) -- so a
/// single failure can never block all later opens in the process.
///
/// Gate F5: the ready-branch dispatch additionally releases the intent when
/// the bridge runtime's pump thread is already dead at spawn time
/// ([`BridgeExecutor::pump_thread_alive`]). Known limitation (disclosed): if
/// that thread dies right after the check, the enable future is never polled,
/// so neither the enable nor its async failure handler runs and the intent
/// stays latched: a later `open_devtools` early-returns on the fence.
#[cfg(any(debug_assertions, feature = "devtools"))]
static DEVTOOLS_ENABLED: AtomicBool = AtomicBool::new(false);

/// #195: records the open intent and reports whether a dispatch/queue is
/// still owed (`true` = this call flipped the flag, so dispatch; `false` =
/// an open is already queued or applied -- idempotent no-op).
#[cfg(any(debug_assertions, feature = "devtools"))]
fn devtools_open_intent() -> bool {
  !DEVTOOLS_ENABLED.swap(true, Ordering::SeqCst)
}

/// #195: records the close intent (clears the flag so a later open can
/// dispatch again). The return mirrors [`devtools_open_intent`] for symmetry.
#[cfg(any(debug_assertions, feature = "devtools"))]
fn devtools_close_intent() -> bool {
  DEVTOOLS_ENABLED.swap(false, Ordering::SeqCst)
}

/// W26-4: shared failure handling for the two async enable paths -- the
/// ready-branch dispatch ([`InnerWebView::open_devtools`]) and the
/// `PendingOp::SetDevtools` replay. A failed `set_web_debugging_access(true)`
/// must release the process-level open intent: the flag is also the
/// idempotence fence, so a latched `true` would permanently swallow every
/// later `open_devtools` in this process. Same policy as
/// [`failed_create_cleanup`] for a queued open that can never replay.
/// Factored out so the device UT exercises the real failure path.
/// Device-gated: `src/ohos` is entirely `#[cfg(target_env = "ohos")]`, so its
/// UTs are only compiled and executed when the crate targets an
/// `*-unknown-linux-ohos` target (the aarch64 device or the x86_64
/// emulator); a host `cargo test` never builds them.
///
/// Race note (inherent to the async latch, identical to
/// [`failed_create_cleanup`]): a concurrent `open_devtools` that consulted the
/// still-latched flag before this release runs is not re-dispatched
/// automatically -- the next `open_devtools` call after the release does
/// dispatch again.
#[cfg(any(debug_assertions, feature = "devtools"))]
fn devtools_open_failed(context: &str, e: &dyn std::fmt::Display) {
  devtools_close_intent();
  log::warn!("[wry] {context} failed, open intent released: {}", e);
}

// ─── Type aliases ─────────────────────────────────────────────────────────────────

type ProtocolHandler = Box<dyn Fn(crate::WebViewId, Request<Vec<u8>>, RequestAsyncResponder)>;
type SharedProtocolHandler = Arc<SendSyncBox<ProtocolHandler>>;

// ─── InnerWebView ───────────────────────────────────────────────────────────────

/// Crate-private on purpose (upstream never exposes `InnerWebView` on any
/// platform); re-exported types live in `src/lib.rs`'s targeted `pub use`.
pub(crate) struct InnerWebView {
  id: String,
  /// Async-ready handle. Set when `WebviewClient::create()` completes.
  /// Uses `OnceLock` — set exactly once when create finishes.
  /// **TOCTOU guard**: `pending_ops` lock must be held when checking `handle.get()`
  /// and when setting the handle + draining pending ops.
  handle: Arc<OnceLock<WebviewHandle>>,
  /// Operations queued before create completes. Also serves as the TOCTOU guard lock.
  pending_ops: Arc<Mutex<Vec<PendingOp>>>,
  /// Set when `WebviewClient::create()` fails. Once set, `dispatch_or_queue`
  /// returns an error instead of queueing ops that would never be replayed.
  /// Guarded by the `pending_ops` lock (set and read while holding it).
  creation_error: Arc<Mutex<Option<String>>>,
  /// For constructing handles before create completes (used by webview_handle()).
  client: WebviewClient,
  runtime: BridgeExecutor,
  page_loaded: Arc<AtomicBool>,
  url_cache: Arc<Mutex<String>>,
  bounds_cache: Mutex<Rect>,
  /// Per-webview "devtools requested" flag - written by `open_devtools` /
  /// `close_devtools`, read by `is_devtools_open`. Every one of those is
  /// devtools-gated, so the field is too (Gate F11: otherwise it is a
  /// dead_code warning in a release build without the devtools feature).
  #[cfg(any(debug_assertions, feature = "devtools"))]
  devtools_open: AtomicBool,
  /// #188: the creation-time incognito flag (`WebViewAttributes.incognito`).
  /// The main-thread `cookies_for_url` sync bridge is id-less, so the store
  /// selector has to travel with the caller -- retained here and passed to
  /// `cookies_for_url_on_main_thread(url, incognito)`.
  incognito: bool,
  // #189: the `is_child` field was removed -- disposal is now unified for main
  // and child webviews ([`InnerWebView::dispose_child`]); child-only behavior
  // that remains (initial bounds conversion) uses the `new_inner` parameter.
  disposed: AtomicBool,
}

/// m5: failed-create cleanup -- a queued `SetDevtools` can never replay once
/// creation failed, so the process-level open intent must be released (a later
/// webview's `open_devtools` dispatches again instead of silently no-oping).
/// Ownership is exact: the queued open only exists when THIS webview flipped
/// the intent (an earlier applied open makes `open_devtools` an early-return
/// idempotent no-op, never a queue entry). Factored out of the create-failure
/// closure so the device UT exercises the real cleanup (device-gated: only
/// compiled and executed when targeting an `*-unknown-linux-ohos` target --
/// the aarch64 device or the x86_64 emulator).
fn failed_create_cleanup(guard: &mut Vec<PendingOp>) {
  #[cfg(any(debug_assertions, feature = "devtools"))]
  if guard.iter().any(|op| matches!(op, PendingOp::SetDevtools)) {
    devtools_close_intent();
  }
  // Queued ops can never execute -- drop them.
  guard.clear();
}

/// PR review fix W1: the pre-handshake open queue attempt, factored out of
/// [`InnerWebView::open_devtools`]'s `None` arm so the device UT exercises the
/// REAL open_devtools-layer failure handling (not just `dispatch_or_queue_op`).
/// Mirrors the m5 [`failed_create_cleanup`] semantics: when the queue is dead
/// (creation already failed) the queued open can never replay, so the
/// just-recorded process-level open intent must be released -- otherwise
/// `DEVTOOLS_ENABLED` latches `true` for the whole process and every later
/// webview's `open_devtools` silently no-ops forever.
#[cfg(any(debug_assertions, feature = "devtools"))]
fn queue_pre_handshake_open(
  pending_ops: &std::sync::Mutex<Vec<PendingOp>>,
  handle: &OnceLock<WebviewHandle>,
  creation_error: &std::sync::Mutex<Option<String>>,
  runtime: &BridgeExecutor,
) {
  if let Err(e) = dispatch_or_queue_op(
    pending_ops,
    handle,
    creation_error,
    runtime,
    PendingOp::SetDevtools,
  ) {
    // The queue rejected the open: release the intent so a later open (this
    // or any other webview) dispatches again instead of no-oping forever.
    devtools_close_intent();
    log::warn!(
      "[wry] open_devtools could not queue, open intent released: {}",
      e
    );
  }
}

/// m4: the dispatch-or-queue decision + enqueue, factored out of the inherent
/// method so the device UT exercises the REAL production path (queue /
/// creation-failed / ready branches) instead of pushing into a scratch Vec.
/// The parameters are exactly the `InnerWebView` fields the method touches --
/// no test-only seam. **TOCTOU guard** (unchanged): the `pending_ops` lock must
/// be held when checking `handle.get()` and when pushing the queued op.
///
/// Gate F2 (PR#26 review round 2): the queue arm refuses an op when the
/// bridge runtime's pump thread is already dead -- a queued op replays only
/// through the create drain, which is itself polled by that very thread -- so
/// the op surfaces an Err synchronously instead of sitting in a queue that
/// never drains. For the devtools open this Err is what makes
/// [`queue_pre_handshake_open`] release the process-level intent (making the
/// synchronous-Err claim true on the queue arm too); for every other op it
/// turns a silent never-replayed queue entry into a surfaced error.
fn dispatch_or_queue_op(
  pending_ops: &std::sync::Mutex<Vec<PendingOp>>,
  handle: &OnceLock<WebviewHandle>,
  creation_error: &std::sync::Mutex<Option<String>>,
  runtime: &BridgeExecutor,
  op: PendingOp,
) -> Result<()> {
  let mut guard = pending_ops.lock().unwrap();
  if let Some(handle) = handle.get() {
    // Handle is ready -- release lock and spawn
    let handle = handle.clone();
    drop(guard);
    runtime.spawn(async move {
      op.execute(&handle).await;
    });
    Ok(())
  } else if let Some(err) = creation_error.lock().unwrap().as_ref() {
    Err(Error::OpenHarmonyWebviewError(format!(
      "webview creation failed: {}",
      err
    )))
  } else if !runtime.pump_thread_alive() {
    // Gate F2: refuse the enqueue while the pump thread is dead. Residual
    // gap (disclosed): a thread dying right after this check still produces
    // a queue entry that never replays.
    Err(Error::OpenHarmonyWebviewError(
      "bridge runtime pump thread is dead; the queued op would never be replayed".into(),
    ))
  } else {
    // Not ready -- queue for replay after create
    guard.push(op);
    Ok(())
  }
}

/// Gate F3 + F10 (PR#26 review round 2): the `set_bounds` production body,
/// factored out of the inherent method exactly like [`dispatch_or_queue_op`]
/// so the device UT can drive the REAL public-path cache write (vp
/// conversion + dispatch + pump-guarded merge) without an `InnerWebView`:
/// `WebviewClient` needs a live NAPI bridge session and has no NAPI-free
/// constructor, so a UT cannot build the struct. The parameters are exactly
/// the fields the method touches - no test-only seam.
fn set_bounds_with_cache(
  pending_ops: &std::sync::Mutex<Vec<PendingOp>>,
  handle: &OnceLock<WebviewHandle>,
  creation_error: &std::sync::Mutex<Option<String>>,
  runtime: &BridgeExecutor,
  bounds_cache: &Mutex<Rect>,
  bounds: Rect,
) -> Result<()> {
  // #198: physical -> ArkUI vp via the live display ratio (was a hardcoded
  // 1.0; the absent-binding fallback 1.0 keeps host/UT values
  // bit-identical -- the desktop reference device reports vp=1.9).
  let vp = virtual_pixel_ratio();
  let (x, y) = geometry_to_logical_vp(bounds.position, vp);
  let (w, h) = size_to_logical_vp(bounds.size, vp);
  dispatch_or_queue_op(
    pending_ops,
    handle,
    creation_error,
    runtime,
    PendingOp::SetBounds(x, y, w, h),
  )?;
  // ability-F6: the cache write skips sentinel components (the
  // tauri-runtime-wry partial-bounds wire, issue Eulogizethesun/tauri#241), so
  // `bounds()` readers must never see -2147483648.0 as a real component.
  // Gate F3: with the pump thread dead the dispatch above is silently lost
  // (the disclosed bridge-dead surface for non-devtools ops) - skipping the
  // write keeps `bounds()` from reporting geometry the render layer never
  // applied. Scope carve-out (PR#26 review round 3): this promise covers the
  // set_bounds path only - the create-time seed write (Gate F4) is the
  // disclosed exception: it seeds the cache with the builder bounds before
  // any render-layer application exists, so on the two MAIN creation rows
  // documented on `WebView::bounds` the cache does not reflect applied
  // geometry (the default placeholder row and the requested-but-never-applied
  // row).
  // The second disclosed exception: while the creation handshake is
  // pending, a live pump takes the queue arm (dispatch_or_queue_op
  // queues the op and returns Ok without applying it) yet the cache
  // write below still records the request, so bounds() reports
  // requested-but-not-yet-applied geometry until the handshake
  // completes and the queue drains.
  // TOCTOU residual gap (disclosed): a thread dying right after this
  // check still leaves the cache written but unapplied.
  if runtime.pump_thread_alive() {
    merge_bounds_into_cache(&mut bounds_cache.lock().unwrap(), bounds);
  } else {
    log::warn!(
      "[wry] set_bounds: bridge runtime pump thread is dead; the request will never be applied and the bounds cache is left unchanged"
    );
  }
  Ok(())
}

impl InnerWebView {
  pub(crate) fn new_as_child(
    window: &impl raw_window_handle::HasWindowHandle,
    attributes: WebViewAttributes,
    pl_attrs: super::PlatformSpecificWebViewAttributes,
  ) -> Result<Self> {
    Self::new_inner(window, attributes, pl_attrs, true)
  }

  pub(crate) fn new(
    window: &impl raw_window_handle::HasWindowHandle,
    attributes: WebViewAttributes,
    pl_attrs: super::PlatformSpecificWebViewAttributes,
  ) -> Result<Self> {
    Self::new_inner(window, attributes, pl_attrs, false)
  }

  #[allow(clippy::too_many_lines)]
  fn new_inner(
    _window: &impl raw_window_handle::HasWindowHandle,
    attributes: WebViewAttributes,
    pl_attrs: super::PlatformSpecificWebViewAttributes,
    is_child: bool,
  ) -> Result<Self> {
    let WebViewAttributes {
      id,
      ref url,
      html,
      incognito,
      initialization_scripts,
      ipc_handler,
      #[cfg(any(debug_assertions, feature = "devtools"))]
      devtools,
      custom_protocols,
      background_color,
      transparent,
      visible,
      headers,
      autoplay,
      user_agent,
      javascript_disabled,
      navigation_handler,
      document_title_changed_handler,
      on_page_load_handler,
      new_window_req_handler,
      download_started_handler,
      download_completed_handler,
      bounds,
      clipboard,
      zoom_hotkeys_enabled,
      drag_drop_handler,
      ..
    } = attributes;

    let initial_url = url.clone();
    let initial_headers = headers;

    let id = id
      .map(|id| id.to_string())
      .unwrap_or_else(|| COUNTER.next().to_string());

    let window_id = pl_attrs.window_id.unwrap_or(0);
    let use_https = pl_attrs.use_https;
    let drag_drop_overlay = pl_attrs.drag_drop_overlay;
    let bridge_runtime = pl_attrs.bridge_runtime.ok_or_else(|| {
      Error::OpenHarmonyInitError(
        "BridgeRuntime not provided — call with_bridge_runtime() on the builder".into(),
      )
    })?;

    log::info!(
      "[WRY OHOS] build: use_https={}, drag_drop_overlay={}, custom_protocols={}",
      use_https,
      drag_drop_overlay,
      custom_protocols.len()
    );

    let client = WebviewClient::from_bridge(bridge_runtime);
    let runtime = BridgeExecutor::new();

    // State shared with callbacks
    let page_loaded = Arc::new(AtomicBool::new(false));
    let url_cache = Arc::new(Mutex::new(String::new()));
    // Gate F11: only the devtools-gated methods touch this flag - gate the
    // binding with them so a release build without the devtools feature has
    // no dead local either.
    #[cfg(any(debug_assertions, feature = "devtools"))]
    let devtools_open = AtomicBool::new(false);

    // 1. Register reverse callbacks (before create)
    let mut callbacks_builder = WebviewCallbacksBuilder::new(&id);

    // Navigation handler: wry semantics true=allow → bridge intercept=true means block
    if let Some(navigation_handler) = navigation_handler {
      let handler = Arc::new(SendSyncBox(navigation_handler));
      callbacks_builder = callbacks_builder.on_navigation_request(move |req| !(handler.0)(req.url));
    }

    // Title change handler
    if let Some(document_title_changed_handler) = document_title_changed_handler {
      let handler = Arc::new(SendSyncBox(document_title_changed_handler));
      callbacks_builder = callbacks_builder.on_title_change(move |event| {
        (handler.0)(event.title);
      });
    }

    // Download started handler (FnMut, needs Mutex)
    if let Some(download_started_handler) = download_started_handler {
      let handler = Arc::new(Mutex::new(SendSyncBox(download_started_handler)));
      callbacks_builder = callbacks_builder.on_download_start(move |req| {
        let mut path = req.temp_path.map(PathBuf::from).unwrap_or_default();
        let allow = {
          let mut guard = handler.lock().unwrap();
          (guard.0)(req.url, &mut path)
        };
        WebviewDownloadStartResponse {
          allow,
          temp_path: path.to_str().map(|s| s.to_string()),
        }
      });
    }

    // Download completed handler
    if let Some(download_completed_handler) = download_completed_handler {
      let handler = Arc::new(SendSyncBox(download_completed_handler));
      callbacks_builder = callbacks_builder.on_download_end(move |event| {
        (handler.0)(event.url, event.temp_path.map(PathBuf::from), event.success);
      });
    }

    // Page begin/end — always registered (for page_loaded + url_cache)
    let on_page_load = on_page_load_handler.map(|h| Arc::new(SendSyncBox(h)));

    let url_cache_begin = url_cache.clone();
    let page_loaded_begin = page_loaded.clone();
    let on_page_load_begin = on_page_load.clone();
    callbacks_builder = callbacks_builder.on_page_begin(move |event| {
      page_loaded_begin.store(false, Ordering::SeqCst);
      url_cache_begin.lock().unwrap().clone_from(&event.url);
      if let Some(handler) = &on_page_load_begin {
        (handler.0)(PageLoadEvent::Started, event.url);
      }
    });

    let url_cache_end = url_cache.clone();
    let page_loaded_end = page_loaded.clone();
    let on_page_load_end = on_page_load.clone();
    callbacks_builder = callbacks_builder.on_page_end(move |event| {
      page_loaded_end.store(true, Ordering::SeqCst);
      url_cache_end.lock().unwrap().clone_from(&event.url);
      if let Some(handler) = &on_page_load_end {
        (handler.0)(PageLoadEvent::Finished, event.url);
      }
    });

    // New window handler
    if let Some(new_window_req_handler) = new_window_req_handler {
      let handler = Arc::new(SendSyncBox(new_window_req_handler));
      callbacks_builder = callbacks_builder.on_new_window_request(move |req| {
        let features = crate::NewWindowFeatures {
          size: None,
          position: None,
          opener: crate::NewWindowOpener {},
        };
        match (handler.0)(req.target_url, features) {
          crate::NewWindowResponse::Allow => true,
          crate::NewWindowResponse::Deny => false,
          // Create: Tauri already built its own OS window (the sub-window
          // WebviewWindow, OHOSWindowKind::SubWindow) and will load the target
          // URL into it. Return false
          // so ArkWeb CANCELS its own popup — the bridge then runs the
          // non-blocking Deny path (setWebController(null)) instead of
          // spawning a duplicate dialog. Returning true here would tell ArkWeb
          // to ALSO open a popup, which is wrong (and the popup controller has
          // no synchronous Web host, risking a UI-thread block).
          crate::NewWindowResponse::Create { .. } => false,
        }
      });
    }

    // Drag-drop handler (4 events)
    if let Some(drag_drop_handler) = drag_drop_handler {
      let handler = Arc::new(SendSyncBox(drag_drop_handler));
      let h_enter = handler.clone();
      callbacks_builder = callbacks_builder.on_drag_enter(move |event| {
        let _ = (h_enter.0)(crate::DragDropEvent::Enter {
          paths: vec![],
          position: (event.x as i32, event.y as i32),
        });
      });
      let h_over = handler.clone();
      callbacks_builder = callbacks_builder.on_drag_over(move |event| {
        let _ = (h_over.0)(crate::DragDropEvent::Over {
          position: (event.x as i32, event.y as i32),
        });
      });
      let h_drop = handler.clone();
      callbacks_builder = callbacks_builder.on_drag_drop(move |event| {
        let paths: Vec<PathBuf> = event.paths.into_iter().map(PathBuf::from).collect();
        let _ = (h_drop.0)(crate::DragDropEvent::Drop {
          paths,
          position: (event.x as i32, event.y as i32),
        });
      });
      let h_leave = handler.clone();
      callbacks_builder = callbacks_builder.on_drag_leave(move |_event| {
        let _ = (h_leave.0)(crate::DragDropEvent::Leave);
      });
    }

    // 2. Convert custom protocols to shared Send+Sync form
    let shared_protocols: HashMap<String, SharedProtocolHandler> = custom_protocols
      .into_iter()
      .map(|(k, v)| (k, Arc::new(SendSyncBox(v))))
      .collect();
    let shared_for_intercept = shared_protocols.clone();

    // #199: pre-fill the URL cache with the (normalized) initial URL so the
    // first IPC invoke that arrives before navigation completes resolves
    // against the real page URL instead of the about:blank fallback. `url()`
    // shares this cache -- before navigation it now returns the initial URL
    // rather than an empty string (benign, more truthful).
    *url_cache.lock().unwrap() =
      url_cache_prefill(initial_url.as_deref(), use_https, &shared_for_intercept);

    // Register https intercept callback (if use_https and protocols exist)
    if use_https && !shared_for_intercept.is_empty() {
      let https_id = id.clone();
      let https_protocols = shared_for_intercept.clone();
      callbacks_builder = callbacks_builder.on_https_intercept_request(move |req| {
        // #186: forward the intercepted request's method + parallel header
        // arrays when the ArkTS plugin sent them (None on older plugins --
        // the builder then keeps the historical GET/no-headers shape).
        dispatch_https_intercept_sync(
          &req.url,
          &https_id,
          &https_protocols,
          req.method.as_deref(),
          req.header_names.as_deref(),
          req.header_values.as_deref(),
        )
      });
    }

    callbacks_builder
      .build()
      .map_err(|e| Error::OpenHarmonyInitError(e.to_string()))?;

    // 3. Register IPC handler via WebviewJavascriptProxyBuilder (before create)
    let id_for_ipc = id.clone();
    let url_cache_ipc = url_cache.clone();
    if let Some(ipc_handler) = ipc_handler {
      let handler = Arc::new(SendSyncBox(ipc_handler));
      WebviewJavascriptProxyBuilder::new(&id_for_ipc, "ipc")
        .add_method("postMessage", move |_wid, args| {
          let message = args.get(0).unwrap_or(&"".to_string()).to_owned();
          let url = url_cache_ipc.lock().unwrap().clone();
          let uri = if url.is_empty() {
            Uri::from_static("about:blank")
          } else {
            url
              .parse::<Uri>()
              .unwrap_or(Uri::from_static("about:blank"))
          };
          let request = Request::builder().uri(uri).body(message).unwrap();
          (handler.0)(request);
        })
        .build()
        .map_err(|e| {
          Error::OpenHarmonyWebviewError(format!("Failed to register IPC proxy: {}", e))
        })?;
    }

    // 4. Register custom protocols (before create)
    //
    // OHOS ArkWeb uses a two-phase custom-protocol model: each scheme must be
    // process-wide *declared* via `WebviewProtocol::register` before the Web
    // engine initializes, then *bound* per-controller via
    // `custom_protocol_async` (which enforces the declaration through
    // `require_declared`). The engine initializes lazily inside the bridge
    // `create` call below (`ensureWebEngineInitialized`), which is spawned in
    // step 6 — i.e. after this synchronous section — so declaring here
    // satisfies the ordering even though tauri only collects its scheme list
    // at runtime (during `Builder::run`). Re-declaring an already-declared
    // scheme is a no-op (`scheme_registration_needed`), so child/second
    // webviews are safe. Options match the openharmony-ability demo: custom
    // protocols must be fetchable, bypass CSP, allow CORS, and use code cache.
    let protocol_options = WebviewProtocolOptions::Standard
      | WebviewProtocolOptions::CorsEnabled
      | WebviewProtocolOptions::CspBypassing
      | WebviewProtocolOptions::FetchEnabled
      | WebviewProtocolOptions::CodeCacheEnabled;
    for protocol in shared_protocols.keys() {
      WebviewProtocol::register(protocol, protocol_options).map_err(|e| {
        Error::OpenHarmonyInitError(format!(
          "Failed to declare custom protocol '{}': {}",
          protocol, e
        ))
      })?;
    }

    for (protocol, callback) in &shared_protocols {
      let webview_id = id.clone();
      let protocol = protocol.clone();
      let callback = Arc::clone(callback);
      client
        .custom_protocol_async(
          webview_id.clone(),
          &protocol,
          move |_url, req, _is_main, responder| {
            let responder_box: Box<dyn FnOnce(Response<Cow<'static, [u8]>>)> =
              Box::new(move |resp| {
                responder.respond(resp);
              });
            (callback.0)(
              webview_id.as_str(),
              req,
              RequestAsyncResponder {
                responder: responder_box,
              },
            );
          },
        )
        .map_err(|e| {
          Error::OpenHarmonyInitError(format!("Failed to register custom protocol: {}", e))
        })?;
    }

    // 5. Build create request
    let initial_bounds = bounds.unwrap_or_default();

    let bg_color_str = background_color.map(rgba_to_argb_hex);

    // ArkWeb's `javaScriptOnDocumentStart` only injects a `ScriptItem` whose
    // `scriptRules` array matches the document origin. An EMPTY array matches
    // no document, so none of the tauri init scripts (including the one that
    // defines `window.__TAURI_INTERNALS__`) would run — the frontend bundle
    // then throws `Cannot read properties of undefined (reading 'metadata')`
    // and never mounts (only a post-load `webview.eval` probe shows).
    //
    // Build match rules covering both runtime configurations:
    //   * `"*"`  — matches http(s) origins, including the `https://tauri.localhost`
    //     rewrite used when `use_https` is enabled.
    //   * `"{scheme}://"` — matches custom-protocol origins (e.g. `tauri://`),
    //     which `"*"` does NOT match on ArkWeb: custom protocols require a
    //     scheme-prefixed rule ending in `://` (see the tauri repo's
    //     multi-window design doc under `tauri/doc/`, TODO-5). One rule
    //     per registered custom scheme.
    // The raw-scheme default (`tauri://localhost`) is the tauri default
    // (`useHttpsScheme` is false unless a consumer opts in), so the
    // scheme-prefixed rule is essential.
    let script_rules: Vec<String> = {
      let mut rules: Vec<String> = vec!["*".to_string()];
      for scheme in shared_protocols.keys() {
        rules.push(format!("{}://", scheme));
      }
      rules
    };

    // Concatenate all init scripts into a SINGLE `ScriptItem`.
    //
    // ArkWeb's `javaScriptOnDocumentStart` executes `ScriptItem[]` in
    // **dictionary (lexicographic) order, NOT array order** (ArkWeb docs:
    // "scripts run in dictionary order rather than array order; use
    // runJavaScriptOnDocumentStart if array order is required"). Tauri's init
    // scripts are an
    // ordered dependency chain (create `window.__TAURI_INTERNALS__` →
    // ipc-protocol → metadata → init/core.js). Registering them as separate
    // ScriptItems lets ArkWeb reorder them by script-content lexicographically:
    // the `metadata` script (`Object.defineProperty(window.__TAURI_INTERNALS__,
    // 'metadata', …)`) sorts BEFORE the script that creates
    // `window.__TAURI_INTERNALS__` (its body begins with a leading newline +
    // fewer spaces, so it compares greater), so it runs while
    // `__TAURI_INTERNALS__` is still `undefined` →
    // `Object.defineProperty called on non-object` → the metadata (and the
    // downstream `invoke`) never attaches → `__TAURI_INTERNALS__` stays
    // `{plugins:{}}` → the frontend bundle throws
    // "Cannot read properties of undefined (reading 'currentWindow')" and never
    // mounts (only a post-load `webview.eval` probe shows).
    //
    // A single concatenated ScriptItem runs all scripts in written order within
    // one execution context, so the dependency chain holds. Joining with `;\n`
    // prevents ASI/empty-statement hazards between script bodies. This mirrors
    // Android's `inject_scripts_into_html`, which collapses all init scripts
    // into one HTML document in order. (OHOS `ScriptItem` carries only `script`
    // + `scriptRules` — `for_main_frame_only` is already dropped on this path —
    // so a single blob loses no behavior OHOS currently honors.)
    let merged_scripts: Vec<WebviewInitializationScript> = if initialization_scripts.is_empty() {
      Vec::new()
    } else {
      let body = initialization_scripts
        .iter()
        .map(|s| s.script.as_str())
        .collect::<Vec<_>>()
        .join(";\n");
      vec![WebviewInitializationScript {
        script: body,
        script_rules,
      }]
    };

    let mut create_req = WebviewCreateRequest::new(&id)
      .style(WebviewStyle {
        background_color: bg_color_str,
        // #188: forward the requested visibility through the existing
        // `WebviewStyle.visible` wire field (zero NAPI change); the ArkTS
        // receiver treats `true`/unset identically.
        visible: Some(visible),
        // #188 (design D9): forward the incognito flag through the new
        // `WebviewStyle.incognito` wire field (Option<bool>,
        // skip-serialized): `true` maps to `Some(true)` -- the ArkTS receiver
        // sets `Web().incognitoMode(true)` (SDK20 @since 20) and carries the
        // flag to the cookie sync bridge as its third parameter; the default
        // `false` stays `None`, keeping the payload byte-identical to the
        // pre-#188 wire (zero change for existing apps).
        incognito: incognito.then_some(true),
        ..Default::default()
      })
      .initialization_scripts(merged_scripts)
      .transparent(transparent);

    // Set url or html
    if let Some(html) = html {
      create_req = create_req.html(html);
    } else if let Some(url) = initial_url {
      let url = if use_https && !shared_for_intercept.is_empty() {
        let rewritten = rewrite_https_url_if_matching(&url, &shared_for_intercept);
        log::info!(
          "[wry https-intercept] URL rewrite: {} → {} (use_https={}, protocols={:?})",
          url,
          rewritten,
          use_https,
          shared_for_intercept.keys().collect::<Vec<_>>()
        );
        rewritten
      } else {
        url
      };
      create_req = create_req.url(url);
      if let Some(headers) = initial_headers {
        create_req.headers = Some(headers_to_btree(&headers));
      }
    }

    // Field assignments (no builder methods for these)
    create_req.javascript_enabled = Some(!javascript_disabled);
    create_req.autoplay = Some(autoplay);
    create_req.clipboard = Some(clipboard);
    create_req.zoom_hotkeys = Some(zoom_hotkeys_enabled);
    create_req.drag_drop_overlay = Some(drag_drop_overlay);
    // Seed https_intercept_protocols at create time (same gate as the URL rewrite above:
    // use_https && !shared_for_intercept.is_empty()). This fixes the create-vs-register
    // race where the ArkTS httpsInterceptProtocols Set was empty at first loadUrl →
    // onInterceptRequest early-returned null → ArkWeb fetched https://tauri.localhost for
    // real → arkweb-error://webdata/ → isSecureContext=false. Late register_https_intercept
    // stays as a runtime add path; Set.add is idempotent so no conflict.
    if use_https && !shared_for_intercept.is_empty() {
      create_req.https_intercept_protocol_list =
        Some(shared_for_intercept.keys().cloned().collect::<Vec<_>>());
    }
    if window_id != 0 {
      create_req.window_id = Some(window_id);
    }
    if let Some(user_agent) = user_agent {
      create_req.user_agent = Some(user_agent);
    }

    // devtools flag at create time
    #[cfg(any(debug_assertions, feature = "devtools"))]
    {
      create_req.devtools = Some(devtools);
    }

    // For child webviews with bounds, set initial style position/size.
    if is_child && bounds.is_some() {
      // #198: physical -> ArkUI vp via the live display ratio (was a hardcoded
      // 1.0 -- a vp!=1 device now lands geometry in vp units; the
      // absent-binding fallback 1.0 -- host builds / UTs -- is an unchanged
      // identity, while the desktop reference device reports vp=1.9).
      let vp = virtual_pixel_ratio();
      let (x, y) = geometry_to_logical_vp(initial_bounds.position, vp);
      let (w, h) = size_to_logical_vp(initial_bounds.size, vp);
      create_req.style.x = Some(Either::A(x));
      create_req.style.y = Some(Either::A(y));
      create_req.style.width = Some(Either::A(w));
      create_req.style.height = Some(Either::A(h));
    }

    // 6. Spawn create on BridgeExecutor (delayed attach)
    let handle_slot: Arc<OnceLock<WebviewHandle>> = Arc::new(OnceLock::new());
    let pending_ops: Arc<Mutex<Vec<PendingOp>>> = Arc::new(Mutex::new(Vec::new()));
    let creation_error: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));

    let client_for_create = client.clone();
    let handle_slot_for_create = handle_slot.clone();
    let pending_ops_for_create = pending_ops.clone();
    let creation_error_for_create = creation_error.clone();
    let runtime_for_create = runtime.clone();
    let id_for_rollback = id.clone();

    runtime.spawn(async move {
      let result = client_for_create.create(create_req).await;
      match result {
        Ok(handle) => {
          // TOCTOU guard: hold pending_ops lock while setting handle + draining
          let pending = {
            let mut guard = pending_ops_for_create.lock().unwrap();
            if handle_slot_for_create.set(handle).is_err() {
              // Already set (shouldn't happen) — discard
              return;
            }
            let handle_ref = handle_slot_for_create.get().unwrap().clone();
            let pending: Vec<PendingOp> = guard.drain(..).collect();
            (handle_ref, pending)
          };
          // Spawn replay outside the lock
          let (handle_ref, pending) = pending;
          // Gate F2 (drain leg, PR#26 review round 2): this drain is the
          // consumption point of the pre-handshake queue
          // (`queue_pre_handshake_open`) - once drained, a queued open's
          // only execution path is the replay task below, polled by the
          // same bridge pump thread. If that thread is dead at drain time
          // the replay is never polled and a drained `SetDevtools` would
          // latch the process-level open intent forever: release it through
          // the shared failure handler. (The create future itself is polled
          // by the pump thread, so the thread is alive while this branch
          // runs; the check pins the drain-point invariant and covers an
          // execution-model change. A thread dying right after this check
          // is the disclosed TOCTOU residual gap - the release below could
          // no longer run either.)
          //
          // Wider disclosed window (PR#26 review round 3): a pump thread
          // dying BEFORE this create future is ever polled runs neither arm
          // of this match - no drain, no `failed_create_cleanup`, no
          // rollback - so a queued `SetDevtools` keeps the process-level
          // open intent latched forever and queued ops (plus this attempt's
          // registry entries) are never cleaned up. That window is strictly
          // wider than the drain-point TOCTOU above and stays disclosed
          // rather than guarded: it requires the pump to die between the
          // enqueue and the first poll of this future.
          #[cfg(any(debug_assertions, feature = "devtools"))]
          if !runtime_for_create.pump_thread_alive()
            && pending
              .iter()
              .any(|op| matches!(op, PendingOp::SetDevtools))
          {
            devtools_open_failed(
              "create drain replay",
              &crate::Error::OpenHarmonyWebviewError(
                "bridge runtime pump thread is dead; the queued open will never be replayed".into(),
              ),
            );
          }
          runtime_for_create.spawn(async move {
            for op in pending {
              op.execute(&handle_ref).await;
            }
          });
        }
        Err(e) => {
          // Surface the failure to callers: ops dispatched after a failed
          // create would otherwise queue forever with no replay trigger.
          // Hold the pending_ops lock (same TOCTOU guard as the Ok branch)
          // so `dispatch_or_queue` never races between the two states.
          let error_str = e.to_string();
          log::error!("[wry] WebviewClient::create() failed: {}", error_str);
          let mut guard = pending_ops_for_create.lock().unwrap();
          *creation_error_for_create.lock().unwrap() = Some(error_str);
          // m5: a queued `SetDevtools` can never replay after a failed create --
          // release the process-level open intent so a later webview's
          // `open_devtools` dispatches again instead of silently no-oping
          // (see `failed_create_cleanup`).
          failed_create_cleanup(&mut guard);
          // Roll back this attempt's entries from the process-global
          // registries (callbacks / ipc proxy / per-webview protocol
          // handlers). They were registered before the create was spawned
          // and nothing will ever consume them now — without this they leak
          // on every failed create. Process-wide scheme declarations are
          // intentionally kept (shared across webviews, idempotent).
          drop(guard);
          if let Err(rollback_err) = client_for_create.rollback_registrations(&id_for_rollback) {
            log::warn!(
              "[wry] rollback of registry entries for failed create '{}' failed: {}",
              id_for_rollback,
              rollback_err
            );
          }
        }
      }
    });

    // 7. Register https intercept protocols (async, fire-and-forget)
    if use_https && !shared_for_intercept.is_empty() {
      let protocol_names: Vec<String> = shared_for_intercept.keys().cloned().collect();
      let client_for_intercept = client.clone();
      let id_for_intercept = id.clone();
      runtime.spawn(async move {
        if let Err(e) = client_for_intercept
          .register_https_intercept(id_for_intercept, protocol_names)
          .await
        {
          log::warn!("[wry] register_https_intercept failed: {}", e);
        }
      });
    }

    // Gate F4 (PR#26 review round 2): the create-time seed routes through
    // the same sentinel screening as the set_bounds cache write
    // (`merge_bounds_into_cache`), so a `with_bounds` call carrying sentinel
    // components never seeds the cache with them verbatim. The common paths
    // are unaffected: the builder default (logical origin + 200x200) has no
    // sentinel component, so the merge is a wholesale replace of the
    // `Rect::default()` start value, and a bounds-less webview seeds from
    // the builder default (logical origin + 200x200). The create-request
    // style write above does run `initial_bounds` through
    // `geometry_to_logical_vp` / `size_to_logical_vp` first (like the
    // set_bounds path), so the wire carries the vp-converted request; what
    // it does not apply is the sentinel merge screening above - the ArkTS
    // render layer does its own sentinel skipping.
    //
    // Execution model (PR#26 review round 3): this seed merge runs
    // synchronously in the builder body, NOT as part of the spawned create
    // future, so it has no pump-liveness precondition at all - unlike the
    // create drain, whose liveness check pins an invariant of pump-polled
    // execution and merely covers an execution-model change. Carve-out: this
    // seed write is the disclosed exception - it is what leaves the
    // requested-but-never-applied creation row's cache holding a rect the
    // render layer never applied (a MAIN webview with explicit `with_bounds`
    // is seeded with the explicit rect while the create-geometry style write
    // is gated on `is_child`), matching the creation matrix documented on
    // `WebView::bounds`; the Gate F3 promise that `bounds()` never reports
    // unapplied set_bounds geometry covers the set_bounds path only.
    let mut bounds_cache_seed = Rect::default();
    merge_bounds_into_cache(&mut bounds_cache_seed, initial_bounds);

    Ok(Self {
      id,
      handle: handle_slot,
      pending_ops,
      creation_error,
      client,
      runtime,
      page_loaded,
      url_cache,
      bounds_cache: Mutex::new(bounds_cache_seed),
      #[cfg(any(debug_assertions, feature = "devtools"))]
      devtools_open,
      incognito,
      disposed: AtomicBool::new(false),
    })
  }

  // ─── Helper: dispatch or queue ──────────────────────────────────────────────

  /// Execute a PendingOp immediately if the handle is ready, otherwise queue it.
  /// **TOCTOU guard**: must hold `pending_ops` lock when checking `handle.get()`.
  /// Returns an error if webview creation already failed — the op is dropped
  /// rather than queued forever.
  fn dispatch_or_queue(&self, op: PendingOp) -> Result<()> {
    dispatch_or_queue_op(
      &self.pending_ops,
      &self.handle,
      &self.creation_error,
      &self.runtime,
      op,
    )
  }

  /// Get the handle if ready, or None if create is still pending.
  fn try_handle(&self) -> Option<WebviewHandle> {
    self.handle.get().cloned()
  }

  // ─── Public API methods ─────────────────────────────────────────────────────

  pub fn print(&self) -> Result<()> {
    if !self.page_loaded.load(Ordering::SeqCst) {
      return Err(Error::OpenHarmonyWebviewError(
        "Page not fully loaded. Call print after onPageEnd.".into(),
      ));
    }
    let temp_path = std::env::temp_dir().join(format!(
      "wry_print_{}.pdf",
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis())
        .unwrap_or(0)
    ));
    let path_str = temp_path.to_string_lossy().to_string();
    self.dispatch_or_queue(PendingOp::Print(path_str))?;
    Ok(())
  }

  pub fn id(&self) -> crate::WebViewId<'_> {
    &self.id
  }

  // Pattern C: cached, with a main-thread synchronous refresh (#192).
  pub fn url(&self) -> Result<String> {
    url_with_main_thread_refresh(
      openharmony_ability::main_thread_status(),
      &self.id,
      &self.url_cache,
    )
  }

  // Pattern B: callback — spawn + async trigger callback
  pub fn eval(&self, js: &str, callback: Option<impl Fn(String) + Send + 'static>) -> Result<()> {
    let js = js.to_string();
    let cb = callback.map(|c| Box::new(c) as Box<dyn Fn(String) + Send + 'static>);
    self.dispatch_or_queue(PendingOp::Eval(js, cb))?;
    Ok(())
  }

  // Devtools: bridge action
  //
  // #195: previously a pre-handshake open was silently dropped (`try_handle`
  // -> None) -- the embedding app's setup hook (e.g. the demo suite's
  // `#[cfg(debug_assertions)] webview.open_devtools()`, routed through
  // tauri-runtime-wry's dispatcher and its OpenDevTools message arm) calls
  // open_devtools right after creation, so on the OHOS delayed-attach path
  // the intent vanished. Now the intent is recorded in the process-level flag
  // first, and a pre-handshake open is queued as `PendingOp::SetDevtools` for
  // the create drain to replay.
  //
  // W26-4: no *failure path* latches the idempotence gate for the rest of
  // the process - every failure path releases the process-level intent: a
  // dead queue (`queue_pre_handshake_open`), a failed create
  // (`failed_create_cleanup`), a failed replay (`PendingOp::SetDevtools`)
  // and a failed ready-branch dispatch (`devtools_open_failed`). The
  // disclosed pre-poll death window (see the pump-thread-dies-before-poll
  // disclosure above, PR#26 round 3) is one of the latch-forever timelines
  // - alongside the ready-branch TOCTOU and drain-point TOCTOU residual
  // gaps disclosed at their corresponding notes - and it is not a
  // failure path: a pump thread dying between the enqueue
  // and the first poll of the create future runs neither match arm, no
  // failure event fires there, so all six release points are skipped and a
  // queued `SetDevtools` keeps the intent latched. The per-webview
  // `devtools_open` flag is NOT rolled back on an async enable failure: it
  // records the requested intent (what `is_devtools_open` reports), and a
  // later `close_devtools` clears it.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  pub fn open_devtools(&self) {
    let needs_dispatch = devtools_open_intent();
    self.devtools_open.store(true, Ordering::SeqCst);
    if !needs_dispatch {
      // Idempotent: an open is already queued or applied (process-level API).
      return;
    }
    match self.try_handle() {
      Some(handle) => {
        self.runtime.spawn(async move {
          if let Err(e) = handle.set_web_debugging_access(true).await {
            // W26-4: a failed enable must not latch the idempotence gate --
            // release the intent so a later open dispatches again.
            devtools_open_failed("open_devtools", &e);
          }
        });
        // Gate F5: synchronous failure leg. `BridgeExecutor::spawn` cannot
        // report an enqueue failure (tokio 1.x `Handle::spawn` never fails
        // the enqueue), but the bridge runtime's pump thread is the only
        // poller: when it has already terminated, the enable future above is
        // never polled (neither succeeding nor reaching the async
        // `devtools_open_failed`), so release the intent here. Residual gap
        // (disclosed known limitation): a thread that dies right after this
        // check latches the intent for the rest of the process - a later
        // `open_devtools` early-returns on the fence and never re-enters the
        // dispatch path (the swap latch clears only via `close_devtools` or
        // a failure release), matching the documented DEVTOOLS_ENABLED
        // limitation above. This ready-branch residual gap is not the only
        // latch-forever timeline: the disclosed pre-poll death window on the
        // new-window create path (a pump thread dying between the enqueue
        // and the first poll of the create future runs neither match arm, so
        // all six release points (W26-4's four failure paths plus the two
        // dead-pump legs this change adds - the ready-branch leg below and
        // the create-future drain leg) are skipped - see
        // the pump-thread-dies-before-poll disclosure above (PR#26 round 3).
        if !self.runtime.pump_thread_alive() {
          devtools_open_failed(
            "open_devtools",
            &crate::Error::OpenHarmonyWebviewError(
              "bridge runtime pump thread is dead; the enable will never be polled".into(),
            ),
          );
        }
      }
      // Create still pending: queue for replay once the handshake completes.
      None => queue_pre_handshake_open(
        &self.pending_ops,
        &self.handle,
        &self.creation_error,
        &self.runtime,
      ),
    }
  }

  // #195: close clears the process-level intent (so a later open can dispatch
  // again) and uses the runtime channel when ready. Edge note: a close issued
  // while an open is still queued cannot retro-cancel that queued op (design
  // D5 keeps a single variant) -- the replayed open wins; close again after the
  // handshake to actually turn it off.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  pub fn close_devtools(&self) {
    let _ = devtools_close_intent();
    if let Some(handle) = self.try_handle() {
      self.runtime.spawn(async move {
        if let Err(e) = handle.set_web_debugging_access(false).await {
          log::warn!("[wry] close_devtools failed: {}", e);
        }
      });
    }
    self.devtools_open.store(false, Ordering::SeqCst);
  }

  #[cfg(any(debug_assertions, feature = "devtools"))]
  pub fn is_devtools_open(&self) -> bool {
    self.devtools_open.load(Ordering::SeqCst)
  }

  // Pattern A: fire-and-forget
  pub fn zoom(&self, scale_factor: f64) -> Result<()> {
    self.dispatch_or_queue(PendingOp::Zoom(scale_factor))?;
    Ok(())
  }

  pub fn set_background_color(&self, background_color: RGBA) -> Result<()> {
    let color_str = rgba_to_argb_hex(background_color);
    self.dispatch_or_queue(PendingOp::SetBackgroundColor(color_str))?;
    Ok(())
  }

  // Pattern D: blocking-from-worker (worker threads) / sync bridge (main
  // thread) — cookies
  pub fn cookies(&self) -> Result<Vec<Cookie<'static>>> {
    let url = self.url_cache.lock().unwrap().clone();
    if url.is_empty() {
      return Ok(vec![]);
    }
    self.cookies_for_url(&url)
  }

  pub fn set_cookie(&self, cookie: &Cookie<'_>) -> Result<()> {
    let domain = cookie.domain();
    let url = match domain {
      Some(d) if !d.is_empty() => format!("https://{}", d.trim_start_matches('.')),
      _ => {
        let current_url = self.url_cache.lock().unwrap().clone();
        if !current_url.is_empty() {
          current_url
        } else {
          log::warn!(
            "[wry] set_cookie: cannot determine target URL (no domain and no current URL)"
          );
          return Ok(());
        }
      }
    };
    let value = format_set_cookie_value(cookie);
    self.dispatch_or_queue(PendingOp::SetCookie(url, value))?;
    Ok(())
  }

  pub fn delete_cookie(&self, _cookie: &Cookie<'_>) -> Result<()> {
    log::warn!("[wry] delete_cookie is a no-op on OHOS: platform lacks single-cookie deletion");
    Ok(())
  }

  pub fn cookies_for_url(&self, url: &str) -> Result<Vec<Cookie<'static>>> {
    // Thread classification uses the authoritative render-entry signal from
    // openharmony-ability (the XComponent render entry records the NAPI main
    // thread), NOT the id of the thread that built the first webview — a
    // direct-wry embedder can build the first webview on a worker, which the
    // old first-construction heuristic would then misrecord as main forever
    // (issue #145).
    match openharmony_ability::main_thread_status() {
      MainThreadStatus::Main => {
        // Main thread: the async bridge is unusable here — its TSFN response
        // needs this very thread to pump, so blocking on it would deadlock.
        // Fetch synchronously through the dedicated `ohos.webview-cookie`
        // MainThreadSync plugin (ArkTS `fetchCookieSync`) instead. Returns
        // the real cookies rather than the old silent empty (issue #110).
        // #188: the incognito flag rides along -- the sync request is
        // id-less, so without it the ArkTS side could only ever read the
        // default store and an incognito webview's main-thread probe would
        // silently observe non-incognito cookies.
        let cookie_str =
          openharmony_ability_plugin_webview::cookies_for_url_on_main_thread(
            url,
            self.incognito,
          )
          .map_err(|e| {
            Error::OpenHarmonyWebviewError(format!(
              "cookies_for_url (main-thread sync bridge): {e}"
            ))
          })?;
        Ok(parse_cookie_string(&cookie_str))
      }
      MainThreadStatus::Worker => {
        let handle = match self.try_handle() {
          Some(h) => h,
          None => return Ok(vec![]),
        };
        let url = url.to_string();
        let (tx, rx) = mpsc::channel::<String>();
        self.runtime.spawn(async move {
          let result = handle.cookies_with_url(url).await;
          let _ = tx.send(result.unwrap_or_default());
        });
        let cookie_str = rx
          // Safe to block here: the Worker classification above guarantees we
          // are on a worker thread, so the TSFN callback (which runs on the
          // main thread) can complete while we wait. This is the
          // "blocking-from-worker" pattern; the forbidden variant is blocking
          // the MAIN thread.
          .recv_timeout(std::time::Duration::from_secs(3))
          .map_err(|_| Error::OpenHarmonyWebviewError("cookies_for_url timed out".into()))?;
        Ok(parse_cookie_string(&cookie_str))
      }
      // The render entry has not run yet, so we cannot prove which thread we
      // are on. The async branch's blocking wait is only safe once the real
      // main thread is known to pump the TSFN response; instead of gambling
      // on a 3s freeze (the failure mode the old heuristic could hit on
      // issue #145), fail fast with an explicit error. Once `render()` runs
      // this state disappears for the rest of the process lifetime.
      MainThreadStatus::Uninitialized => Err(Error::OpenHarmonyWebviewError(
        "cookies_for_url: main-thread env not initialized (XComponent render entry not yet run); cannot classify caller thread"
          .into(),
      )),
    }
  }

  // Pattern A: fire-and-forget
  pub fn reload(&self) -> Result<()> {
    self.dispatch_or_queue(PendingOp::Reload)?;
    Ok(())
  }

  pub fn load_url(&self, url: &str) -> Result<()> {
    self.dispatch_or_queue(PendingOp::LoadUrl(url.to_string()))?;
    Ok(())
  }

  pub fn load_url_with_headers(&self, url: &str, headers: http::HeaderMap) -> Result<()> {
    let header_map = headers_to_btree(&headers);
    self.dispatch_or_queue(PendingOp::LoadUrlWithHeaders(url.to_string(), header_map))?;
    Ok(())
  }

  pub fn load_html(&self, html: &str) -> Result<()> {
    self.dispatch_or_queue(PendingOp::LoadHtml(html.to_string()))?;
    Ok(())
  }

  pub fn clear_all_browsing_data(&self) -> Result<()> {
    self.dispatch_or_queue(PendingOp::ClearAllBrowsingData)?;
    Ok(())
  }

  // Pattern B: callback
  pub fn create_pdf(
    &self,
    path: &str,
    config: Option<PdfConfig>,
    callback: Box<dyn Fn(bool) + Send + 'static>,
  ) -> Result<()> {
    if !self.page_loaded.load(Ordering::SeqCst) {
      callback(false);
      return Err(Error::OpenHarmonyWebviewError(
        "Page not fully loaded. Call createPdf after onPageEnd.".into(),
      ));
    }
    // Forward the caller-supplied layout to the bridge; when `None` the ArkTS
    // side applies its fixed A4 defaults.
    let pdf_config = config.map(|c| WebviewPdfConfig {
      width: c.width,
      height: c.height,
      margin_top: c.margin_top,
      margin_bottom: c.margin_bottom,
      margin_left: c.margin_left,
      margin_right: c.margin_right,
      scale: c.scale,
      should_print_background: c.should_print_background,
    });
    self.dispatch_or_queue(PendingOp::CreatePdf(
      path.to_string(),
      pdf_config,
      Some(callback),
    ))?;
    Ok(())
  }

  // Pattern C: cached
  /// Returns the webview bounds (logical units, as passed to the builder or
  /// [`Self::set_bounds`]).
  ///
  /// # OHOS unit contract
  ///
  /// [`Self::set_bounds`] converts window physical coordinates into ArkUI vp
  /// units through the live display virtual-pixel ratio
  /// ([`virtual_pixel_ratio`], #198 -- previously a hardcoded 1.0). The live
  /// ratio is device-real: the OHOS desktop reference device reports
  /// vp = 1.9, so physical px is divided by vp before it reaches ArkUI (the
  /// historical full-stack "physical px == vp" assumption held only where
  /// the binding is absent and the fallback 1.0 applies -- host builds and
  /// unit tests, where the conversion is an identity and UT numbers stay
  /// bit-identical). Logical-coordinate input passes through
  /// `dpi::Position::to_logical` unchanged regardless of vp.
  ///
  /// # Cache semantics (not a live geometry readback)
  ///
  /// The value is cache-only: written at creation (builder bounds) and on
  /// every `set_bounds` (except the dead-pump branch of `set_bounds`, which
  /// warns and leaves the cache unchanged). `wry` itself never refreshes it
  /// on window resizes -- freshness depends entirely on the embedding
  /// runtime re-issuing `set_bounds`, which tauri-runtime-wry does on window
  /// resize only through its autoresize flow (that re-issued call writes
  /// this cache).
  /// Without that flow the cache goes stale as the window resizes.
  ///
  /// ArkUI-initiated layout changes DO occur and are NOT observed (no bridge
  /// writeback exists): a natural-layout webview follows container layout --
  /// window resizes move and resize its ArkTS node with no `set_bounds`
  /// call -- so the cache can go stale without any write from the runtime.
  /// The value is therefore the last written bounds, never the live
  /// geometry.
  ///
  /// For a natural-layout (bounds-less) webview the cache holds the
  /// `WebViewAttributes::default()` placeholder - logical position (0, 0),
  /// size 200x200 - NOT the actual on-screen geometry, which follows the
  /// container. (The `None` arm of the `unwrap_or_default` that seeds this
  /// cache is unreachable through the public builder API: the attributes
  /// default starts at `Some(200x200)` and `with_bounds` only ever writes
  /// `Some`.) Path note: that placeholder is "not real geometry" only for a
  /// MAIN webview - a child webview created with the same default gets the
  /// placeholder written as EXPLICIT create geometry (`is_child &&
  /// bounds.is_some()`), so `bounds()` reads back the requested 200x200 until
  /// a later write replaces it. Conversely, a MAIN webview created WITH an
  /// explicit `with_bounds` writes no create geometry at all (the style write
  /// is gated on `is_child && bounds.is_some()`) while the cache still holds
  /// the explicit rectangle - the "requested-but-never-applied" case. Callers
  /// must not use this value to
  /// reconstruct or fill in unknown geometry components: tauri-runtime-wry's
  /// i32::MIN sentinels (partial `set_bounds` updates, issue
  /// Eulogizethesun/tauri#241) never enter the cache - a sentinel component
  /// keeps its cached value while the set components of the same request
  /// update theirs ([`merge_bounds_into_cache`]) - so a cached
  /// component reflects only the last real write through the builder or
  /// `set_bounds`.
  ///
  /// # Render semantics (openspec ohos-webview-sizing)
  ///
  /// The ArkTS render layer consumes the full geometry: a child create
  /// request with explicit bounds renders the webview at the requested size
  /// (not inflated to the container; the style write is child-only: a MAIN
  /// create never carries bounds, even with `with_bounds`), and a runtime
  /// `set_bounds` carrying explicit width/height (a full request, or a
  /// SetSize-shaped partial) applies position AND size -- flipping a
  /// natural-layout (bounds-less) webview away from container following; a
  /// SetPosition-shaped first request (size pair = `i32::MIN` sentinel,
  /// skipped by this render layer) leaves natural layout in place. A
  /// bounds-less webview keeps natural layout: the wrapper renders
  /// at "100%" and follows window resizes through container layout.
  pub fn bounds(&self) -> Result<Rect> {
    Ok(*self.bounds_cache.lock().unwrap())
  }

  pub fn set_bounds(&self, bounds: Rect) -> Result<()> {
    set_bounds_with_cache(
      &self.pending_ops,
      &self.handle,
      &self.creation_error,
      &self.runtime,
      &self.bounds_cache,
      bounds,
    )
  }

  pub fn set_visible(&self, visible: bool) -> Result<()> {
    self.dispatch_or_queue(PendingOp::SetVisible(visible))?;
    Ok(())
  }

  pub fn focus(&self) -> Result<()> {
    self.dispatch_or_queue(PendingOp::Focus)?;
    Ok(())
  }

  pub fn focus_parent(&self) -> Result<()> {
    // OHOS has no separate parent window for the webview
    self.dispatch_or_queue(PendingOp::Focus)?;
    Ok(())
  }

  /// Removes this webview's ArkTS `Web` component. Unified for main AND child
  /// webviews (committer #189): the previous `self.is_child &&` gate skipped
  /// disposal for main webviews, leaking the ArkTS Web component on Drop --
  /// the "leftover fullscreen transparent window eats clicks" family. The
  /// first caller wins via the `disposed` swap (idempotent); `Drop` funnels
  /// through here too, so the dispatch result is deliberately ignored (on the
  /// Drop path a creation failure is already logged and there is nothing to
  /// propagate to).
  ///
  /// Dangling-dispatch boundary: while create is still pending the
  /// `Remove` op is queued and replayed once the handshake completes. The two
  /// arms are bounded differently: on the replay arm the queued op is
  /// dispatched as a bridge request, so it is bounded by the bridge's own 15s
  /// request timeout (`ability::crates/ability/src/bridge/mod.rs`
  /// `DEFAULT_TIMEOUT_MS = 15_000`); on the never-attached arm the op is
  /// never dispatched at all - no bridge request is issued and nothing waits
  /// on one - so there is no pending call to time out and no hang to bound.
  /// No unbounded hang on either side.
  pub fn dispose_child(&self) {
    if dispose_once(&self.disposed) {
      let _ = self.dispatch_or_queue(PendingOp::Remove);
    }
  }

  /// Returns the `WebviewHandle` for public API consumption.
  /// If create hasn't completed yet, returns a facade wrapping the client + id
  /// (method calls will be dispatched once the controller is ready).
  pub fn handle(&self) -> WebviewHandle {
    self
      .handle
      .get()
      .cloned()
      .unwrap_or_else(|| self.client.handle(&self.id))
  }
}

impl Drop for InnerWebView {
  fn drop(&mut self) {
    self.dispose_child();
  }
}

// ─── ArkWeb engine version ──────────────────────────────────────────────────────

/// Returns the active ArkWeb engine version, e.g. `"M132"` / `"M132 (evergreen)"`.
///
/// Delegates to `openharmony-ability-plugin-webview::arkweb_engine_version`,
/// which reads `OH_NativeArkWeb_GetActiveWebEngineVersion` from `libohweb.so`
/// (see that function's docs for the CAPI/dlopen rationale).
///
/// This is deliberately NOT a bridge round-trip: it must stay callable during
/// app bootstrap — synchronously inside the NAPI `openharmony()` entry on the
/// ArkTS main thread — where a bridge call (whose ArkTS handler needs that
/// same thread) would deadlock. The C API reads the same engine state with no
/// thread requirements.
///
/// Callers: wry's own `webview_version()` wrapper (behind the default
/// `os-webview` feature, which tauri-runtime-wry's wry dependency enables)
/// compiles on OHOS and forwards here. Beyond that wrapper this is public
/// API surface for direct wry users on OHOS.
///
/// Consumer contract: an `Err` from this function (or from
/// `webview_version()` on OHOS) does NOT mean "no WebView runtime
/// installed" — ArkWeb is an always-present system component on OpenHarmony,
/// and on systems below API 20 the `Err` only signals that this system does
/// not export the version CAPI (`OH_NativeArkWeb_GetActiveWebEngineVersion`).
/// Consumers gating on `webview_version().is_ok()` must not treat that `Err`
/// as a missing runtime — doing so fail-closes webview creation on devices
/// that are guaranteed to ship ArkWeb.
///
/// Format note: unlike the sibling platforms' dotted-numeric strings
/// (webview2 `"120.0.2210.61"`-style), this returns a kernel-generation
/// label (`"M114"`/`"M132"`/`"M144"`/`"ARKWEB_EVERGREEN"`/`"SYSTEM_DEFAULT"`
/// /`"ArkWebEngineVersion(N)"`, plus an optional `" (evergreen)"` suffix).
/// Downstream code must not parse it as semver.
pub fn platform_webview_version() -> Result<String> {
  openharmony_ability_plugin_webview::arkweb_engine_version()
    .map_err(|e| Error::OpenHarmonyWebviewError(e.to_string()))
}

// ─── https intercept ─────────────────────────────────────────────────────────────

/// Synchronously dispatches an https intercept request to the matching custom protocol handler.
///
/// The URL has the form `https://<protocol>.<host>/<path>` (the tauri default
/// host is `.localhost`, but the matcher is host-agnostic — any host matches,
/// mirroring upstream Windows/Android semantics). This function matches the
/// URL against the registered protocols using
/// [`custom_protocol_workaround::is_work_around_uri`], reverts it to
/// `<protocol>://<host>/<path>` with
/// [`custom_protocol_workaround::revert_uri_work_around`], builds a `Request`,
/// and calls the handler with a `RequestAsyncResponder`.
///
/// **Threading model**: This runs on the NAPI main thread via `invokeNativeSync`. The handler
/// is expected to call the responder **synchronously** (inline) — the default tauri asset handler
/// (`tauri::protocol::tauri::get`) does exactly this: it calls `get_response()` then
/// `responder.respond()` before returning.
///
/// We use an `Arc<Mutex<Option<Response>>>` instead of `mpsc::channel + rx.recv_timeout()`.
/// The previous `rx.recv_timeout(3s)` blocked the NAPI main thread, violating the design doc
/// (`p2-bridge-https-intercept/design.md:369`, which forbids "run_on_main_thread +
/// rx.recv() blocking patterns") and risking deadlock if any handler dispatched its responder
/// via `run_on_main_thread`.
///
/// If the handler does NOT call the responder synchronously (returns before responding),
/// we return `passthrough()` immediately — no blocking. This is a safe degradation: the
/// ArkWeb default network stack handles the request (which will fail for `tauri.localhost`
/// since it's not a real domain, but this only happens for async handlers, which the default
/// tauri handler is not). A warning is logged so the issue is visible.
///
/// #186: the intercepted request's method and headers are carried through from
/// the ArkTS interceptor (`WebResourceRequest.getRequestMethod()`/`getRequestHeader()`,
/// parallel same-order name/value arrays on the NAPI wire). `None` -- the shape
/// older bridge plugins send -- keeps the previous request shape (method=GET,
/// no headers), so old ArkTS plugins stay compatible. A malformed method falls
/// back to GET; a single malformed header (name/value not a legal HTTP token)
/// is skipped with a debug log rather than failing the whole request. The
/// request body is NOT forwarded: the OHOS platform exposes no accessor for
/// it (disclosed in ohos-platform-limitations). W26-5: the body-framing
/// headers `content-length` and `transfer-encoding` are dropped from the
/// forwarded set (case-insensitively) -- the rebuilt request's body is always
/// empty, so forwarding a stale framing header would make a downstream
/// consumer wait for body bytes (or a chunked terminator) that never arrive.
fn dispatch_https_intercept_sync(
  url: &str,
  webview_id: &str,
  protocols: &HashMap<String, SharedProtocolHandler>,
  method: Option<&str>,
  header_names: Option<&[String]>,
  header_values: Option<&[String]>,
) -> WebviewHttpsInterceptResponse {
  log::debug!(
    "[wry https-intercept] enter: url={} webview_id={}",
    url,
    webview_id
  );

  // Match a registered protocol with the upstream workaround matcher
  // (`{scheme}://{protocol}.` prefix — host-agnostic). Only registered
  // protocols can match, so URLs like `https://<unknown>.localhost/…` fall
  // through to passthrough. This closes the gap the old `.localhost`-only
  // extractor had: a rewritten `https://asset.mydomain/x` now dispatches to
  // the `asset` handler instead of silently dropping the request.
  let (protocol, callback, original_url) = match protocols
    .iter()
    .find(|(protocol, _)| custom_protocol_workaround::is_work_around_uri(url, "https", protocol))
  {
    Some((protocol, callback)) => (
      protocol.clone(),
      Arc::clone(callback),
      custom_protocol_workaround::revert_uri_work_around(url, "https", protocol),
    ),
    None => {
      // No registered protocol matches — ordinary external https traffic.
      // The normal case, so debug rather than warn.
      log::debug!(
        "[wry https-intercept] passthrough: no registered protocol matches url={}",
        url
      );
      return WebviewHttpsInterceptResponse::passthrough();
    }
  };
  log::debug!(
    "[wry https-intercept] matched protocol='{}': {} → {}",
    protocol,
    url,
    original_url
  );

  // #186: rebuild the intercepted request's method + headers when the ArkTS
  // interceptor supplied them. Defaults preserve the old wire shape.
  let parsed_method = method.and_then(|m| match http::Method::from_bytes(m.as_bytes()) {
    Ok(m) => Some(m),
    Err(_) => {
      log::debug!("[wry https-intercept] invalid method '{m}', falling back to GET");
      None
    }
  });
  let mut builder = Request::builder().uri(&original_url);
  if let Some(m) = &parsed_method {
    builder = builder.method(m.clone());
  }
  if let (Some(names), Some(values)) = (header_names, header_values) {
    for (name, value) in names.iter().zip(values.iter()) {
      let parsed_name = http::HeaderName::from_bytes(name.as_bytes());
      let value_ok = http::HeaderValue::from_str(value).is_ok();
      if parsed_name.is_err() || !value_ok {
        // One bad header must not sink the request -- skip it.
        log::debug!("[wry https-intercept] skipping invalid header '{name}': '{value}'");
        continue;
      }
      // W26-5: the body is never forwarded (always empty), so body-framing
      // headers must not be forwarded either -- a stale `content-length` /
      // `transfer-encoding` would make a downstream consumer wait for body
      // bytes that never arrive. Dropped case-insensitively via the parsed
      // (lowercased) name.
      let header_name = parsed_name.unwrap();
      if header_name == http::header::CONTENT_LENGTH
        || header_name == http::header::TRANSFER_ENCODING
      {
        log::debug!(
          "[wry https-intercept] dropping body-framing header '{name}' (body is not forwarded)"
        );
        continue;
      }
      builder = builder.header(header_name, value);
    }
  }
  let request = match builder.body(Vec::new()) {
    Ok(r) => r,
    Err(e) => {
      log::warn!(
        "[wry https-intercept] passthrough: failed to build request for {}: {}",
        original_url,
        e
      );
      return WebviewHttpsInterceptResponse::passthrough();
    }
  };

  // Non-blocking response cell: the handler is expected to call the responder
  // synchronously (before returning). We check immediately after the call — no
  // recv_timeout, no main-thread blocking.
  let response_cell: Arc<Mutex<Option<Response<Cow<'static, [u8]>>>>> = Arc::new(Mutex::new(None));
  let response_cell_clone = Arc::clone(&response_cell);

  let responder: Box<dyn FnOnce(Response<Cow<'static, [u8]>>)> = Box::new(move |resp| {
    *response_cell_clone.lock().unwrap() = Some(resp);
  });

  log::debug!(
    "[wry https-intercept] calling protocol handler for protocol='{}'...",
    protocol
  );
  (callback.0)(webview_id, request, RequestAsyncResponder { responder });
  log::debug!(
    "[wry https-intercept] protocol handler returned for protocol='{}'",
    protocol
  );

  // Check if the handler called the responder synchronously (inline).
  // This is the expected path for the default tauri asset handler.
  // NOTE: bind the Option to a local so the MutexGuard (from `.lock().unwrap()`)
  // drops before the end of the block — otherwise the guard's temporary borrow
  // outlives `response_cell` and trips E0597.
  let maybe_response = response_cell.lock().unwrap().take();
  match maybe_response {
    Some(response) => {
      let status = response.status().as_u16();
      let mime_type = response
        .headers()
        .get(http::header::CONTENT_TYPE)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("text/html")
        .to_string();
      let body = response.body().to_vec();
      // #186 (fix-variant M1): forward the protocol handler's response headers
      // to ArkTS (`WebResourceResponse.setResponseHeader`). Content-Type is
      // carried by `mime_type` and never duplicated (double-application risk in
      // ArkWeb); non-UTF-8 headers are skipped individually -- the same
      // degrade-safely rule as the request direction. An empty set stays `None`
      // so headerless responses keep the pre-M1 wire shape (D9).
      let mut header_names: Vec<String> = Vec::new();
      let mut header_values: Vec<String> = Vec::new();
      for (name, value) in response.headers().iter() {
        if name.as_str().eq_ignore_ascii_case("content-type") {
          continue;
        }
        // HeaderName is ASCII by construction (http crate) -- only the value
        // can carry non-UTF-8/opaque bytes. Mirrors the request-side
        // extraction at the wire build site below.
        let name_str = name.as_str();
        let Ok(value_str) = value.to_str() else {
          log::debug!("[wry https-intercept] skipping non-UTF8 response header '{name_str}'");
          continue;
        };
        header_names.push(name_str.to_string());
        header_values.push(value_str.to_string());
      }
      let (header_names, header_values) = if header_names.is_empty() {
        (None, None)
      } else {
        (Some(header_names), Some(header_values))
      };
      log::debug!(
        "[wry https-intercept] success: protocol='{}' status={} mime={} body_len={} resp_headers={}",
        protocol, status, mime_type, body.len(),
        header_names.as_ref().map(|n| n.len()).unwrap_or(0),
      );
      WebviewHttpsInterceptResponse {
        handled: true,
        status,
        mime_type,
        body,
        header_names,
        header_values,
      }
    }
    None => {
      // The handler did not call the responder synchronously. This means either:
      // 1. The handler is genuinely async (spawns a thread, calls responder later)
      // 2. The handler encountered an internal error and forgot to call the responder
      //
      // We CANNOT block here (design.md:369 prohibits rx.recv on main thread).
      // Return passthrough — ArkWeb will attempt a real fetch of https://tauri.localhost
      // which will fail (not a real domain), but this is the safest non-blocking option.
      log::warn!(
        "[wry https-intercept] handler did not respond synchronously for protocol='{}' url={} — returning passthrough (no blocking)",
        protocol, url
      );
      WebviewHttpsInterceptResponse::passthrough()
    }
  }
}

/// Returns true if any custom protocols are registered (used for https scheme logic).
/// Test-only: production code gates on `use_https && !protocols.is_empty()` inline.
#[cfg(test)]
fn custom_protocols_use_https(protocols: &HashMap<String, SharedProtocolHandler>) -> bool {
  !protocols.is_empty()
}

/// Rewrite `<protocol>://localhost/<path>` to `https://<protocol>.localhost/<path>`
/// when the URL's scheme matches one of `custom_protocols`' keys.
fn rewrite_https_url_if_matching(
  url: &str,
  custom_protocols: &HashMap<String, SharedProtocolHandler>,
) -> String {
  for protocol in custom_protocols.keys() {
    let original_prefix = format!("{}://", protocol);
    if url.starts_with(&original_prefix) {
      return custom_protocol_workaround::apply_uri_work_around(url, "https", protocol);
    }
  }
  url.to_string()
}

/// Formats an RGBA color as the ArkWeb `#AARRGGBB` string (alpha first).
fn rgba_to_argb_hex(color: RGBA) -> String {
  format!(
    "#{:02X}{:02X}{:02X}{:02X}",
    color.3, color.0, color.1, color.2
  )
}

/// Converts an `http::HeaderMap` into the bridge's `BTreeMap<String, String>`
/// form (header names as strings; non-UTF-8 values become empty).
fn headers_to_btree(headers: &http::HeaderMap) -> std::collections::BTreeMap<String, String> {
  headers
    .iter()
    .map(|(k, v)| (k.as_str().to_string(), v.to_str().unwrap_or("").to_string()))
    .collect()
}

/// Formats an `OffsetDateTime` as an RFC 6265 section 5.1.1 IMF-fixdate string in
/// UTC (e.g. `Thu, 01 Jan 2026 00:00:00 GMT`). Note IMF-fixdate is NOT the
/// same as RFC 2822 (`+0000` suffix etc.) -- ArkWeb expects the fixed form.
fn format_imf_fixdate(dt: cookie::time::OffsetDateTime) -> String {
  use cookie::time::UtcOffset;
  const WEEKDAYS: [&str; 7] = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
  const MONTHS: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
  ];
  let dt = dt.to_offset(UtcOffset::UTC);
  format!(
    "{}, {:02} {} {:04} {:02}:{:02}:{:02} GMT",
    WEEKDAYS[dt.weekday().number_days_from_monday() as usize],
    dt.day(),
    MONTHS[dt.month() as u8 as usize - 1],
    dt.year(),
    dt.hour(),
    dt.minute(),
    dt.second()
  )
}

/// Format a `cookie::Cookie` as a Set-Cookie value string (RFC 6265).
fn format_set_cookie_value(cookie: &Cookie<'_>) -> String {
  let mut value = format!("{}={}", cookie.name(), cookie.value());
  if let Some(d) = cookie.domain() {
    value.push_str(&format!("; Domain={}", d));
  }
  if let Some(p) = cookie.path() {
    value.push_str(&format!("; Path={}", p));
  }
  // Persistence attributes (#190(1)): emit Expires (IMF-fixdate) and Max-Age so
  // a persistent cookie does not degrade to a session cookie in ArkWeb. When
  // both are present RFC 6265 section 5.3 prefers Max-Age -- both are emitted here and
  // the receiving system applies the precedence. Session cookies carry neither.
  if let Some(cookie::Expiration::DateTime(dt)) = cookie.expires() {
    value.push_str(&format!("; Expires={}", format_imf_fixdate(dt)));
  }
  if let Some(max_age) = cookie.max_age() {
    value.push_str(&format!("; Max-Age={}", max_age.whole_seconds()));
  }
  if cookie.secure().unwrap_or(false) {
    value.push_str("; Secure");
  }
  if cookie.http_only().unwrap_or(false) {
    value.push_str("; HttpOnly");
  }
  if let Some(same_site) = cookie.same_site() {
    value.push_str(&format!("; SameSite={}", same_site));
  }
  value
}

/// Resolves the eval-callback payload for an evaluation outcome (#194).
/// Success keeps the existing semantics (result text; `None` -> empty), while
/// a failure yields the literal `"null"` so the awaiting promise settles
/// instead of hanging forever.
fn eval_callback_payload<E>(result: &std::result::Result<Option<String>, E>) -> String {
  match result {
    Ok(Some(s)) => s.clone(),
    Ok(None) => String::new(),
    Err(_) => "null".to_string(),
  }
}

/// Resolves the initial value of the URL cache for a created webview (#199):
/// the normalized initial URL (same https-rewrite the create request applies)
/// or an empty string when the webview is created from HTML with no URL.
fn url_cache_prefill(
  initial_url: Option<&str>,
  use_https: bool,
  protocols: &HashMap<String, SharedProtocolHandler>,
) -> String {
  match initial_url {
    Some(url) if use_https && !protocols.is_empty() => {
      rewrite_https_url_if_matching(url, protocols)
    }
    Some(url) => url.to_string(),
    None => String::new(),
  }
}

/// Parses the raw `fetchCookieSync` string (`"k=v; k2=v2"`) into owned cookies.
/// Shared by the worker-thread (async bridge) and main-thread (sync bridge)
/// paths of `cookies_for_url`.
fn parse_cookie_string(cookie_str: &str) -> Vec<Cookie<'static>> {
  cookie_str
    .split(';')
    .filter_map(|s| {
      let s = s.trim();
      if s.is_empty() {
        return None;
      }
      Cookie::parse(s.to_string()).map(|c| c.into_owned()).ok()
    })
    .collect()
}

#[cfg(test)]
mod tests {
  // Device-gated: `src/ohos` is entirely `#[cfg(target_env = "ohos")]`, so the
  // UTs below are only compiled and executed when the crate targets an
  // `*-unknown-linux-ohos` target (the aarch64 device or the x86_64
  // emulator). A host `cargo test` never builds them;
  // receipts for these tests must come from a device-target test binary run.
  use super::*;
  use cookie::SameSite;

  // PR review fix W3: UTs that rewrite the process-level `DEVTOOLS_ENABLED`
  // flag must not interleave -- the harness runs them on multiple threads and
  // unsynchronized save/store/restore sequences would flip each other's state
  // mid-assert (intermittent false reds). Every DEVTOOLS_ENABLED-touching UT
  // holds this mutex for its whole body.
  static DEVTOOLS_UT_LOCK: Mutex<()> = Mutex::new(());

  fn devtools_ut_lock() -> std::sync::MutexGuard<'static, ()> {
    DEVTOOLS_UT_LOCK
      .lock()
      .unwrap_or_else(|poisoned| poisoned.into_inner())
  }

  #[test]
  fn format_set_cookie_value_includes_core_attrs() {
    let cookie = Cookie::build(("token", "abc"))
      .domain("example.com")
      .path("/")
      .secure(true)
      .http_only(true)
      .same_site(SameSite::Lax)
      .build();
    let v = format_set_cookie_value(&cookie);
    assert!(v.starts_with("token=abc"));
    assert!(v.contains("; Domain=example.com"));
    assert!(v.contains("; Path=/"));
    assert!(v.contains("; Secure"));
    assert!(v.contains("; HttpOnly"));
    assert!(v.contains("; SameSite=Lax"));
  }

  #[test]
  fn format_set_cookie_value_minimal() {
    let cookie = Cookie::build(("k", "v")).build();
    assert_eq!(format_set_cookie_value(&cookie), "k=v");
  }

  // #190(1): persistence attributes survive the Set-Cookie formatting so a
  // persistent cookie does not degrade to a session cookie in ArkWeb.

  /// UT for #190(1): an expiration datetime is emitted as an IMF-fixdate
  /// `Expires` in UTC (RFC 6265 section 5.1.1), e.g. `Thu, 01 Jan 2026 00:00:00 GMT`.
  /// # Brief: build a cookie with a fixed expiry and assert the formatted
  /// attribute verbatim.
  #[test]
  fn ut_format_set_cookie_value_persistent_keeps_imf_fixdate_expires() {
    let dt = cookie::time::OffsetDateTime::new_utc(
      cookie::time::Date::from_calendar_date(2026, cookie::time::Month::January, 1).unwrap(),
      cookie::time::Time::MIDNIGHT,
    );
    let cookie = Cookie::build(("token", "abc")).expires(dt).build();
    let v = format_set_cookie_value(&cookie);
    assert!(
      v.contains("; Expires=Thu, 01 Jan 2026 00:00:00 GMT"),
      "IMF-fixdate Expires missing or malformed: {v}"
    );
  }

  /// UT for #190(1): a max-age duration is emitted as whole-second `Max-Age`.
  /// # Brief: build a cookie with max_age 3600s and assert `Max-Age=3600`.
  #[test]
  fn ut_format_set_cookie_value_max_age_whole_seconds() {
    let cookie = Cookie::build(("k", "v"))
      .max_age(cookie::time::Duration::seconds(3600))
      .build();
    let v = format_set_cookie_value(&cookie);
    assert!(v.contains("; Max-Age=3600"), "Max-Age missing: {v}");
    // Expiration came only from max_age -- no `Expires` must be invented.
    assert!(!v.contains("Expires="), "unexpected Expires: {v}");
  }

  /// UT for #190(1): a session cookie carries neither persistence attribute.
  /// # Brief: build a bare cookie and assert both attributes are absent.
  #[test]
  fn ut_format_set_cookie_value_session_omits_both_attributes() {
    let cookie = Cookie::build(("k", "v")).build();
    let v = format_set_cookie_value(&cookie);
    assert!(
      !v.contains("Expires="),
      "session cookie gained Expires: {v}"
    );
    assert!(
      !v.contains("Max-Age="),
      "session cookie gained Max-Age: {v}"
    );
  }

  /// UT for #190(1): when both attributes are present both are emitted (the
  /// RFC 6265 section 5.3 Max-Age precedence is the receiving side's semantics).
  /// # Brief: build a cookie with expiry + max-age and assert both appear.
  #[test]
  fn ut_format_set_cookie_value_emits_both_when_both_given() {
    let dt = cookie::time::OffsetDateTime::new_utc(
      cookie::time::Date::from_calendar_date(2026, cookie::time::Month::January, 1).unwrap(),
      cookie::time::Time::MIDNIGHT,
    );
    let cookie = Cookie::build(("k", "v"))
      .expires(dt)
      .max_age(cookie::time::Duration::seconds(60))
      .build();
    let v = format_set_cookie_value(&cookie);
    assert!(
      v.contains("; Expires=Thu, 01 Jan 2026 00:00:00 GMT"),
      "Expires missing: {v}"
    );
    assert!(v.contains("; Max-Age=60"), "Max-Age missing: {v}");
  }

  // #194: eval failures settle the awaiting callback with the literal "null".

  /// UT for #194: a failed evaluation maps to the `"null"` callback payload so
  /// the pending promise settles instead of hanging.
  /// # Brief: feed an `Err` outcome to the payload helper and assert `"null"`.
  #[test]
  fn ut_eval_callback_payload_failure_is_null() {
    let err = crate::Error::OpenHarmonyInitError("bridge gone".into());
    assert_eq!(eval_callback_payload(&Err(err)), "null");
  }

  /// UT for #194: successful evaluations keep the existing payload semantics
  /// (result passed through, `None` -> empty string).
  /// # Brief: feed `Ok` outcomes to the payload helper and assert both shapes.
  #[test]
  fn ut_eval_callback_payload_success_passthrough() {
    let ok_some: std::result::Result<Option<String>, crate::Error> = Ok(Some("42".to_string()));
    let ok_none: std::result::Result<Option<String>, crate::Error> = Ok(None);
    assert_eq!(eval_callback_payload(&ok_some), "42");
    assert_eq!(eval_callback_payload(&ok_none), "");
  }

  // #199: the URL cache is pre-filled with the (normalized) initial URL.

  /// UT for #199: a creation URL lands in the cache verbatim when no https
  /// rewrite applies, so the first IPC invoke resolves the real URL.
  /// # Brief: call the prefill helper with a URL and no protocols.
  #[test]
  fn ut_url_cache_prefill_uses_initial_url() {
    let empty: HashMap<String, SharedProtocolHandler> = HashMap::new();
    assert_eq!(
      url_cache_prefill(Some("https://example.com/app"), false, &empty),
      "https://example.com/app"
    );
  }

  /// UT for #199: HTML-created webviews (no URL) keep the empty cache so the
  /// existing about:blank fallback stays in effect.
  /// # Brief: call the prefill helper with `None`.
  #[test]
  fn ut_url_cache_prefill_empty_without_url() {
    let empty: HashMap<String, SharedProtocolHandler> = HashMap::new();
    assert_eq!(url_cache_prefill(None, false, &empty), "");
  }

  /// UT for #199: the prefill applies the same https-scheme rewrite the
  /// create request applies, so cache and request agree.
  /// # Brief: register the "tauri" protocol and assert the rewritten form.
  #[test]
  fn ut_url_cache_prefill_applies_https_rewrite() {
    let dummy: SharedProtocolHandler = Arc::new(SendSyncBox(Box::new(|_id, _req, _responder| {})));
    let mut protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    protocols.insert("tauri".to_string(), dummy);
    assert_eq!(
      url_cache_prefill(Some("tauri://localhost/index.html"), true, &protocols),
      "https://tauri.localhost/index.html"
    );
  }

  // This module is gated on `target_env = "ohos"`: these tests only run in
  // test builds for OHOS targets (host `cargo test` doesn't compile it).
  #[test]
  fn parse_cookie_string_parses_multiple_cookies() {
    let cookies = parse_cookie_string("k=v; k2=v2");
    assert_eq!(cookies.len(), 2);
    assert_eq!(cookies[0].name(), "k");
    assert_eq!(cookies[0].value(), "v");
    assert_eq!(cookies[1].name(), "k2");
    assert_eq!(cookies[1].value(), "v2");
  }

  #[test]
  fn parse_cookie_string_empty_input_yields_empty() {
    assert!(parse_cookie_string("").is_empty());
  }

  #[test]
  fn parse_cookie_string_whitespace_only_segments_yields_empty() {
    assert!(parse_cookie_string("  ;  ").is_empty());
  }

  #[test]
  fn parse_cookie_string_drops_invalid_segments() {
    // A segment without `=` is rejected by cookie 0.18's parse and dropped
    // via `.ok()`.
    let cookies = parse_cookie_string("k=v; novalue; k2=v2");
    assert_eq!(cookies.len(), 2);
  }

  #[test]
  fn parse_cookie_string_keeps_empty_value() {
    // cookie 0.18 parses `k=` as a valid cookie with an empty value.
    let cookies = parse_cookie_string("k=");
    assert_eq!(cookies.len(), 1);
    assert_eq!(cookies[0].name(), "k");
    assert_eq!(cookies[0].value(), "");
  }

  #[test]
  fn parse_cookie_string_value_may_contain_equals() {
    // Splits on the first `=`: name "k", value "a=b".
    let cookies = parse_cookie_string("k=a=b");
    assert_eq!(cookies.len(), 1);
    assert_eq!(cookies[0].name(), "k");
    assert_eq!(cookies[0].value(), "a=b");
  }

  #[test]
  fn parse_cookie_string_does_not_percent_decode() {
    // Plain `Cookie::parse` keeps values URL-encoded (decoding only happens
    // in the `*_encoded` variants), so the raw `%20` survives.
    let cookies = parse_cookie_string("k=a%20b");
    assert_eq!(cookies.len(), 1);
    assert_eq!(cookies[0].value(), "a%20b");
  }

  #[test]
  fn parse_cookie_string_drops_empty_name_segment() {
    // `=v` is rejected by cookie 0.18 (EmptyName) and dropped via `.ok()`.
    let cookies = parse_cookie_string("k=v; =novalue");
    assert_eq!(cookies.len(), 1);
    assert_eq!(cookies[0].name(), "k");
  }

  #[test]
  fn custom_protocols_use_https_returns_true_when_nonempty() {
    let empty: HashMap<String, SharedProtocolHandler> = HashMap::new();
    assert!(!custom_protocols_use_https(&empty));
  }

  #[test]
  fn rewrite_https_url_matches_registered_protocol() {
    // When the URL scheme matches a registered protocol key, it should be
    // rewritten to https://{protocol}.localhost/...
    let dummy: SharedProtocolHandler = Arc::new(SendSyncBox(Box::new(|_id, _req, _responder| {})));
    let mut protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    protocols.insert("tauri".to_string(), dummy);

    let url = "tauri://localhost/index.html";
    let rewritten = rewrite_https_url_if_matching(url, &protocols);
    assert_eq!(rewritten, "https://tauri.localhost/index.html");
  }

  #[test]
  fn rewrite_https_url_no_match_external_url() {
    // External URLs should not be rewritten
    let dummy: SharedProtocolHandler = Arc::new(SendSyncBox(Box::new(|_id, _req, _responder| {})));
    let mut protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    protocols.insert("tauri".to_string(), dummy);

    let url = "https://example.com/page";
    let rewritten = rewrite_https_url_if_matching(url, &protocols);
    assert_eq!(rewritten, url);
  }

  #[test]
  fn rewrite_https_url_no_match_empty_protocols() {
    // When no protocols are registered, URL should be unchanged
    let protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    let url = "tauri://localhost/index.html";
    let rewritten = rewrite_https_url_if_matching(url, &protocols);
    assert_eq!(rewritten, url);
  }

  #[test]
  fn rewrite_https_url_first_matching_protocol_wins() {
    // If multiple protocols are registered, the URL is rewritten using
    // the first matching protocol key (HashMap iteration order is unspecified,
    // but only one protocol prefix can match any given URL).
    let dummy: SharedProtocolHandler = Arc::new(SendSyncBox(Box::new(|_id, _req, _responder| {})));
    let mut protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    protocols.insert("tauri".to_string(), dummy.clone());
    protocols.insert("wry".to_string(), dummy);

    let url = "wry://localhost/path";
    let rewritten = rewrite_https_url_if_matching(url, &protocols);
    assert_eq!(rewritten, "https://wry.localhost/path");
  }

  #[test]
  fn https_intercept_non_localhost_host_is_handled() {
    // Host-agnostic matching (upstream `is_work_around_uri` semantics):
    // `https://asset.mydomain/x` must dispatch to the `asset` handler — the
    // old `.localhost`-only extractor dropped these requests.
    let resp = dispatch_https_intercept_sync(
      "https://asset.mydomain/x",
      "w1",
      &https_test_handler("asset", true),
      // older-plugin default shape: no method/headers on the wire
      None,
      None,
      None,
    );
    assert!(resp.handled);
    assert_eq!(resp.status, 201);
    assert_eq!(resp.mime_type, "application/json");
  }

  #[test]
  fn https_intercept_reverts_to_original_scheme_and_host() {
    // The handler must receive the reverted custom-scheme URL, host intact.
    let seen: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let seen_handler = Arc::clone(&seen);
    let handler: ProtocolHandler = Box::new(move |_id, req, responder| {
      *seen_handler.lock().unwrap() = Some(req.uri().to_string());
      let resp = http::Response::builder()
        .status(200)
        .body(Vec::new())
        .unwrap();
      responder.respond(resp);
    });
    let mut protocols: HashMap<String, SharedProtocolHandler> = HashMap::new();
    protocols.insert("asset".into(), Arc::new(SendSyncBox(handler)));

    let resp = dispatch_https_intercept_sync(
      "https://asset.mydomain/x?y=1",
      "w1",
      &protocols,
      None,
      None,
      None,
    );
    assert!(resp.handled);
    assert_eq!(
      *seen.lock().unwrap(),
      Some("asset://mydomain/x?y=1".to_string())
    );
  }

  #[test]
  fn format_set_cookie_value_with_path_only() {
    let cookie = Cookie::build(("session", "xyz")).path("/app").build();
    let v = format_set_cookie_value(&cookie);
    assert!(v.starts_with("session=xyz"));
    assert!(v.contains("; Path=/app"));
    assert!(!v.contains("; Secure"));
    assert!(!v.contains("; HttpOnly"));
  }

  #[test]
  fn format_set_cookie_value_with_same_site_strict() {
    let cookie = Cookie::build(("token", "abc"))
      .same_site(SameSite::Strict)
      .build();
    let v = format_set_cookie_value(&cookie);
    assert!(v.contains("; SameSite=Strict"));
  }

  #[test]
  fn format_set_cookie_value_with_same_site_none() {
    let cookie = Cookie::build(("token", "abc"))
      .same_site(SameSite::None)
      .build();
    let v = format_set_cookie_value(&cookie);
    assert!(v.contains("; SameSite=None"));
  }

  // ─── S7 pure-transform batch: branches of dispatch_https_intercept_sync ────────

  fn https_test_handler(
    protocol: &str,
    respond_inline: bool,
  ) -> HashMap<String, SharedProtocolHandler> {
    let mut m: HashMap<String, SharedProtocolHandler> = HashMap::new();
    let handler: ProtocolHandler = Box::new(move |_id, _req, responder| {
      if respond_inline {
        let resp = http::Response::builder()
          .status(201)
          .header("content-type", "application/json")
          .body(Vec::new())
          .unwrap();
        responder.respond(resp);
      }
      // respond_inline=false → handler returns without calling responder
      // → non-blocking check finds None → passthrough (no 3s wait)
    });
    m.insert(protocol.into(), Arc::new(SendSyncBox(handler)));
    m
  }

  #[test]
  fn https_intercept_non_https_url_passthrough() {
    let resp = dispatch_https_intercept_sync(
      "http://x.localhost/p",
      "w1",
      &HashMap::new(),
      None,
      None,
      None,
    );
    assert!(!resp.handled && resp.status == 0);
  }

  #[test]
  fn https_intercept_unregistered_protocol_passthrough() {
    let resp = dispatch_https_intercept_sync(
      "https://unknown.localhost/p",
      "w1",
      &https_test_handler("myproto", true),
      None,
      None,
      None,
    );
    assert!(!resp.handled && resp.status == 0);
  }

  #[test]
  fn https_intercept_invalid_uri_passthrough() {
    // Protocol registered, but the restored URI contains a space →
    // Request::builder fails → passthrough
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/a b",
      "w1",
      &https_test_handler("myproto", true),
      None,
      None,
      None,
    );
    assert!(!resp.handled && resp.status == 0);
  }

  #[test]
  fn https_intercept_inline_response_is_handled() {
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_test_handler("myproto", true),
      None,
      None,
      None,
    );
    assert!(resp.handled);
    assert_eq!(resp.status, 201);
    assert_eq!(resp.mime_type, "application/json");
  }

  #[test]
  fn https_intercept_unanswered_handler_returns_early_via_disconnect() {
    // handler returns without calling responder → response_cell is None
    // → non-blocking passthrough (no recv_timeout, no 3s wait)
    let start = std::time::Instant::now();
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/slow",
      "w1",
      &https_test_handler("myproto", false),
      None,
      None,
      None,
    );
    assert!(!resp.handled && resp.status == 0);
    assert!(start.elapsed() < std::time::Duration::from_secs(3));
  }

  // --- p3 fix-variant M1: response header write path (#186) ------------------

  /// UT for #186 M1: the protocol handler's response headers reach the wire
  /// struct as parallel arrays, with Content-Type excluded (it travels via
  /// `mime_type`) and non-UTF-8 headers skipped individually.
  /// # Brief: 1) register a handler that responds with two extra headers
  /// 2) dispatch through the intercept seam 3) assert the parallel arrays
  /// stay aligned, carry the custom header, and exclude Content-Type.
  #[test]
  fn ut_intercept_response_headers_are_forwarded() {
    let mut m: HashMap<String, SharedProtocolHandler> = HashMap::new();
    let handler: ProtocolHandler = Box::new(|_id, _req, responder| {
      let resp = http::Response::builder()
        .status(200)
        .header("content-type", "text/html")
        .header("Access-Control-Allow-Origin", "*")
        .header("X-Tauri-Scheme-Echo", "p3-m1-ok")
        .body(Vec::new())
        .unwrap();
      responder.respond(resp);
    });
    m.insert("myproto".into(), Arc::new(SendSyncBox(handler)));

    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/header-probe",
      "w1",
      &m,
      None,
      None,
      None,
    );
    assert!(resp.handled, "inline response must be handled");
    let names = resp
      .header_names
      .as_deref()
      .expect("response headers must be forwarded on the wire");
    let values = resp
      .header_values
      .as_deref()
      .expect("response header values must be forwarded on the wire");
    assert_eq!(
      names.len(),
      values.len(),
      "parallel arrays must stay aligned"
    );
    assert!(
      !names.iter().any(|n| n.eq_ignore_ascii_case("content-type")),
      "content-type must not be duplicated into the header arrays"
    );
    let echo_idx = names
      .iter()
      .position(|n| n.eq_ignore_ascii_case("x-tauri-scheme-echo"))
      .expect("the handler's custom header must survive the seam");
    assert_eq!(values[echo_idx], "p3-m1-ok");
  }

  /// UT for #186 M1 + D9: a handler that only sets Content-Type keeps the old
  /// wire shape -- header arrays stay `None` (byte-identical default).
  /// # Brief: 1) dispatch a Content-Type-only response 2) assert both header
  /// arrays stay `None`.
  #[test]
  fn ut_intercept_headerless_response_keeps_old_wire_shape() {
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_test_handler("myproto", true),
      None,
      None,
      None,
    );
    assert!(resp.handled);
    assert!(
      resp.header_names.is_none() && resp.header_values.is_none(),
      "content-type-only responses must keep the pre-M1 wire shape (None headers)"
    );
  }

  // --- p3 committer-issues batch: #189/#192/#195/#198 unit tests -------------

  // #198 (design D6): the vp conversion contract. Nothing here runs on the
  // host: `src/ohos` is device-gated and a host `cargo test` never builds
  // this path (see the module note above). The identity UT below pins the
  // mapping directly - it passes ratio 1.0 (the <=0/absent-binding fallback
  // value) into the conversion helpers and asserts physical coordinates come
  // back unchanged, so it depends on no host behavior and never calls the
  // `vp_ratio_sanitized` wrapper.

  /// UT for #198: vp = 1.0 (the <=0/absent-binding fallback; the OHOS
  /// desktop reference device reports vp = 1.9) is an identity --
  /// Physical(200,100) stays (200,100).
  /// # Brief: 1) convert a Physical position and size at ratio 1.0 2) assert
  /// both come back unchanged.
  #[test]
  fn ut_vp_conversion_identity_at_ratio_one() {
    let p = dpi::PhysicalPosition::new(200_i32, 100);
    assert_eq!(
      geometry_to_logical_vp(dpi::Position::Physical(p), 1.0),
      (200.0, 100.0)
    );
    let s = dpi::PhysicalSize::new(640_u32, 480);
    assert_eq!(
      size_to_logical_vp(dpi::Size::Physical(s), 1.0),
      (640.0, 480.0)
    );
  }

  /// UT for #198: vp = 2.0 halves Physical(200,100) -> (100,50), while a
  /// Logical input passes through unchanged (dpi identity contract).
  /// # Brief: 1) convert Physical position/size at ratio 2.0 and assert the
  /// halved values 2) convert a Logical input and assert it is unchanged.
  #[test]
  fn ut_vp_conversion_halves_physical_and_keeps_logical() {
    let p = dpi::PhysicalPosition::new(200_i32, 100);
    assert_eq!(
      geometry_to_logical_vp(dpi::Position::Physical(p), 2.0),
      (100.0, 50.0)
    );
    let s = dpi::PhysicalSize::new(200_u32, 100);
    assert_eq!(
      size_to_logical_vp(dpi::Size::Physical(s), 2.0),
      (100.0, 50.0)
    );
    let l = dpi::LogicalPosition::new(30.0_f64, 40.0);
    assert_eq!(
      geometry_to_logical_vp(dpi::Position::Logical(l), 2.0),
      (30.0, 40.0)
    );
  }

  /// Gate F6 (round 2): a Physical sentinel component maps 1:1 onto the
  /// sentinel LOGICAL value instead of being divided by vp - the ArkTS render
  /// layer screens logical values by exact sentinel equality, and a blind
  /// division would destroy that exact value and apply the sentinel as a real
  /// position. Real components still convert normally, and Logical sentinels
  /// pass through unchanged. PhysicalSize has no sentinel arm: its u32
  /// components can never equal the negative sentinel (documented on
  /// `size_to_logical_vp`).
  /// # Brief: 1) convert Physical(i32::MIN, 100) at vp=1.9 and assert the
  /// sentinel x is exact while y converts 2) same at vp=1.0 3) a Logical
  /// sentinel pair passes through unchanged.
  #[test]
  fn ut_geometry_to_logical_vp_maps_physical_sentinel_without_division() {
    let sentinel = i32::MIN as f64;
    let p = dpi::PhysicalPosition::new(i32::MIN, 100_i32);
    let (x, y) = geometry_to_logical_vp(dpi::Position::Physical(p), 1.9);
    assert_eq!(x, sentinel, "sentinel x must not be divided by vp");
    assert!(
      (y - 100.0 / 1.9).abs() < 1e-9,
      "a real component converts normally"
    );
    let (x, y) = geometry_to_logical_vp(dpi::Position::Physical(p), 1.0);
    assert_eq!(x, sentinel, "sentinel x stays exact at the identity ratio");
    assert_eq!(y, 100.0);
    let l = dpi::LogicalPosition::new(sentinel, 5.0);
    let (x, y) = geometry_to_logical_vp(dpi::Position::Logical(l), 1.9);
    assert_eq!(x, sentinel, "a Logical sentinel passes through unchanged");
    assert_eq!(y, 5.0);
  }

  /// UT for #198: the wrapper's sanitize guard is deterministic -- <=0, NaN and
  /// +/-inf fall back to exactly 1.0 (never a division hazard), real ratios pass
  /// through untouched. The LIVE binding value is device-real (1.9 on the
  /// desktop reference device), so the fallback contract is pinned on the pure
  /// guard, not on the environment.
  /// # Brief: 1) feed NaN / +/-inf / <=0 to the guard and assert exactly 1.0
  /// 2) feed real ratios and assert they pass through 3) assert the live
  /// binding value stays finite and positive.
  #[test]
  fn ut_vp_ratio_guard_falls_back_to_one() {
    assert_eq!(vp_ratio_sanitized(f64::NAN), 1.0);
    assert_eq!(vp_ratio_sanitized(f64::INFINITY), 1.0);
    assert_eq!(vp_ratio_sanitized(f64::NEG_INFINITY), 1.0);
    assert_eq!(vp_ratio_sanitized(0.0), 1.0);
    assert_eq!(vp_ratio_sanitized(-1.5), 1.0);
    assert_eq!(vp_ratio_sanitized(1.0), 1.0);
    assert_eq!(vp_ratio_sanitized(1.9), 1.9);
    assert_eq!(vp_ratio_sanitized(2.5), 2.5);
    // Totality of the live wrapper: whatever the binding reports on this
    // environment, the widened value is always finite and positive.
    let vp = virtual_pixel_ratio();
    assert!(
      vp.is_finite() && vp > 0.0,
      "live vp ratio must stay total, got {vp}"
    );
  }

  // #192 (design D4): the url() three-state router.

  /// UT for #192: Worker / Uninitialized states are cache-only -- zero bridge
  /// traffic, the cached value comes back unchanged (and nothing blocks: the
  /// non-Main arms never touch the bridge at all).
  /// # Brief: 1) seed the cache 2) query in Worker then Uninitialized state
  /// 3) assert the cached value returns unchanged.
  #[test]
  fn ut_url_worker_and_uninitialized_states_return_cache_only() {
    let cache = Mutex::new("tauri://localhost/".to_string());
    assert_eq!(
      url_with_main_thread_refresh(MainThreadStatus::Worker, "ut-w", &cache).unwrap(),
      "tauri://localhost/"
    );
    assert_eq!(
      url_with_main_thread_refresh(MainThreadStatus::Uninitialized, "ut-w", &cache).unwrap(),
      "tauri://localhost/"
    );
  }

  /// UT for #192: on the Main state a sync-bridge failure (host: the sync app
  /// handle is never registered in tests) falls back to the cached value --
  /// url() neither fails nor blocks (the refresh is a re-entrant MainThreadSync
  /// direct call; no recv_timeout exists anywhere on the path).
  /// # Brief: 1) seed the cache 2) query in Main state with no sync bridge
  /// registered 3) assert the cached value comes back.
  #[test]
  fn ut_url_main_state_bridge_failure_falls_back_to_cache() {
    let cache = Mutex::new("tauri://localhost/".to_string());
    assert_eq!(
      url_with_main_thread_refresh(MainThreadStatus::Main, "ut-w", &cache).unwrap(),
      "tauri://localhost/"
    );
  }

  // #195 (design D5): the process-level devtools intent + queue replay.

  /// UT for #195: the open intent flips exactly once -- the first open reports
  /// "dispatch owed", repeat opens are idempotent no-ops, and close re-arms
  /// the flag so a later open dispatches again.
  /// # Brief: 1) reset the flag 2) assert the first open reports dispatch owed
  /// and repeats are no-ops 3) close consumes the open 4) open after close
  /// dispatches again 5) restore the flag.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_devtools_open_intent_is_idempotent_and_close_re_arms() {
    let _guard = devtools_ut_lock();
    let saved = DEVTOOLS_ENABLED.load(Ordering::SeqCst);
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);
    assert!(devtools_open_intent(), "first open must dispatch");
    assert!(!devtools_open_intent(), "repeat open must be idempotent");
    assert!(
      !devtools_open_intent(),
      "third open must still be idempotent"
    );
    // Close returns the pre-swap flag: an applied/queued open is consumed, so
    // the FIRST close reports true (mirrors open's "flipped = dispatch owed").
    assert!(devtools_close_intent(), "close consumes the applied open");
    assert!(
      !devtools_close_intent(),
      "repeat close after consumption is a no-op"
    );
    assert!(
      devtools_open_intent(),
      "open after close must dispatch again"
    );
    DEVTOOLS_ENABLED.store(saved, Ordering::SeqCst);
  }

  /// UT for #195 + fix-variant m4: the pre-handshake open goes through the REAL
  /// `dispatch_or_queue_op` path (the exact production fn, not a scratch Vec) --
  /// queued in order while the handle is unset, rejected after a failed create
  /// (ops after failure must surface the error instead of queueing forever),
  /// and the create drain (`guard.drain(..)`, the Ok-branch semantics) empties
  /// the queue for replay.
  /// # Brief: 1) queue SetDevtools + Reload pre-handshake 2) fail the create
  /// and assert a follow-up op surfaces the error 3) drain and assert the
  /// queue is empty.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_dispatch_or_queue_set_devtools_real_path() {
    let queue: Arc<Mutex<Vec<PendingOp>>> = Arc::new(Mutex::new(Vec::new()));
    let handle: Arc<OnceLock<WebviewHandle>> = Arc::new(OnceLock::new());
    let creation_error: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let runtime = BridgeExecutor::new();

    // Pre-handshake: both ops land in the production queue, order preserved.
    dispatch_or_queue_op(
      &queue,
      &handle,
      &creation_error,
      &runtime,
      PendingOp::SetDevtools,
    )
    .expect("pre-handshake op must queue");
    dispatch_or_queue_op(
      &queue,
      &handle,
      &creation_error,
      &runtime,
      PendingOp::Reload,
    )
    .expect("pre-handshake op must queue");
    {
      let guard = queue.lock().unwrap();
      assert_eq!(guard.len(), 2, "both ops must sit in the production queue");
      assert!(
        matches!(guard[0], PendingOp::SetDevtools),
        "SetDevtools must keep its queue position for the create drain"
      );
    }

    // Failed create: `dispatch_or_queue_op` returns the creation error instead
    // of accepting ops that would never be replayed.
    *creation_error.lock().unwrap() = Some("injected create failure".to_string());
    assert!(
      dispatch_or_queue_op(
        &queue,
        &handle,
        &creation_error,
        &runtime,
        PendingOp::Reload
      )
      .is_err(),
      "ops after a failed create must surface the creation error"
    );

    // Create-drain semantics (Ok branch: `guard.drain(..)` then replay): the
    // drain collects exactly the queued ops and leaves the queue empty.
    let drained: Vec<PendingOp> = queue.lock().unwrap().drain(..).collect();
    assert_eq!(drained.len(), 2, "drain must collect the queued ops");
    assert!(
      queue.lock().unwrap().is_empty(),
      "drain must empty the queue"
    );
  }

  /// UT for #195 + fix-variant m5: a queued open that can never replay (failed
  /// create) releases the process-level intent via the REAL cleanup fn, so a
  /// later webview's open dispatches again instead of silently no-oping.
  /// # Brief: 1) flip the intent 2) run failed_create_cleanup over a queue
  /// holding SetDevtools 3) assert the queue empties and a later open
  /// dispatches again.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_failed_create_releases_queued_devtools_intent() {
    let _guard = devtools_ut_lock();
    let saved = DEVTOOLS_ENABLED.load(Ordering::SeqCst);
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);

    // The webview's open_devtools flips the intent and queues SetDevtools.
    assert!(devtools_open_intent(), "first open must flip the intent");

    let mut queue: Vec<PendingOp> = vec![PendingOp::SetDevtools, PendingOp::Reload];
    failed_create_cleanup(&mut queue);
    assert!(
      queue.is_empty(),
      "cleanup must drop the never-replayable ops"
    );
    assert!(
      devtools_open_intent(),
      "after the cleanup released the intent, a later open must dispatch again"
    );

    DEVTOOLS_ENABLED.store(saved, Ordering::SeqCst);
  }

  /// PR review fix W1: the open_devtools LAYER (not just `dispatch_or_queue_op`)
  /// releases the just-recorded open intent when the queue is dead (create
  /// already failed) -- otherwise the process-level flag latches and every
  /// later webview's open_devtools silently no-ops forever.
  /// # Brief: 1) flip the intent with the create already failed 2) run the
  /// real queue_pre_handshake_open 3) assert the intent was released and a
  /// later open dispatches again 4) positive control: a healthy queue holds
  /// the op and keeps the intent latched.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_open_devtools_dead_queue_releases_intent_for_later_opens() {
    let _guard = devtools_ut_lock();
    let saved = DEVTOOLS_ENABLED.load(Ordering::SeqCst);
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);

    let queue: Arc<Mutex<Vec<PendingOp>>> = Arc::new(Mutex::new(Vec::new()));
    let handle: Arc<OnceLock<WebviewHandle>> = Arc::new(OnceLock::new());
    let creation_error: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let runtime = BridgeExecutor::new();

    // open_devtools' first step flips the intent; then the None arm hits the
    // dead queue (create already failed -- the m4 state dispatch rejects).
    assert!(devtools_open_intent(), "first open must flip the intent");
    *creation_error.lock().unwrap() = Some("injected create failure".to_string());
    queue_pre_handshake_open(&queue, &handle, &creation_error, &runtime);

    assert!(
      !DEVTOOLS_ENABLED.load(Ordering::SeqCst),
      "the dead queue must release the process-level open intent"
    );
    assert!(
      queue.lock().unwrap().is_empty(),
      "the dead queue must not have accepted the open"
    );
    assert!(
      devtools_open_intent(),
      "after the release a later open must dispatch again (no permanent latch)"
    );
    // The probe above re-latched the flag; reset for the control phase.
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);

    // Positive control: with the queue healthy the same layered path queues
    // the op and the intent stays latched (idempotence fence intact).
    *creation_error.lock().unwrap() = None;
    assert!(devtools_open_intent(), "control open must flip the intent");
    queue_pre_handshake_open(&queue, &handle, &creation_error, &runtime);
    {
      let guard = queue.lock().unwrap();
      assert_eq!(guard.len(), 1, "the healthy queue must hold the open");
      assert!(
        matches!(guard[0], PendingOp::SetDevtools),
        "the queued op must be SetDevtools for the create drain"
      );
    }
    assert!(
      DEVTOOLS_ENABLED.load(Ordering::SeqCst),
      "a queued open keeps the intent latched (idempotence fence intact)"
    );

    DEVTOOLS_ENABLED.store(saved, Ordering::SeqCst);
  }

  /// W26-4: a failed async enable -- the ready-branch dispatch or the
  /// `PendingOp::SetDevtools` replay -- releases the process-level open intent
  /// through the REAL shared failure handler, so one failure can never latch
  /// the idempotence gate and swallow every later open_devtools in the
  /// process. Device-gated: this UT only compiles and executes when targeting
  /// an `*-unknown-linux-ohos` target (the aarch64 device or the x86_64
  /// emulator; `src/ohos` never builds on a host).
  /// # Brief: 1) flip the intent 2) run the real `devtools_open_failed` 3)
  /// assert the intent is released and a later open dispatches again.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_devtools_open_failed_releases_intent_for_later_opens() {
    let _guard = devtools_ut_lock();
    let saved = DEVTOOLS_ENABLED.load(Ordering::SeqCst);
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);

    assert!(
      devtools_open_intent(),
      "the open must flip the intent first"
    );
    devtools_open_failed(
      "open_devtools",
      &crate::Error::OpenHarmonyInitError("injected enable failure".into()),
    );
    assert!(
      !DEVTOOLS_ENABLED.load(Ordering::SeqCst),
      "the failed enable must release the process-level open intent"
    );
    assert!(
      devtools_open_intent(),
      "after the release a later open must dispatch again (no permanent latch)"
    );

    DEVTOOLS_ENABLED.store(saved, Ordering::SeqCst);
  }

  // Gate F5: the ready-branch dispatch releases the intent when the bridge
  // runtime's pump thread is already dead at spawn time (its async enable
  // future would otherwise never be polled and the idempotence fence would
  // latch forever).

  /// Gate F9 (round 2): a BridgeExecutor whose pump thread reports FINISHED -
  /// the exact observable state `pump_thread_alive` consumes in production
  /// once the thread has terminated. The production death mechanism (the
  /// `block_on(pending())` thread actually terminating) cannot be triggered
  /// from a UT, so the state is fabricated at the probe's observation point:
  /// a real JoinHandle of a thread that already exited. The `handle` field is
  /// a live executor's handle - the paths under test (probe, queue arm) never
  /// spawn through it.
  fn dead_pump_executor_for_ut() -> BridgeExecutor {
    let live = BridgeExecutor::new();
    let finished = std::thread::Builder::new()
      .name("ut-dead-pump".into())
      .spawn(|| {})
      .expect("failed to spawn the ut pump stand-in thread");
    let mut waited_ms = 0_u64;
    while !finished.is_finished() {
      std::thread::sleep(std::time::Duration::from_millis(1));
      waited_ms += 1;
      assert!(
        waited_ms < 2000,
        "the ut pump stand-in thread never finished"
      );
    }
    BridgeExecutor {
      handle: live.handle.clone(),
      pump_thread: Arc::new(Mutex::new(finished)),
    }
  }

  /// Gate F5: `pump_thread_alive` reports a live pump thread for a healthy
  /// executor (the probe the ready-branch `open_devtools` consults after
  /// spawning). The dead side of the probe cannot be produced by an actually
  /// terminated pump thread here (the shared runtime's thread is owned by the
  /// process-wide executor); it is pinned by the simulated-state UT below
  /// (`ut_bridge_executor_pump_thread_alive_probe_dead_side_simulated`).
  /// # Brief: 1) get the executor 2) assert `pump_thread_alive` is true.
  #[test]
  fn ut_bridge_executor_pump_thread_alive_probe_healthy() {
    let runtime = BridgeExecutor::new();
    assert!(
      runtime.pump_thread_alive(),
      "a fresh bridge runtime must report a live pump thread"
    );
  }

  /// Gate F9 (round 2): the DEAD side of the `pump_thread_alive` probe,
  /// simulated at its observation point (a finished JoinHandle stand-in).
  /// Production thread death itself stays un-simulatable in a UT (disclosed);
  /// this pins the probe's false arm that the ready-branch and queue-arm
  /// dead-pump guards consume.
  /// # Brief: 1) build the simulated-dead-pump executor 2) assert the probe
  /// reports false.
  #[test]
  fn ut_bridge_executor_pump_thread_alive_probe_dead_side_simulated() {
    let runtime = dead_pump_executor_for_ut();
    assert!(
      !runtime.pump_thread_alive(),
      "a finished pump-thread stand-in must report the dead state"
    );
  }

  /// Gate F2 (round 2): the pre-handshake QUEUE arm refuses an op when the
  /// bridge runtime's pump thread is already dead (the create drain that
  /// would replay it is polled by that very thread), and the open_devtools
  /// layer releases the just-recorded intent - the synchronous-Err leg now
  /// covers the queue arm too. The dead-pump STATE is simulated at the
  /// probe's observation point (a finished JoinHandle stand-in, see
  /// `dead_pump_executor_for_ut`); the production thread-death mechanism
  /// itself stays un-simulatable (disclosed, Gate F9).
  /// # Brief: 1) build the simulated-dead-pump executor 2) assert
  /// `dispatch_or_queue_op` refuses the op synchronously and the queue stays
  /// empty 3) run the real `queue_pre_handshake_open` and assert the intent
  /// is released and a later open dispatches again.
  #[cfg(any(debug_assertions, feature = "devtools"))]
  #[test]
  fn ut_queue_arm_dead_pump_refuses_op_and_releases_devtools_intent() {
    let _guard = devtools_ut_lock();
    let saved = DEVTOOLS_ENABLED.load(Ordering::SeqCst);
    DEVTOOLS_ENABLED.store(false, Ordering::SeqCst);

    let runtime = dead_pump_executor_for_ut();
    assert!(
      !runtime.pump_thread_alive(),
      "the stand-in must report the dead-pump state"
    );

    let queue: Arc<Mutex<Vec<PendingOp>>> = Arc::new(Mutex::new(Vec::new()));
    let handle: Arc<OnceLock<WebviewHandle>> = Arc::new(OnceLock::new());
    let creation_error: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));

    assert!(
      dispatch_or_queue_op(
        &queue,
        &handle,
        &creation_error,
        &runtime,
        PendingOp::Reload
      )
      .is_err(),
      "a dead pump must refuse the queue entry synchronously"
    );
    assert!(
      queue.lock().unwrap().is_empty(),
      "the dead-pump queue arm must not accept the op"
    );

    // open_devtools' None arm: the intent is flipped, then the queue attempt
    // hits the dead pump - the Err releases the intent (no latch).
    assert!(devtools_open_intent(), "the open flips the intent first");
    queue_pre_handshake_open(&queue, &handle, &creation_error, &runtime);
    assert!(
      !DEVTOOLS_ENABLED.load(Ordering::SeqCst),
      "the dead-pump queue arm must release the open intent"
    );
    assert!(
      devtools_open_intent(),
      "after the release a later open must dispatch again"
    );

    DEVTOOLS_ENABLED.store(saved, Ordering::SeqCst);
  }

  // ability-F6 (PR#26 review gate): tauri-runtime-wry's partial set_bounds
  // requests (issue Eulogizethesun/tauri#241) carry the i32::MIN sentinel for
  // the components a call does not set. The public bounds cache must never
  // hold the sentinel: bounds() readers would otherwise read back
  // -2147483648.0 as a real position/size component.

  /// ability-F6: `merge_bounds_into_cache` is the exact cache write of
  /// `set_bounds`, so what it leaves in the cache is what `bounds()` reads
  /// back. A sentinel-carrying component keeps its cached value; a component
  /// with only real values is replaced; a full request still replaces the
  /// cache wholesale (the pre-fix behavior must survive for full writes).
  /// Gate F5 (round 2): the merge is per COMPONENT - a mixed partial applies
  /// its real component while keeping the sentinel one, matching the ArkTS
  /// render granularity.
  /// # Brief: 1) seed the cache with the builder-default placeholder 2) merge
  /// a SetSize-shaped partial (sentinel position pair) 3) assert no -2^31
  /// component, preserved position, applied size 4) merge a SetPosition-shaped
  /// partial 5) merge two mixed partials and assert per-component results
  /// 6) merge a full request and assert the wholesale replace.
  #[test]
  fn ut_set_bounds_sentinel_components_never_enter_the_bounds_cache() {
    fn components(r: &Rect) -> (f64, f64, f64, f64) {
      let (px, py) = position_components(r.position);
      let (pw, ph) = size_components(r.size);
      (px, py, pw, ph)
    }

    let sentinel = i32::MIN as f64;

    // Seed: the builder-default placeholder a webview starts from.
    let mut cache = Rect {
      position: dpi::LogicalPosition::new(0.0, 0.0).into(),
      size: dpi::LogicalSize::new(200.0, 200.0).into(),
    };

    // SetSize-shaped partial (tauri-runtime-wry issue #241): the unset
    // position rides as the sentinel pair, the size is real.
    merge_bounds_into_cache(
      &mut cache,
      Rect {
        position: dpi::LogicalPosition::new(sentinel, sentinel).into(),
        size: dpi::LogicalSize::new(320.0, 240.0).into(),
      },
    );
    let (x, y, w, h) = components(&cache);
    assert_ne!(x, sentinel, "sentinel x must not enter the bounds cache");
    assert_ne!(y, sentinel, "sentinel y must not enter the bounds cache");
    assert_eq!(x, 0.0, "sentinel position keeps the cached value");
    assert_eq!(y, 0.0, "sentinel position keeps the cached value");
    assert_eq!(w, 320.0, "real size overwrites the cache");
    assert_eq!(h, 240.0, "real size overwrites the cache");

    // SetPosition-shaped partial: real position, sentinel size pair.
    merge_bounds_into_cache(
      &mut cache,
      Rect {
        position: dpi::LogicalPosition::new(15.0, 25.0).into(),
        size: dpi::LogicalSize::new(sentinel, sentinel).into(),
      },
    );
    let (x, y, w, h) = components(&cache);
    assert_ne!(w, sentinel, "sentinel width must not enter the cache");
    assert_ne!(h, sentinel, "sentinel height must not enter the cache");
    assert_eq!(x, 15.0, "real position overwrites the cache");
    assert_eq!(y, 25.0, "real position overwrites the cache");
    assert_eq!(w, 320.0, "sentinel size keeps the cached value");
    assert_eq!(h, 240.0, "sentinel size keeps the cached value");

    // Gate F5 (round 2): a mixed partial updates per COMPONENT, matching the
    // ArkTS render granularity - the sentinel x keeps the cached value while
    // the real y of the same request is applied (the whole-axis merge would
    // have discarded the real y).
    merge_bounds_into_cache(
      &mut cache,
      Rect {
        position: dpi::LogicalPosition::new(sentinel, 45.0).into(),
        size: dpi::LogicalSize::new(sentinel, sentinel).into(),
      },
    );
    let (x, y, w, h) = components(&cache);
    assert_eq!(x, 15.0, "sentinel x keeps the cached value");
    assert_eq!(y, 45.0, "real y of the mixed partial is applied");
    assert_eq!(w, 320.0, "sentinel width keeps the cached value");
    assert_eq!(h, 240.0, "sentinel height keeps the cached value");

    // Mirrored mixed partial: real x + sentinel y, and a mixed size partial.
    merge_bounds_into_cache(
      &mut cache,
      Rect {
        position: dpi::LogicalPosition::new(25.0, sentinel).into(),
        size: dpi::LogicalSize::new(400.0, sentinel).into(),
      },
    );
    let (x, y, w, h) = components(&cache);
    assert_eq!(x, 25.0, "real x of the mixed partial is applied");
    assert_eq!(y, 45.0, "sentinel y keeps the cached value");
    assert_eq!(w, 400.0, "real width of the mixed partial is applied");
    assert_eq!(h, 240.0, "sentinel height keeps the cached value");

    // Control: a full request (no sentinel component) replaces the cache
    // wholesale, including across variants.
    merge_bounds_into_cache(
      &mut cache,
      Rect {
        position: dpi::PhysicalPosition::new(5_i32, 6_i32).into(),
        size: dpi::PhysicalSize::new(7_u32, 8_u32).into(),
      },
    );
    let (x, y, w, h) = components(&cache);
    assert_eq!(x, 5.0, "a full request replaces the position wholesale");
    assert_eq!(y, 6.0, "a full request replaces the position wholesale");
    assert_eq!(w, 7.0, "a full request replaces the size wholesale");
    assert_eq!(h, 8.0, "a full request replaces the size wholesale");
  }

  /// Gate F10 (round 2): the set_bounds PUBLIC path pins the merge call
  /// site - a mixed partial driven through the production body
  /// (`set_bounds_with_cache`, the exact body `InnerWebView::set_bounds`
  /// delegates to) reads back per-component through the bounds() shape (the
  /// cache deref). The body is factored out exactly like
  /// `dispatch_or_queue_op` because a UT cannot build `InnerWebView`:
  /// `WebviewClient` needs a live NAPI bridge session and has no NAPI-free
  /// constructor.
  /// # Brief: 1) seed the cache 2) run the real set_bounds body with a mixed
  /// partial (sentinel x + real y, real w + sentinel h) 3) read back and
  /// assert the per-component results 4) assert the op was queued for replay.
  #[test]
  fn ut_set_bounds_public_path_mixed_partial_reads_back_per_component() {
    let pending_ops: Arc<Mutex<Vec<PendingOp>>> = Arc::new(Mutex::new(Vec::new()));
    let handle: Arc<OnceLock<WebviewHandle>> = Arc::new(OnceLock::new());
    let creation_error: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
    let runtime = BridgeExecutor::new();
    let bounds_cache = Mutex::new(Rect {
      position: dpi::LogicalPosition::new(10.0, 20.0).into(),
      size: dpi::LogicalSize::new(100.0, 50.0).into(),
    });

    set_bounds_with_cache(
      &pending_ops,
      &handle,
      &creation_error,
      &runtime,
      &bounds_cache,
      Rect {
        position: dpi::LogicalPosition::new(i32::MIN as f64, 30.0).into(),
        size: dpi::LogicalSize::new(200.0, i32::MIN as f64).into(),
      },
    )
    .expect("a live pump must accept the op");

    // bounds() read-back shape: `Ok(*bounds_cache.lock().unwrap())`.
    let cached = *bounds_cache.lock().unwrap();
    let (x, y) = position_components(cached.position);
    let (w, h) = size_components(cached.size);
    assert_eq!(x, 10.0, "sentinel x keeps the cached value");
    assert_eq!(y, 30.0, "real y is applied (per-component merge)");
    assert_eq!(w, 200.0, "real width is applied (per-component merge)");
    assert_eq!(h, 50.0, "sentinel height keeps the cached value");
    assert_eq!(
      pending_ops.lock().unwrap().len(),
      1,
      "the live-pump path queues the op for replay"
    );
  }

  // #189 (design D3): the unified dispose fence.

  /// UT for #189: the fence fires exactly once -- a fresh webview owes the
  /// `Remove` dispatch (main webviews included: the is_child gate is gone),
  /// and the second call (double Drop / double dispose) is a no-op.
  /// # Brief: 1) dispose three times 2) assert only the first reports a
  /// dispatch owed and the flag ends true.
  #[test]
  fn ut_dispose_fence_fires_once_and_double_drop_is_noop() {
    let disposed = AtomicBool::new(false);
    assert!(
      dispose_once(&disposed),
      "first dispose must dispatch Remove"
    );
    assert!(!dispose_once(&disposed), "double dispose must be a no-op");
    assert!(
      !dispose_once(&disposed),
      "triple dispose must still be a no-op"
    );
    assert!(disposed.load(Ordering::SeqCst));
  }

  // #186 (design D2): the intercepted request's method + parallel header
  // arrays reach the protocol handler through the Request builder; missing
  // wire fields (older plugins) and malformed values degrade safely.

  /// Capture handler: records `method=...`, `uri=...` and one `header:name=value`
  /// line per received header, then responds inline.
  fn https_capture_handler(
    protocol: &str,
    captured: Arc<Mutex<Vec<String>>>,
  ) -> HashMap<String, SharedProtocolHandler> {
    let mut m: HashMap<String, SharedProtocolHandler> = HashMap::new();
    let handler: ProtocolHandler = Box::new(move |_id, req, responder| {
      let mut c = captured.lock().unwrap();
      c.push(format!("method={}", req.method()));
      c.push(format!("uri={}", req.uri()));
      for (name, value) in req.headers() {
        if let Ok(v) = value.to_str() {
          c.push(format!("header:{}={v}", name.as_str()));
        }
      }
      drop(c);
      let resp = http::Response::builder()
        .status(200)
        .body(Vec::new())
        .unwrap();
      responder.respond(resp);
    });
    m.insert(protocol.into(), Arc::new(SendSyncBox(handler)));
    m
  }

  fn captured_lines(captured: &Arc<Mutex<Vec<String>>>) -> Vec<String> {
    captured.lock().unwrap().clone()
  }

  /// UT for #186: a POST method with parallel header arrays is rebuilt on the
  /// handler's Request (names and values stay paired, in order).
  /// # Brief: 1) dispatch a POST with two parallel header arrays 2) assert the
  /// method and both paired headers reach the handler.
  #[test]
  fn ut_intercept_method_and_headers_reach_handler() {
    let captured = Arc::new(Mutex::new(Vec::new()));
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_capture_handler("myproto", Arc::clone(&captured)),
      Some("POST"),
      Some(&["x-test".to_string(), "accept".to_string()]),
      Some(&["1".to_string(), "application/json".to_string()]),
    );
    assert!(resp.handled);
    let lines = captured_lines(&captured);
    assert!(lines.contains(&"method=POST".to_string()), "{lines:?}");
    assert!(
      lines.contains(&"header:x-test=1".to_string()),
      "header 1 missing: {lines:?}"
    );
    assert!(
      lines.contains(&"header:accept=application/json".to_string()),
      "header 2 missing: {lines:?}"
    );
  }

  /// UT for W26-5: body-framing headers (`content-length` /
  /// `transfer-encoding`) are dropped from the forwarded set -- the rebuilt
  /// request's body is always empty, so forwarding a stale framing header
  /// would make a downstream consumer wait for body bytes that never arrive.
  /// Dropped case-insensitively; unrelated headers pass through untouched.
  /// # Brief: 1) dispatch with mixed-case framing headers + one regular
  /// header 2) assert both framing headers are gone and the regular header
  /// survives.
  #[test]
  fn ut_intercept_body_framing_headers_are_dropped() {
    let captured = Arc::new(Mutex::new(Vec::new()));
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_capture_handler("myproto", Arc::clone(&captured)),
      Some("POST"),
      Some(&[
        "Content-Length".to_string(),
        "transfer-encoding".to_string(),
        "x-keep".to_string(),
      ]),
      Some(&["10".to_string(), "chunked".to_string(), "1".to_string()]),
    );
    assert!(resp.handled);
    let lines = captured_lines(&captured);
    assert!(
      !lines.iter().any(|l| l.starts_with("header:content-length")),
      "stale content-length must not reach the handler: {lines:?}"
    );
    assert!(
      !lines
        .iter()
        .any(|l| l.starts_with("header:transfer-encoding")),
      "stale transfer-encoding must not reach the handler: {lines:?}"
    );
    assert!(
      lines.contains(&"header:x-keep=1".to_string()),
      "unrelated headers must pass through: {lines:?}"
    );
  }

  /// UT for #186: no wire fields (older ArkTS bridge plugins) keep the
  /// historical shape -- method defaults to GET and no headers are attached.
  /// # Brief: 1) dispatch with all wire fields absent 2) assert GET and zero
  /// headers on the handler's Request.
  #[test]
  fn ut_intercept_missing_fields_fall_back_to_get_no_headers() {
    let captured = Arc::new(Mutex::new(Vec::new()));
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_capture_handler("myproto", Arc::clone(&captured)),
      None,
      None,
      None,
    );
    assert!(resp.handled);
    let lines = captured_lines(&captured);
    assert!(lines.contains(&"method=GET".to_string()), "{lines:?}");
    assert!(
      !lines.iter().any(|l| l.starts_with("header:")),
      "unexpected headers on the default shape: {lines:?}"
    );
  }

  /// UT for #186: a malformed method falls back to GET, and a single invalid
  /// header name is skipped without sinking the request or its valid peers.
  /// # Brief: 1) dispatch a malformed method + one bad header name 2) assert
  /// the GET fallback and that the valid peer header survives.
  #[test]
  fn ut_intercept_invalid_method_and_headers_degrade_safely() {
    let captured = Arc::new(Mutex::new(Vec::new()));
    let resp = dispatch_https_intercept_sync(
      "https://myproto.localhost/data",
      "w1",
      &https_capture_handler("myproto", Arc::clone(&captured)),
      Some("BAD METHOD"), // space -> Method::from_bytes fails -> GET
      Some(&["bad name".to_string(), "ok-name".to_string()]),
      Some(&["v1".to_string(), "v2".to_string()]),
    );
    assert!(resp.handled, "one bad header must not fail the request");
    let lines = captured_lines(&captured);
    assert!(lines.contains(&"method=GET".to_string()), "{lines:?}");
    assert!(
      lines.contains(&"header:ok-name=v2".to_string()),
      "valid peer header lost: {lines:?}"
    );
    assert!(
      !lines.iter().any(|l| l.contains("bad name")),
      "invalid header name leaked: {lines:?}"
    );
  }
}
