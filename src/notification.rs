//! Freedesktop notifications and AnDWM-style notification history.
//!
//! This is the Rust port of `notification_*` in AnDWM's `dwm.c`: the same
//! center ARGB window, queue/history lifecycle, D-Bus interface, text layout,
//! GL glyphs and vertical opacity ramp. The existing `gl` and `Drw` plumbing is
//! shared with Finder so the popup never exposes a stale clock-sized patch.

use std::collections::{HashMap, VecDeque};
use std::error::Error;
use std::ffi::{CStr, CString, c_char, c_double, c_int};
use std::hash::{Hash, Hasher};
use std::path::Path;
use std::ptr;
use std::sync::Arc;
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::time::{Duration, Instant};

use x11::keysym::{XK_BackSpace, XK_Escape, XK_KP_Enter, XK_Return};
use x11::xft::{FcPattern, XftFont, XftFontClose, XftFontOpenName};
use x11::xlib;
use x11::xrender;
use zbus::blocking::{Connection, fdo};
use zbus::fdo::{RequestNameFlags, RequestNameReply};
use zbus::message::Message;
use zbus::names::WellKnownName;
use zbus::zvariant::{
    Array as ZArray, NATIVE_ENDIAN, OwnedValue, serialized::Context, to_bytes_for_signature,
};

use crate::bar::CLOCKPAD;
use crate::drw::Drw;
use crate::gl::{GlFont, GlFontSpec, GlPbuffer, GlSurface, compat};
use crate::text::FONTS;

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

const SERVICE: &str = "org.freedesktop.Notifications";
const PATH: &str = "/org/freedesktop/Notifications";
const IFACE: &str = "org.freedesktop.Notifications";

const NOTIFY_MAX: usize = 5;
const NOTIFY_TIMEOUT: Duration = Duration::from_secs(5);
const NOTIFY_TRANSITION: Duration = Duration::from_millis(500);
const NOTIFY_HOVER_GRACE: Duration = Duration::from_millis(400);
const NOTIFY_MAX_W: i32 = 300;
const NOTIFY_PADDING: i32 = 15;
const NOTIFY_IMAGE_MAX_H: i32 = 60;
const NOTIFY_IMAGE_MAX_W: i32 = 100;
const NOTIFY_IMAGE_RADIUS: i32 = 16;
const NOTIFY_INPUT_ROW_H: i32 = 24;
const NOTIFY_BUTTON_H: i32 = 24;
const NOTIFY_BODY_LINE_GAP: i32 = 0;
const NOTIFY_POPUP_BODY_MAX_LINES: usize = 2;
const NOTIFY_POPUP_BODY_HOVER_MAX_LINES: usize = 4;
const NOTIFY_HISTORY_BODY_MAX_LINES: usize = 2;
const NOTIFY_HISTORY_TIME_GAP: i32 = 8;
const NOTIFY_HISTORY_TIME_SCALE: f64 = 0.75;
const NOTIFY_HISTORY_TEXT_ONLY_OFFSET: i32 = 5;
const NOTIFY_HISTORY_MAX: usize = 10;
const NOTIFY_HISTORY_MAX_H: i32 = 400;
const NOTIFY_HISTORY_FPS: Duration = Duration::from_millis(10);
const HISTORY_SCROLL_TIME: f64 = 0.055;
const HISTORY_SCROLL_STEP: i32 = 60;

const GL_PBUFFER_MAX_WIDTH: u32 = 550;
const GL_PBUFFER_MAX_HEIGHT: u32 = 2048;

/// dwm's `notification_history_background_create()` color (dwm.c 9744). Both
/// the popup and history composite their foreground over this through the same
/// vertical opacity mask.
const POPUP_BACKGROUND: (u16, u16, u16, u16) = (7864, 8519, 11141, 65535);

/// GL text colours, copied from dwm.c rather than the `Clr` scheme: dwm's
/// notification renderer never reads those scheme entries.
const FG: (f32, f32, f32) = (1.0, 1.0, 1.0);
const BODY: (f32, f32, f32) = (0.82, 0.85, 0.9);
const ACTION: (f32, f32, f32) = (0.82, 0.85, 0.9);
const CONTROL_TEXT: (f32, f32, f32) = (0.92, 0.93, 0.96);
const PLACEHOLDER: (f32, f32, f32) = (0.58, 0.61, 0.66);
const DIM_SUMMARY: (f32, f32, f32) = (0.84, 0.86, 0.90);
const DIM_BODY: (f32, f32, f32) = (0.56, 0.58, 0.61);
const DIM_MEDIA: (f32, f32, f32) = (0.68, 0.70, 0.73);
const DIM_TIME: (f32, f32, f32) = (0.48, 0.51, 0.55);
const TIME: (f32, f32, f32) = (0.66, 0.69, 0.74);

#[derive(Clone, Debug)]
struct ImageData {
    pixels: Vec<u32>,
    width: u32,
    height: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct NotificationData {
    id: u32,
    app_name: String,
    summary: String,
    body: String,
    actions: Vec<String>,
    input_enabled: bool,
    input_action: String,
    input_placeholder: String,
    input_text: String,
    image: Option<Arc<ImageData>>,
    received_time: String,
}

#[derive(Clone, Debug)]
pub(crate) enum Event {
    New(NotificationData),
    Close(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CenterClass {
    Dwm,
    Notification,
    History,
}

#[derive(Clone)]
struct Entry {
    data: NotificationData,
    shown_at: Instant,
    action_used: bool,
    /// Cached popup layout, matching dwm's `notify_*` globals.
    text_y: i32,
    image_y: i32,
    input_y: i32,
    action_y: i32,
    action_x: Vec<i32>,
    action_w: Vec<i32>,
}

impl Entry {
    fn new(data: NotificationData) -> Entry {
        Entry {
            data,
            shown_at: Instant::now(),
            action_used: false,
            text_y: 0,
            image_y: 0,
            input_y: 0,
            action_y: 0,
            action_x: Vec::new(),
            action_w: Vec::new(),
        }
    }
}

/// Service state lives on zbus's blocking executor thread. New notifications
/// are forwarded to the WM; close/action signals are emitted from the WM using
/// the returned connection.
struct NotifyService {
    tx: SyncSender<Event>,
    next_id: u32,
}

#[zbus::interface(name = "org.freedesktop.Notifications")]
impl NotifyService {
    fn get_capabilities(&self) -> Vec<String> {
        [
            "actions",
            "body",
            "body-markup",
            "icon-static",
            "image-data",
            "image-path",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect()
    }

    fn get_server_information(&self) -> (String, String, String, String) {
        ("AnDWM".into(), "AnDWM".into(), "1".into(), "1.2".into())
    }

    fn close_notification(&self, id: u32) {
        let _ = self.tx.try_send(Event::Close(id));
    }

    fn notify(
        &mut self,
        app_name: &str,
        replaces_id: u32,
        icon: &str,
        summary: &str,
        body: &str,
        actions: Vec<String>,
        hints: HashMap<String, OwnedValue>,
        _expire_timeout: i32,
    ) -> u32 {
        let id = if replaces_id != 0 {
            replaces_id
        } else {
            let id = self.next_id;
            self.next_id = self.next_id.wrapping_add(1).max(1);
            id
        };
        let data = parse_notification(id, app_name, icon, summary, body, actions, hints);
        let _ = self.tx.try_send(Event::New(data));
        id
    }
}

pub(crate) struct ServiceHandle {
    pub rx: Receiver<Event>,
    pub connection: Arc<Connection>,
}

/// Starts the D-Bus service. `None` means another notification server already
/// owns the well-known name, which is the same outcome as AnDWM's failed
/// `DBUS_REQUEST_NAME_REPLY_PRIMARY_OWNER` check.
pub(crate) fn start_service() -> Result<Option<ServiceHandle>> {
    let connection = Arc::new(Connection::session()?);
    let owner = fdo::DBusProxy::new(connection.as_ref())?.request_name(
        WellKnownName::from_static_str(SERVICE)?,
        RequestNameFlags::ReplaceExisting.into(),
    )?;
    if owner != RequestNameReply::PrimaryOwner {
        return Ok(None);
    }
    let (tx, rx) = mpsc::sync_channel(32);
    connection
        .object_server()
        .at(PATH, NotifyService { tx, next_id: 1 })?;
    Ok(Some(ServiceHandle { rx, connection }))
}

fn send_flat_signal(connection: &Connection, member: &str, signature: &str, body: &[u8]) {
    let send = || -> std::result::Result<(), zbus::Error> {
        let builder = Message::signal(PATH, IFACE, member)?;
        // The body bytes are produced by zvariant with the same native endian
        // and signature that the builder writes into the message header.
        let message = unsafe { builder.build_raw_body(body, signature, vec![])? };
        connection.send(&message)
    };
    let _ = send();
}

pub fn emit_action(connection: &Connection, id: u32, action: &str) {
    let Ok(body) = to_bytes_for_signature(Context::new_dbus(NATIVE_ENDIAN, 0), "us", &(id, action))
    else {
        return;
    };
    send_flat_signal(connection, "ActionInvoked", "us", body.bytes());
}

pub fn emit_input(connection: &Connection, id: u32, action: &str, text: &str) {
    let Ok(body) = to_bytes_for_signature(
        Context::new_dbus(NATIVE_ENDIAN, 0),
        "uss",
        &(id, action, text),
    ) else {
        return;
    };
    send_flat_signal(connection, "InputSubmitted", "uss", body.bytes());
}

pub fn emit_closed(connection: &Connection, id: u32, reason: u32) {
    let Ok(body) = to_bytes_for_signature(Context::new_dbus(NATIVE_ENDIAN, 0), "uu", &(id, reason))
    else {
        return;
    };
    send_flat_signal(connection, "NotificationClosed", "uu", body.bytes());
}

fn parse_notification(
    id: u32,
    app_name: &str,
    icon: &str,
    summary: &str,
    body: &str,
    actions: Vec<String>,
    hints: HashMap<String, OwnedValue>,
) -> NotificationData {
    let mut icon = icon.to_string();
    let mut image = None;
    let input_action_hint = string_value(&hints, "x-andwm-input-action");
    let mut input_action = input_action_hint.clone().unwrap_or_default();
    // dwm enables the input row with either hint, including an empty action
    // string, then fills in the legacy "submit" action name when the client
    // did not supply one.
    let input_enabled = bool_value(&hints, "x-andwm-input") || input_action_hint.is_some();
    if input_enabled && input_action.is_empty() {
        input_action = "submit".to_string();
    }
    let input_placeholder = string_value(&hints, "x-andwm-input-placeholder").unwrap_or_default();
    if let Some(path) = string_value(&hints, "image-path") {
        icon = path;
    }
    if let Some(data) = image_value(&hints) {
        image = load_image_bytes(
            data.width,
            data.height,
            data.rowstride,
            data.has_alpha,
            &data.bytes,
        );
    }
    if image.is_none() && !icon.is_empty() {
        image = load_image_path(&icon);
    }

    let mut actions = actions;
    if actions.len() % 2 != 0 {
        actions.pop();
    }
    NotificationData {
        id,
        app_name: app_name.to_string(),
        summary: summary.to_string(),
        body: body.to_string(),
        actions,
        input_enabled,
        input_action,
        input_placeholder,
        input_text: String::new(),
        image,
        received_time: now_received_time(),
    }
}

struct RawImage {
    width: u32,
    height: u32,
    rowstride: u32,
    has_alpha: bool,
    bytes: Vec<u8>,
}

fn bool_value(hints: &HashMap<String, OwnedValue>, key: &str) -> bool {
    hints
        .get(key)
        .and_then(|v| v.downcast_ref::<bool>().ok())
        .unwrap_or(false)
}

fn string_value(hints: &HashMap<String, OwnedValue>, key: &str) -> Option<String> {
    let value = hints.get(key)?;
    let text: &str = value.downcast_ref().ok()?;
    Some(text.to_string())
}

fn image_value(hints: &HashMap<String, OwnedValue>) -> Option<RawImage> {
    let value = hints.get("image-data")?;
    let structure: &zbus::zvariant::Structure = value.downcast_ref().ok()?;
    let fields = structure.fields();
    if fields.len() < 7 {
        return None;
    }
    let width = fields[0].downcast_ref::<i32>().ok()?;
    let height = fields[1].downcast_ref::<i32>().ok()?;
    let rowstride = fields[2].downcast_ref::<i32>().ok()?;
    let has_alpha = fields[3].downcast_ref::<bool>().ok()?;
    let bits = fields[4].downcast_ref::<i32>().ok()?;
    let channels = fields[5].downcast_ref::<i32>().ok()?;
    let array: ZArray = fields[6].downcast_ref().ok()?;
    let bytes: Vec<u8> = Vec::try_from(array).ok()?;
    if width <= 0
        || height <= 0
        || width > 2048
        || height > 2048
        || rowstride <= 0
        || i64::from(rowstride) < i64::from(width) * 4
        || bits != 8
        || channels != 4
        || bytes.len() > 16 * 1024 * 1024
        || bytes.len() < (i64::from(rowstride) * i64::from(height)) as usize
    {
        return None;
    }
    Some(RawImage {
        width: width as u32,
        height: height as u32,
        rowstride: rowstride as u32,
        has_alpha,
        bytes,
    })
}

fn load_image_bytes(
    width: u32,
    height: u32,
    rowstride: u32,
    has_alpha: bool,
    bytes: &[u8],
) -> Option<Arc<ImageData>> {
    let mut pixels = Vec::with_capacity((width * height) as usize);
    for y in 0..height as usize {
        let row = &bytes[y * rowstride as usize..];
        for x in 0..width as usize {
            let p = x * 4;
            if p + 3 >= row.len() {
                break;
            }
            let alpha = if has_alpha { row[p + 3] } else { 255 };
            pixels.push(pack_argb(row[p], row[p + 1], row[p + 2], alpha));
        }
    }
    Arc::new(prepare_image(pixels, width, height)).into()
}

fn load_image_path(path: &str) -> Option<Arc<ImageData>> {
    let path = Path::new(path);
    if !path.is_file() {
        return None;
    }
    let image = image::open(path).ok()?.to_rgba8();
    let (width, height) = image.dimensions();
    let pixels = image
        .chunks_exact(4)
        .map(|p| pack_argb(p[0], p[1], p[2], p[3]))
        .collect();
    Arc::new(prepare_image(pixels, width, height)).into()
}

fn pack_argb(r: u8, g: u8, b: u8, a: u8) -> u32 {
    (u32::from(a) << 24) | (u32::from(r) << 16) | (u32::from(g) << 8) | u32::from(b)
}

fn fit_size(src_w: u32, src_h: u32, max_w: u32, max_h: u32) -> (u32, u32) {
    if src_w == 0 || src_h == 0 {
        return (1, 1);
    }
    let mut w = src_w;
    let mut h = src_h;
    if w > max_w {
        h = ((h as u64 * max_w as u64) / w as u64).max(1) as u32;
        w = max_w;
    }
    if h > max_h {
        w = ((w as u64 * max_h as u64) / h as u64).max(1) as u32;
        h = max_h;
    }
    (w.max(1), h.max(1))
}

/// Applies dwm's rounded-corner coverage to the source pixels at the display
/// size, so the same source works for the GL path and for icons in history.
fn prepare_image(pixels: Vec<u32>, src_w: u32, src_h: u32) -> ImageData {
    // dwm rounds the source alpha at the size the icon is actually drawn,
    // after capping the fitted width at 100px.
    let (mut draw_w, mut draw_h) = fit_size(src_w, src_h, 260, NOTIFY_IMAGE_MAX_H as u32);
    if draw_w > NOTIFY_IMAGE_MAX_W as u32 {
        let fitted_w = draw_w;
        draw_w = NOTIFY_IMAGE_MAX_W as u32;
        draw_h = ((draw_h as u64 * draw_w as u64) / fitted_w as u64).max(1) as u32;
    }
    let radius = (NOTIFY_IMAGE_RADIUS as f32)
        .min(draw_w.min(draw_h) as f32 / 2.0)
        .max(0.0);
    if radius <= 0.0 || src_w == 0 {
        return ImageData {
            pixels,
            width: src_w,
            height: src_h,
        };
    }
    let scale_x = src_w as f32 / draw_w as f32;
    let scale_y = src_h as f32 / draw_h as f32;
    let mut out = Vec::with_capacity(pixels.len());
    for (i, &pixel) in pixels.iter().enumerate() {
        let x = (i as u32 % src_w) as f32;
        let y = (i as u32 / src_w) as f32;
        let px = (x + 0.5) / scale_x;
        let py = (y + 0.5) / scale_y;
        let dx = if px < radius {
            radius - px
        } else if px > draw_w as f32 - radius {
            px - (draw_w as f32 - radius)
        } else {
            0.0
        };
        let dy = if py < radius {
            radius - py
        } else if py > draw_h as f32 - radius {
            py - (draw_h as f32 - radius)
        } else {
            0.0
        };
        let coverage = if dx > 0.0 && dy > 0.0 {
            (radius + 0.5 - (dx * dx + dy * dy).sqrt()).clamp(0.0, 1.0)
        } else {
            1.0
        };
        let a = ((pixel >> 24) & 0xff) as f32 * coverage;
        out.push((pixel & 0x00ff_ffff) | (((a + 0.5) as u32 & 0xff) << 24));
    }
    ImageData {
        pixels: out,
        width: src_w,
        height: src_h,
    }
}

fn now_received_time() -> String {
    unsafe {
        let mut now = libc::time(std::ptr::null_mut());
        let mut tm: libc::tm = std::mem::zeroed();
        if libc::localtime_r(&mut now, &mut tm).is_null() {
            return "00-00-00".into();
        }
        let mut buf = [0u8; 9];
        let fmt = b"%H-%M-%S\0";
        if libc::strftime(
            buf.as_mut_ptr() as *mut c_char,
            buf.len(),
            fmt.as_ptr() as *const c_char,
            &tm,
        ) == 0
        {
            return "00-00-00".into();
        }
        String::from_utf8_lossy(&buf)
            .trim_end_matches('\0')
            .to_string()
    }
}

const IGNORE_APPS: &[&str] = &[];
const IGNORE_SUMMARIES: &[&str] = &[];
const IGNORE_BODIES: &[&str] = &["You have unseen notifications."];

fn ignored(data: &NotificationData) -> bool {
    let app_match = IGNORE_APPS.iter().any(|s| data.app_name.contains(s));
    let text_match = IGNORE_SUMMARIES.iter().any(|s| data.summary.contains(s))
        || IGNORE_BODIES.iter().any(|s| data.body.contains(s));
    if !IGNORE_APPS.is_empty() && (!IGNORE_SUMMARIES.is_empty() || !IGNORE_BODIES.is_empty()) {
        app_match && text_match
    } else {
        app_match || text_match
    }
}

struct FontBundle {
    specs: Vec<GlFontSpec>,
    height: i32,
    lcd_order: u8,
}

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcPatternGetString(
        pattern: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut *mut c_char,
    ) -> c_int;
    fn FcPatternGetInteger(
        pattern: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut c_int,
    ) -> c_int;
    fn FcPatternGetDouble(
        pattern: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut c_double,
    ) -> c_int;
}

unsafe fn fc_string(pattern: *mut FcPattern, name: &str) -> Option<String> {
    let object = CString::new(name).ok()?;
    let mut value: *mut c_char = ptr::null_mut();
    if unsafe { FcPatternGetString(pattern, object.as_ptr(), 0, &mut value) } == 0
        && !value.is_null()
    {
        Some(
            unsafe { CStr::from_ptr(value) }
                .to_string_lossy()
                .into_owned(),
        )
    } else {
        None
    }
}

unsafe fn fc_int(pattern: *mut FcPattern, name: &str) -> Option<i32> {
    let object = CString::new(name).ok()?;
    let mut value = 0;
    (unsafe { FcPatternGetInteger(pattern, object.as_ptr(), 0, &mut value) } == 0).then_some(value)
}

unsafe fn fc_double(pattern: *mut FcPattern, name: &str) -> Option<f64> {
    let object = CString::new(name).ok()?;
    let mut value = 0.0;
    (unsafe { FcPatternGetDouble(pattern, object.as_ptr(), 0, &mut value) } == 0).then_some(value)
}

fn font_bundle(dpy: *mut xlib::Display, screen: i32, scale: f64) -> Result<FontBundle> {
    let scale = if scale > 0.0 { scale } else { 1.0 };
    let mut lcd_order = match unsafe { xrender::XRenderQuerySubpixelOrder(dpy, screen) } {
        1 => 1,
        2 => 2,
        _ => 0,
    };
    let mut specs = Vec::new();
    let mut height = 0;
    for (i, name) in FONTS.iter().enumerate() {
        let Ok(name) = CString::new(*name) else {
            continue;
        };
        let font: *mut XftFont = unsafe { XftFontOpenName(dpy, screen, name.as_ptr()) };
        if font.is_null() {
            continue;
        }
        let pattern = unsafe { (*font).pattern };
        let unscaled_h = unsafe { (*font).ascent + (*font).descent };
        if i == 0 {
            height = (unscaled_h as f64 * scale).round() as i32;
            if !pattern.is_null() {
                lcd_order = unsafe { fc_int(pattern, "rgba") }
                    .filter(|order| *order == 1 || *order == 2)
                    .map(|order| order as u8)
                    .unwrap_or(lcd_order);
            }
        }
        if let Some(file) = unsafe {
            (!pattern.is_null())
                .then(|| fc_string(pattern, "file"))
                .flatten()
        } {
            let index = if pattern.is_null() {
                0
            } else {
                unsafe { fc_int(pattern, "index") }.unwrap_or(0)
            };
            let size = if pattern.is_null() {
                unscaled_h as f64
            } else {
                unsafe { fc_double(pattern, "pixelsize") }
                    .filter(|size| *size > 0.0)
                    .unwrap_or(unscaled_h as f64)
            };
            specs.push(GlFontSpec {
                file,
                index,
                pixel_size: size * scale,
            });
        }
        unsafe { XftFontClose(dpy, font) };
    }
    if specs.is_empty() {
        return Err("no configured Xft font could be resolved for notification GL text".into());
    }
    if height <= 0 {
        height = specs[0].pixel_size.ceil() as i32;
    }
    Ok(FontBundle {
        specs,
        height,
        lcd_order,
    })
}

// Field order is drop order: glyph textures need a current context, so both
// fonts and the readback surface are dropped before the pbuffer that owns it.
struct GlState {
    font: GlFont,
    time_font: GlFont,
    surface: GlSurface,
    pbuffer: GlPbuffer,
}

struct FrameSurface {
    dpy: *mut xlib::Display,
    visual: *mut xlib::Visual,
    bg_pixmap: xlib::Pixmap,
    bg_picture: xrender::Picture,
    mask_pixmap: xlib::Pixmap,
    mask_picture: xrender::Picture,
    frame_pixmap: xlib::Pixmap,
    frame_picture: xrender::Picture,
    width: u32,
    height: u32,
}

impl FrameSurface {
    fn new() -> FrameSurface {
        FrameSurface {
            dpy: ptr::null_mut(),
            visual: ptr::null_mut(),
            bg_pixmap: 0,
            bg_picture: 0,
            mask_pixmap: 0,
            mask_picture: 0,
            frame_pixmap: 0,
            frame_picture: 0,
            width: 0,
            height: 0,
        }
    }

    fn resize(
        &mut self,
        dpy: *mut xlib::Display,
        visual: *mut xlib::Visual,
        w: u32,
        h: u32,
    ) -> Result<()> {
        if self.frame_picture != 0 && self.dpy == dpy && (self.width, self.height) == (w, h) {
            self.visual = visual;
            return Ok(());
        }
        self.destroy();
        self.dpy = dpy;
        self.visual = visual;
        unsafe {
            let root = xlib::XDefaultRootWindow(dpy);
            let argb = xrender::XRenderFindStandardFormat(dpy, xrender::PictStandardARGB32);
            let a8 = xrender::XRenderFindStandardFormat(dpy, xrender::PictStandardA8);
            if argb.is_null() || a8.is_null() {
                return Err("XRender has no ARGB32/A8 picture format".into());
            }
            self.bg_pixmap = xlib::XCreatePixmap(dpy, root, w, h, 32);
            self.frame_pixmap = xlib::XCreatePixmap(dpy, root, w, h, 32);
            self.mask_pixmap = xlib::XCreatePixmap(dpy, root, w, h, 8);
            if self.bg_pixmap == 0 || self.frame_pixmap == 0 || self.mask_pixmap == 0 {
                return Err("cannot create notification frame pixmaps".into());
            }
            self.bg_picture =
                xrender::XRenderCreatePicture(dpy, self.bg_pixmap, argb, 0, ptr::null());
            self.frame_picture =
                xrender::XRenderCreatePicture(dpy, self.frame_pixmap, argb, 0, ptr::null());
            self.mask_picture =
                xrender::XRenderCreatePicture(dpy, self.mask_pixmap, a8, 0, ptr::null());
            if self.bg_picture == 0 || self.frame_picture == 0 || self.mask_picture == 0 {
                return Err("cannot create notification frame pictures".into());
            }
        }
        self.width = w;
        self.height = h;
        self.paint_history_background();
        Ok(())
    }

    fn paint_history_background(&self) {
        unsafe {
            let color = xrender::XRenderColor {
                red: POPUP_BACKGROUND.0,
                green: POPUP_BACKGROUND.1,
                blue: POPUP_BACKGROUND.2,
                alpha: POPUP_BACKGROUND.3,
            };
            xrender::XRenderFillRectangle(
                self.dpy,
                xrender::PictOpSrc,
                self.bg_picture,
                &color,
                0,
                0,
                self.width,
                self.height,
            );
            let gc = xlib::XCreateGC(self.dpy, self.mask_pixmap, 0, ptr::null_mut());
            if !gc.is_null() {
                for y in 0..self.height {
                    let a = vertical_alpha(y, self.height) as u16 * 257;
                    let mask_color = xrender::XRenderColor {
                        red: 0,
                        green: 0,
                        blue: 0,
                        alpha: a,
                    };
                    xrender::XRenderFillRectangle(
                        self.dpy,
                        xrender::PictOpSrc,
                        self.mask_picture,
                        &mask_color,
                        0,
                        y as i32,
                        self.width,
                        1,
                    );
                }
                xlib::XFreeGC(self.dpy, gc);
            }
        }
    }

    /// dwm's generic popup path (dwm.c 9412-9420): the transparent GL
    /// foreground is composited over the 1x1 tiled background through the
    /// vertical opacity mask. The result is cached in the frame picture so the
    /// presentation step only has to copy it to the center window.
    fn composite_popup(&self, foreground: xrender::Picture) {
        unsafe {
            let clear = xrender::XRenderColor {
                red: 0,
                green: 0,
                blue: 0,
                alpha: 0,
            };
            xrender::XRenderFillRectangle(
                self.dpy,
                xrender::PictOpSrc,
                self.frame_picture,
                &clear,
                0,
                0,
                self.width,
                self.height,
            );
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpSrc,
                self.bg_picture,
                self.mask_picture,
                self.frame_picture,
                0,
                0,
                0,
                0,
                0,
                0,
                self.width,
                self.height,
            );
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpOver,
                foreground,
                0,
                self.frame_picture,
                0,
                0,
                0,
                0,
                0,
                0,
                self.width,
                self.height,
            );
        }
    }

    fn composite_history(
        &self,
        foreground: xrender::Picture,
        scroll: i32,
        viewport_h: u32,
        foreground_h: u32,
    ) {
        unsafe {
            let clear = xrender::XRenderColor {
                red: 0,
                green: 0,
                blue: 0,
                alpha: 0,
            };
            xrender::XRenderFillRectangle(
                self.dpy,
                xrender::PictOpSrc,
                self.frame_picture,
                &clear,
                0,
                0,
                self.width,
                self.height,
            );
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpSrc,
                self.bg_picture,
                self.mask_picture,
                self.frame_picture,
                0,
                0,
                0,
                0,
                0,
                0,
                self.width,
                self.height,
            );
            let pad = NOTIFY_PADDING as u32;
            let visible = viewport_h
                .saturating_sub(2 * pad)
                .min(foreground_h.saturating_sub(pad.saturating_add_signed(scroll)));
            if visible == 0 {
                return;
            }
            let source_y = pad.saturating_add_signed(scroll);
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpOver,
                foreground,
                0,
                self.frame_picture,
                0,
                source_y as i32,
                0,
                0,
                0,
                pad as i32,
                self.width,
                visible,
            );
        }
    }

    fn destroy(&mut self) {
        unsafe {
            if self.bg_picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.bg_picture);
            }
            if self.frame_picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.frame_picture);
            }
            if self.mask_picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.mask_picture);
            }
            if self.bg_pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.bg_pixmap);
            }
            if self.frame_pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.frame_pixmap);
            }
            if self.mask_pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.mask_pixmap);
            }
        }
        self.bg_pixmap = 0;
        self.bg_picture = 0;
        self.mask_pixmap = 0;
        self.mask_picture = 0;
        self.frame_pixmap = 0;
        self.frame_picture = 0;
        self.width = 0;
        self.height = 0;
    }
}

impl Drop for FrameSurface {
    fn drop(&mut self) {
        self.destroy();
    }
}

/// dwm's 12-stop vertical opacity ramp: opaque at the top, 50% at the bottom.
fn vertical_alpha(y: u32, h: u32) -> u8 {
    const STOPS: [f64; 12] = [0.0, 0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0];
    const ALPHA: [u8; 12] = [255, 255, 254, 251, 246, 238, 228, 215, 200, 182, 162, 128];
    let position = if h > 1 {
        y as f64 / (h - 1) as f64
    } else {
        0.0
    };
    for i in 1..STOPS.len() {
        if position <= STOPS[i] {
            let span = STOPS[i] - STOPS[i - 1];
            let fraction = if span > 0.0 {
                (position - STOPS[i - 1]) / span
            } else {
                0.0
            };
            return (ALPHA[i - 1] as f64 + (ALPHA[i] as f64 - ALPHA[i - 1] as f64) * fraction)
                .round() as u8;
        }
    }
    ALPHA[ALPHA.len() - 1]
}

pub struct NotificationManager {
    rx: Option<Receiver<Event>>,
    dbus: Option<Arc<Connection>>,
    finder_active: bool,
    queue: VecDeque<Entry>,
    current: Option<Entry>,
    history: VecDeque<Entry>,
    notify_width: i32,
    notify_height: i32,
    transition_pending: bool,
    transition_started: Instant,
    history_open: bool,
    clock_hovered: bool,
    hover_grace_until: Option<Instant>,
    hover_grace_pos: Option<(i32, i32)>,
    hovered: bool,
    hover_started: Instant,
    hover: i32,
    history_scroll: i32,
    history_scroll_target: i32,
    history_scroll_started: Instant,
    history_hover_entry: i32,
    history_hover_action: i32,
    history_input: Option<u32>,
    input_focus: bool,
    gl: Option<GlState>,
    frame: FrameSurface,
    frame_key: u64,
    frame_valid: bool,
    presentation: Option<(u32, u32, i32, i32)>,
}

impl NotificationManager {
    pub fn new(handle: Option<ServiceHandle>) -> NotificationManager {
        let (rx, dbus) = match handle {
            Some(handle) => (Some(handle.rx), Some(handle.connection)),
            None => (None, None),
        };
        NotificationManager {
            rx,
            dbus,
            finder_active: false,
            queue: VecDeque::new(),
            current: None,
            history: VecDeque::new(),
            notify_width: 0,
            notify_height: 0,
            transition_pending: false,
            transition_started: Instant::now(),
            history_open: false,
            clock_hovered: false,
            hover_grace_until: None,
            hover_grace_pos: None,
            hovered: false,
            hover_started: Instant::now(),
            hover: -1,
            history_scroll: 0,
            history_scroll_target: 0,
            history_scroll_started: Instant::now(),
            history_hover_entry: -1,
            history_hover_action: -1,
            history_input: None,
            input_focus: false,
            gl: None,
            frame: FrameSurface::new(),
            frame_key: 0,
            frame_valid: false,
            presentation: None,
        }
    }

    pub fn is_popup_active(&self) -> bool {
        self.current.is_some()
    }

    pub fn is_history_active(&self) -> bool {
        self.history_input.is_some() || self.history_popup_active()
    }

    fn history_popup_active(&self) -> bool {
        self.current.is_none() && !self.transition_pending && self.history_open
    }

    pub fn is_active(&self) -> bool {
        self.is_popup_active() || self.is_history_active() || self.transition_pending
    }

    /// Finder owns the center window while it is open; dwm refuses to reveal
    /// notification history underneath it.
    pub fn set_finder_active(&mut self, active: bool) {
        self.finder_active = active;
    }

    /// Whether the shared center window belongs to the notification center.
    /// The 500 ms gap between notifications is deliberately excluded so the
    /// normal clock returns while the next popup is being promoted.
    pub fn is_center_active(&self) -> bool {
        self.is_popup_active() || self.is_history_active()
    }

    pub fn has_input_focus(&self) -> bool {
        self.input_focus
    }

    pub fn center_class(&self) -> CenterClass {
        if self.is_popup_active() {
            CenterClass::Notification
        } else if self.is_history_active() {
            CenterClass::History
        } else {
            CenterClass::Dwm
        }
    }

    pub fn popup_size(&self, bh: i32) -> (u32, u32) {
        (
            self.notify_width.max(1) as u32,
            self.notify_height.max(bh).max(1) as u32,
        )
    }

    pub fn next_tick(&self, now: Instant) -> Instant {
        let mut next = now + Duration::from_millis(100);
        if self.transition_pending {
            next = next.min(self.transition_started + NOTIFY_TRANSITION);
        }
        if self.current.is_some() && !self.hovered {
            if let Some(current) = &self.current {
                let deadline = current.shown_at + NOTIFY_TIMEOUT;
                if deadline > now {
                    next = next.min(deadline);
                }
            }
        }
        if self.history_scroll != self.history_scroll_target {
            next = next.min(self.history_scroll_started + NOTIFY_HISTORY_FPS);
        }
        next
    }

    pub fn prepare(
        &mut self,
        dpy: *mut xlib::Display,
        screen: i32,
        visual: *mut xlib::Visual,
    ) -> Result<()> {
        if self.gl.is_some() || visual.is_null() || self.dbus.is_none() {
            return Ok(());
        }
        let pbuffer = GlPbuffer::new(dpy, screen, GL_PBUFFER_MAX_WIDTH, GL_PBUFFER_MAX_HEIGHT)?;
        let main = font_bundle(dpy, screen, 1.0)?;
        let time = font_bundle(dpy, screen, NOTIFY_HISTORY_TIME_SCALE)?;
        let font = GlFont::new(&main.specs, main.height, main.lcd_order)?;
        let time_font = GlFont::new(&time.specs, time.height, time.lcd_order)?;
        let surface = GlSurface::new(dpy, visual, 1, 1)?;
        self.gl = Some(GlState {
            font,
            time_font,
            surface,
            pbuffer,
        });
        self.frame_valid = false;
        Ok(())
    }

    /// Drains D-Bus events and advances all notification timers. Returns true
    /// when the bar geometry or pixels must be refreshed.
    pub fn poll(&mut self, fullscreen: bool, bar_h: i32, now: Instant) -> Result<bool> {
        let mut dirty = false;
        let events: Vec<Event> = self
            .rx
            .as_ref()
            .map(|rx| {
                let mut out = Vec::new();
                while let Ok(event) = rx.try_recv() {
                    out.push(event);
                }
                out
            })
            .unwrap_or_default();
        for event in events {
            match event {
                Event::New(data) => dirty |= self.enqueue(data, fullscreen, bar_h),
                Event::Close(id) => dirty |= self.close(id, bar_h),
            }
        }
        dirty |= self.tick(bar_h, now);
        Ok(dirty)
    }

    /// dwm's replacement path keeps the original id, received time, action
    /// state and timer; only the notification contents are replaced.
    fn replace_data(entry: &mut Entry, mut data: NotificationData) {
        let id = entry.data.id;
        let received_time = entry.data.received_time.clone();
        data.id = id;
        data.received_time = received_time;
        entry.data = data;
    }

    fn enqueue(&mut self, data: NotificationData, fullscreen: bool, bar_h: i32) -> bool {
        if ignored(&data) {
            return false;
        }
        if let Some(entry) = self.history.iter_mut().find(|e| e.data.id == data.id) {
            Self::replace_data(entry, data);
            self.invalidate_frame();
            if self.is_history_active() {
                self.update_layout(bar_h);
            }
            return false;
        }
        if self.history_open && self.current.is_none() {
            self.history.push_front(Entry::new(data));
            while self.history.len() > NOTIFY_HISTORY_MAX {
                self.history.pop_back();
            }
            self.invalidate_frame();
            self.update_layout(bar_h);
            return true;
        }
        if let Some(current) = self.current.as_mut() {
            if current.data.id == data.id {
                Self::replace_data(current, data);
                current.shown_at = Instant::now();
                self.input_focus = false;
                self.hovered = false;
                self.hover = -1;
                self.invalidate_frame();
                self.update_layout(bar_h);
                return true;
            }
        }
        if let Some(entry) = self.queue.iter_mut().find(|e| e.data.id == data.id) {
            Self::replace_data(entry, data);
            return false;
        }
        if fullscreen {
            self.history.push_front(Entry::new(data));
            while self.history.len() > NOTIFY_HISTORY_MAX {
                self.history.pop_back();
            }
            self.invalidate_frame();
            if self.is_history_active() {
                self.update_layout(bar_h);
            }
            return false;
        }
        if self.queue.len() >= NOTIFY_MAX {
            return false;
        }
        self.queue.push_back(Entry::new(data));
        self.promote(bar_h);
        true
    }

    fn promote(&mut self, bar_h: i32) {
        if self.current.is_some() || self.transition_pending || self.queue.is_empty() {
            return;
        }
        let mut entry = self.queue.pop_front().expect("queue was checked");
        entry.shown_at = Instant::now();
        self.current = Some(entry);
        self.input_focus = false;
        self.hovered = false;
        self.hover = -1;
        self.invalidate_frame();
        self.update_layout(bar_h);
    }

    fn close(&mut self, id: u32, bar_h: i32) -> bool {
        if self.current.as_ref().is_some_and(|n| n.data.id == id) {
            if let (Some(dbus), Some(current)) = (&self.dbus, &self.current) {
                emit_closed(dbus, current.data.id, 3);
            }
            self.advance(bar_h);
            return true;
        }
        let before = self.queue.len();
        self.queue.retain(|n| n.data.id != id);
        before != self.queue.len()
    }

    fn tick(&mut self, bar_h: i32, now: Instant) -> bool {
        let mut dirty = false;
        if self.transition_pending
            && now.duration_since(self.transition_started) >= NOTIFY_TRANSITION
        {
            self.transition_pending = false;
            if !self.queue.is_empty() {
                self.promote(bar_h);
                dirty = true;
            } else if self.clock_hovered && !self.history.is_empty() && !self.history_open {
                self.history_show(bar_h);
                dirty = true;
            }
        }
        if let Some(current) = &self.current {
            if !self.hovered && now.duration_since(current.shown_at) >= NOTIFY_TIMEOUT {
                self.advance(bar_h);
                dirty = true;
            }
        }
        if self.history_scroll_tick(now) {
            dirty = true;
        }
        dirty
    }

    fn advance(&mut self, bar_h: i32) {
        let Some(old) = self.current.take() else {
            return;
        };
        self.input_focus = false;
        self.hovered = false;
        self.hover = -1;
        self.add_history(old);
        self.notify_width = 0;
        self.notify_height = 0;
        self.transition_pending = true;
        self.transition_started = Instant::now();
        self.invalidate_frame();
        if self.history_open && bar_h > 0 {
            self.update_layout(bar_h);
        }
    }

    fn clear_queue(&mut self, bar_h: i32) {
        if let Some(current) = self.current.take() {
            self.add_history(current);
        }
        for entry in std::mem::take(&mut self.queue) {
            self.add_history(entry);
        }
        self.input_focus = false;
        self.hovered = false;
        self.hover = -1;
        self.notify_width = 0;
        self.notify_height = 0;
        self.transition_pending = true;
        self.transition_started = Instant::now();
        self.invalidate_frame();
        if self.history_open && bar_h > 0 {
            self.update_layout(bar_h);
        }
    }

    fn add_history(&mut self, entry: Entry) {
        if self.history.iter().any(|e| e.data.id == entry.data.id) {
            return;
        }
        self.history.push_front(entry);
        while self.history.len() > NOTIFY_HISTORY_MAX {
            self.history.pop_back();
        }
    }

    pub(crate) fn invalidate_frame(&mut self) {
        self.frame_valid = false;
    }

    fn history_show(&mut self, bar_h: i32) {
        if self.history.is_empty()
            || self.current.is_some()
            || self.transition_pending
            || self.finder_active
        {
            return;
        }
        if self
            .hover_grace_until
            .is_some_and(|until| Instant::now() < until)
        {
            return;
        }
        self.history_open = true;
        self.input_focus = false;
        self.hovered = false;
        self.hover = -1;
        self.history_hover_entry = -1;
        self.history_hover_action = -1;
        self.history_scroll = 0;
        self.history_scroll_target = 0;
        self.invalidate_frame();
        self.update_layout(bar_h);
    }

    fn history_hide(&mut self, bar_h: i32) {
        if !self.history_open {
            return;
        }
        self.history_open = false;
        self.input_focus = false;
        self.history_input = None;
        self.hovered = false;
        self.hover = -1;
        self.history_hover_entry = -1;
        self.history_hover_action = -1;
        self.invalidate_frame();
        self.update_layout(bar_h);
    }

    fn set_hovered(&mut self, hovered: bool, bar_h: i32) {
        if self.hovered == hovered {
            return;
        }
        let now = Instant::now();
        if !hovered {
            if let Some(current) = self.current.as_mut() {
                current.shown_at += now.duration_since(self.hover_started);
            }
        } else {
            self.hover_started = now;
        }
        self.hovered = hovered;
        self.invalidate_frame();
        self.update_layout(bar_h);
    }

    pub fn arm_hover_grace(&mut self, x: i32, y: i32) {
        self.clock_hovered = false;
        self.hovered = false;
        self.hover = -1;
        self.hover_grace_until = Some(Instant::now() + NOTIFY_HOVER_GRACE);
        self.hover_grace_pos = Some((x, y));
    }

    fn hover_suppressed(&mut self, x: i32, y: i32) -> bool {
        let Some(until) = self.hover_grace_until else {
            return false;
        };
        if Instant::now() >= until {
            self.hover_grace_until = None;
            self.hover_grace_pos = None;
            return false;
        }
        if let Some((gx, gy)) = self.hover_grace_pos {
            if (x - gx).abs() > 2 || (y - gy).abs() > 2 {
                self.hover_grace_until = None;
                self.hover_grace_pos = None;
                return false;
            }
        }
        true
    }

    pub fn clock_hit(&self, x: i32, width: i32, window_width: i32) -> bool {
        let width = if width <= 0 || width >= window_width {
            window_width
        } else {
            width
        };
        if width <= 0 {
            return true;
        }
        let left = (window_width - width) / 2;
        x >= left && x < left + width
    }

    pub fn enter(&mut self, x: i32, y: i32, root_x: i32, root_y: i32, bar_h: i32) -> bool {
        if self.hover_suppressed(root_x, root_y) {
            return false;
        }
        self.clock_hovered = true;
        if self.current.is_some() {
            self.enter_popup(x, y, bar_h);
            return true;
        }
        if self.is_history_active() {
            self.history_motion(x, y, bar_h);
            return false;
        }
        if !self.transition_pending && !self.history.is_empty() {
            self.history_show(bar_h);
            self.history_motion(x, y, bar_h);
            return true;
        }
        false
    }

    pub fn leave(&mut self, bar_h: i32) -> bool {
        let was_active = self.is_active();
        self.clock_hovered = false;
        self.set_hovered(false, bar_h);
        self.history_hide(bar_h);
        self.hover = -1;
        was_active || self.is_active()
    }

    fn enter_popup(&mut self, x: i32, y: i32, bar_h: i32) {
        self.set_hovered(
            x >= 0 && x < self.notify_width && y >= 0 && y < self.notify_height,
            bar_h,
        );
        self.popup_motion(x, y, bar_h);
    }

    pub fn motion(&mut self, x: i32, y: i32, root_x: i32, root_y: i32, bar_h: i32) -> bool {
        if self.hover_suppressed(root_x, root_y) {
            return false;
        }
        // The WM already applied the fixed clock-sized hit test before calling
        // this. An earlier EnterNotify may have landed in the animated
        // visualizer padding and been ignored, leaving `clock_hovered` false;
        // moving into the clock region must still open history like dwm's
        // motionnotify(), which sets notify_clock_hovered unconditionally here.
        self.clock_hovered = true;
        if self.current.is_some() {
            self.popup_motion(x, y, bar_h);
        } else if self.is_history_active() {
            self.history_motion(x, y, bar_h);
        } else if !self.transition_pending && !self.history.is_empty() {
            self.history_show(bar_h);
            return true;
        }
        false
    }

    fn popup_motion(&mut self, x: i32, y: i32, bar_h: i32) {
        let inside = x >= 0 && x < self.notify_width && y >= 0 && y < self.notify_height;
        self.set_hovered(inside, bar_h);
        let mut hover = -1;
        if inside && self.hovered {
            if let Some(n) = &self.current {
                if n.data.input_enabled
                    && x >= NOTIFY_PADDING
                    && x < NOTIFY_PADDING + (self.notify_width - 2 * NOTIFY_PADDING)
                    && y >= n.input_y
                    && y < n.input_y + NOTIFY_INPUT_ROW_H
                {
                    hover = -2;
                } else if self.hovered && n.data.actions.len() >= 2 {
                    for i in 0..n.action_x.len().min(16) {
                        if x >= n.action_x[i]
                            && x < n.action_x[i] + n.action_w[i]
                            && y >= n.action_y
                            && y < n.action_y + NOTIFY_BUTTON_H
                        {
                            hover = i as i32;
                            break;
                        }
                    }
                }
            }
        }
        if hover != self.hover {
            self.hover = hover;
            self.invalidate_frame();
        }
    }

    fn history_motion(&mut self, x: i32, y: i32, bar_h: i32) {
        if !self.is_history_active() || self.history.is_empty() {
            return;
        }
        let pad = NOTIFY_PADDING;
        let last = self.history.len().saturating_sub(1);
        let mut entry = -1;
        let mut action = -1;
        let mut cursor_y = pad - self.history_scroll;
        for (i, n) in self.history.iter().enumerate() {
            let entry_h = self.history_entry_height(n, bar_h, i < last);
            let entry_content_h = self.history_entry_content_height(n, bar_h);
            let content_h = self.history_content_height(n, bar_h);
            if y >= cursor_y
                && y < cursor_y + entry_content_h
                && y >= pad
                && y < self.notify_height - pad
            {
                entry = i as i32;
                if n.data.actions.len() >= 4 && x >= pad && x < pad + self.notify_width - 2 * pad {
                    // dwm highlights the action cell through the entry's
                    // trailing gap, not just the 24px button row.
                    let local_y = y - cursor_y;
                    let action_start = content_h
                        + if n.data.input_enabled {
                            NOTIFY_INPUT_ROW_H
                        } else {
                            0
                        };
                    if local_y >= action_start && local_y < entry_h {
                        let actions = (n.data.actions.len() / 2).min(16);
                        let content_w = self.notify_width - 2 * pad;
                        let cell = content_w / actions as i32;
                        action = ((x - pad) / cell.max(1)).clamp(0, actions as i32 - 1);
                    }
                }
                break;
            }
            cursor_y += entry_h;
        }
        if entry != self.history_hover_entry || action != self.history_hover_action {
            self.history_hover_entry = entry;
            self.history_hover_action = action;
            self.invalidate_frame();
        }
    }

    pub fn button(&mut self, button: u8, x: i32, y: i32, bar_h: i32) -> bool {
        if self.current.is_some() {
            self.popup_button(button, x, y, bar_h)
        } else if self.is_history_active() {
            self.history_button(button, x, y, bar_h)
        } else {
            false
        }
    }

    fn popup_button(&mut self, button: u8, x: i32, y: i32, bar_h: i32) -> bool {
        let (input, clicked_action, default_action) = {
            let Some(n) = self.current.as_ref() else {
                return false;
            };
            let input = n.data.input_enabled
                && x >= NOTIFY_PADDING
                && x < NOTIFY_PADDING + (self.notify_width - 2 * NOTIFY_PADDING)
                && y >= n.input_y
                && y < n.input_y + NOTIFY_INPUT_ROW_H;
            if input {
                (true, None, None)
            } else {
                // dwm recomputes the action hitboxes from the current layout on
                // every click; the hover state alone is not authoritative.
                let clicked = n
                    .action_x
                    .iter()
                    .enumerate()
                    .find_map(|(i, &ax)| {
                        let aw = n.action_w.get(i).copied().unwrap_or(0);
                        let in_x = aw > 0 && x >= ax && x < ax + aw;
                        let in_y = y >= n.action_y && y < n.action_y + NOTIFY_BUTTON_H;
                        (in_x && in_y).then_some(i)
                    })
                    .filter(|i| i * 2 + 1 < n.data.actions.len())
                    .map(|i| n.data.actions[i * 2].clone());
                let default = (n.data.actions.len() >= 2).then(|| n.data.actions[0].clone());
                (false, clicked, default)
            }
        };
        if input {
            // Non-primary buttons leave the current focus alone, like dwm.
            if button == 1 && !self.input_focus {
                self.input_focus = true;
                self.invalidate_frame();
            }
            return true;
        }
        if let Some(action) = clicked_action {
            if button == 1 {
                self.emit_action_and_close(&action);
                self.advance(bar_h);
            }
            return true;
        }
        match button {
            1 => {
                if let Some(action) = default_action {
                    self.emit_action_and_close(&action);
                    self.advance(bar_h);
                }
            }
            3 => self.advance(bar_h),
            2 => self.clear_queue(bar_h),
            _ => return false,
        }
        true
    }

    fn history_button(&mut self, button: u8, x: i32, y: i32, bar_h: i32) -> bool {
        if button == 4 || button == 5 {
            let delta = if button == 4 {
                -HISTORY_SCROLL_STEP
            } else {
                HISTORY_SCROLL_STEP
            };
            let base = if self.history_scroll != self.history_scroll_target {
                self.history_scroll_target
            } else {
                self.history_scroll
            };
            let max = self.max_scroll(bar_h);
            self.history_scroll_target = (base + delta).clamp(0, max);
            if self.history_scroll == self.history_scroll_target {
                self.history_scroll = self.history_scroll_target;
            } else if self.history_scroll == base {
                self.history_scroll_started = Instant::now();
            }
            return true;
        }
        if button != 1 {
            return false;
        }
        let pad = NOTIFY_PADDING;
        let content_w = self.notify_width - 2 * pad;
        if x < pad || x >= pad + content_w || y < pad || y >= self.notify_height - pad {
            return true;
        }
        enum Click {
            None,
            Input(u32),
            Action(usize, String),
            Default(usize, String),
        }
        let mut click = Click::None;
        let last = self.history.len().saturating_sub(1);
        let mut cursor_y = pad - self.history_scroll;
        for (i, n) in self.history.iter().enumerate() {
            let entry_h = self.history_entry_height(n, bar_h, i < last);
            if y >= cursor_y && y < cursor_y + entry_h {
                let local_y = y - cursor_y;
                let content_h = self.history_content_height(n, bar_h);
                let entry_content_h = self.history_entry_content_height(n, bar_h);
                if local_y >= entry_content_h {
                    return true;
                }
                if n.data.input_enabled
                    && local_y >= content_h
                    && local_y < content_h + NOTIFY_INPUT_ROW_H
                {
                    click = Click::Input(n.data.id);
                    break;
                }
                let controls_y = content_h
                    + if n.data.input_enabled {
                        NOTIFY_INPUT_ROW_H
                    } else {
                        0
                    };
                let actions = (n.data.actions.len() / 2).min(16);
                if actions > 0 && local_y >= controls_y && local_y < controls_y + NOTIFY_BUTTON_H {
                    let cell = content_w / actions as i32;
                    let index = ((x - pad) / cell.max(1)).clamp(0, actions as i32 - 1) as usize;
                    if index * 2 + 1 < n.data.actions.len() {
                        click = Click::Action(i, n.data.actions[index * 2].clone());
                    }
                    break;
                }
                if n.data.actions.len() >= 2 {
                    click = Click::Default(i, n.data.actions[0].clone());
                }
                break;
            }
            cursor_y += entry_h;
        }
        match click {
            Click::Input(id) => {
                self.input_focus = true;
                self.history_input = Some(id);
                self.invalidate_frame();
            }
            Click::Action(i, action) => self.emit_action_and_history(i, &action, bar_h),
            Click::Default(i, action) => self.emit_action_and_history(i, &action, bar_h),
            Click::None => {}
        }
        true
    }

    fn emit_action_and_close(&mut self, action: &str) {
        let id = self.current.as_ref().map(|n| n.data.id);
        if let (Some(dbus), Some(id)) = (&self.dbus, id) {
            emit_action(dbus, id, action);
            emit_closed(dbus, id, 2);
        }
        if let Some(current) = self.current.as_mut() {
            current.action_used = true;
            clear_controls(&mut current.data);
        }
    }

    fn emit_action_and_history(&mut self, index: usize, action: &str, bar_h: i32) {
        let Some(n) = self.history.get_mut(index) else {
            return;
        };
        if let Some(dbus) = &self.dbus {
            emit_action(dbus, n.data.id, action);
            emit_closed(dbus, n.data.id, 2);
        }
        n.action_used = true;
        clear_controls(&mut n.data);
        if self.history_input == Some(n.data.id) {
            self.input_focus = false;
            self.history_input = None;
        }
        self.invalidate_frame();
        self.update_layout(bar_h);
    }

    /// Submits the focused input row. An empty `x-andwm-input-action` still
    /// consumes the controls and marks the notification used, but emits no
    /// `InputSubmitted` signal, matching dwm's `notification_emit_input()`.
    fn emit_input(&mut self) -> bool {
        let (id, action, text, is_current) = if let Some(n) = self.current.as_ref() {
            (
                n.data.id,
                n.data.input_action.clone(),
                n.data.input_text.clone(),
                true,
            )
        } else if let Some(id) = self.history_input {
            let Some(n) = self.history.iter().find(|n| n.data.id == id) else {
                return false;
            };
            (
                id,
                n.data.input_action.clone(),
                n.data.input_text.clone(),
                false,
            )
        } else {
            return false;
        };
        if !action.is_empty() {
            if let Some(dbus) = &self.dbus {
                emit_input(dbus, id, &action, &text);
            }
        }
        if is_current {
            if let Some(dbus) = &self.dbus {
                emit_closed(dbus, id, 2);
            }
            if let Some(n) = self.current.as_mut() {
                n.action_used = true;
                clear_controls(&mut n.data);
            }
        } else if let Some(n) = self.history.iter_mut().find(|n| n.data.id == id) {
            n.action_used = true;
            clear_controls(&mut n.data);
        }
        true
    }

    /// Handles keys while the input row owns focus. Returns true when the key
    /// was consumed; the caller must not run ordinary WM bindings then.
    pub fn keypress(&mut self, sym: u32, text: &str, bar_h: i32) -> bool {
        if !self.input_focus {
            return false;
        }
        match sym {
            XK_Escape => {
                self.input_focus = false;
                if self.current.is_some() {
                    self.escape_popup_input(bar_h);
                } else {
                    self.clear_focused_history_controls();
                    self.history_input = None;
                    self.history_hide(bar_h);
                }
                true
            }
            XK_Return | XK_KP_Enter => {
                self.input_focus = false;
                if self.emit_input() {
                    if self.current.is_some() {
                        self.advance(bar_h);
                    } else {
                        self.history_input = None;
                        self.invalidate_frame();
                        self.update_layout(bar_h);
                    }
                }
                true
            }
            XK_BackSpace => {
                let entry = self.focused_entry_mut();
                if let Some(n) = entry {
                    if let Some((index, _)) = n.data.input_text.char_indices().rev().next() {
                        n.data.input_text.truncate(index);
                        self.invalidate_frame();
                        self.update_layout(bar_h);
                    }
                }
                true
            }
            _ => {
                if !text.is_empty() {
                    let entry = self.focused_entry_mut();
                    if let Some(n) = entry {
                        if n.data.input_text.len() < 4095 {
                            n.data.input_text.push_str(text);
                            self.invalidate_frame();
                            self.update_layout(bar_h);
                        }
                    }
                }
                true
            }
        }
    }

    fn focused_entry_mut(&mut self) -> Option<&mut Entry> {
        if let Some(current) = self.current.as_mut() {
            return Some(current);
        }
        let id = self.history_input?;
        self.history.iter_mut().find(|n| n.data.id == id)
    }

    fn escape_popup_input(&mut self, bar_h: i32) {
        let id = self.current.as_ref().map(|n| n.data.id);
        if let (Some(dbus), Some(id)) = (&self.dbus, id) {
            emit_closed(dbus, id, 2);
        }
        if let Some(current) = self.current.as_mut() {
            clear_controls(&mut current.data);
        }
        self.advance(bar_h);
    }

    fn clear_focused_history_controls(&mut self) {
        let Some(id) = self.history_input else {
            return;
        };
        if let Some(n) = self.history.iter_mut().find(|n| n.data.id == id) {
            clear_controls(&mut n.data);
        }
    }

    pub fn escape(&mut self, bar_h: i32) -> bool {
        if self.input_focus {
            return false;
        }
        if self.is_history_active() {
            self.history_hide(bar_h);
            return true;
        }
        false
    }

    pub fn clear_for_fullscreen(&mut self, bar_h: i32) {
        self.clear_queue(bar_h);
        self.transition_pending = false;
    }

    fn history_scroll_tick(&mut self, now: Instant) -> bool {
        if self.history_scroll == self.history_scroll_target {
            return false;
        }
        if now.duration_since(self.history_scroll_started) < NOTIFY_HISTORY_FPS {
            return false;
        }
        let elapsed = now
            .duration_since(self.history_scroll_started)
            .as_secs_f64();
        let delta = self.history_scroll_target - self.history_scroll;
        let fraction = 1.0 - (-elapsed / HISTORY_SCROLL_TIME).exp();
        let mut step = (delta as f64 * fraction).round() as i32;
        if step == 0 {
            step = if delta > 0 { 1 } else { -1 };
        }
        if step.abs() >= delta.abs() {
            self.history_scroll = self.history_scroll_target;
        } else {
            self.history_scroll += step;
        }
        self.history_scroll_started = now;
        true
    }

    fn max_scroll(&self, bar_h: i32) -> i32 {
        let content = self.history_entries_height(bar_h);
        let viewport = self.notify_height - 2 * NOTIFY_PADDING;
        (content - viewport).max(0)
    }

    fn layout_metrics(&self) -> (i32, i32, i32) {
        let gl = self
            .gl
            .as_ref()
            .expect("notification GL state is initialized");
        let line_h = gl.font.height.max(1);
        let body_line_h = (gl.font.pixel_size.ceil() as i32 + NOTIFY_BODY_LINE_GAP).max(1);
        (line_h, body_line_h, gl.font.ascender())
    }

    fn image_display_size(&self, image: &ImageData) -> (i32, i32) {
        // dwm first fits the source into 260x60, then caps the drawn width at
        // 100 while keeping the aspect ratio of that fitted size.
        let (mut w, mut h) = fit_size(
            image.width,
            image.height,
            (NOTIFY_MAX_W - 40) as u32,
            NOTIFY_IMAGE_MAX_H as u32,
        );
        if w > NOTIFY_IMAGE_MAX_W as u32 {
            let fitted_w = w;
            w = NOTIFY_IMAGE_MAX_W as u32;
            h = ((h as u64 * w as u64) / fitted_w as u64).max(1) as u32;
        }
        (w as i32, h as i32)
    }

    /// dwm's `notification_text_width()`: the widest line, not the width of
    /// the whole string with embedded newlines.
    fn text_width(&self, text: &str) -> i32 {
        let Some(gl) = &self.gl else {
            return 0;
        };
        text.split('\n')
            .map(|line| unsafe_font_width(&gl.font, line) as i32)
            .max()
            .unwrap_or(0)
    }

    fn time_text_width(&self, text: &str) -> i32 {
        self.gl
            .as_ref()
            .map(|gl| unsafe_font_width(&gl.time_font, text) as i32)
            .unwrap_or(0)
    }

    fn wrap_lines(&self, text: &str, width: i32, max_lines: usize) -> Vec<String> {
        if self.gl.is_none() || text.is_empty() || width <= 0 || max_lines == 0 {
            return Vec::new();
        }
        let font = &self.gl.as_ref().unwrap().font;
        let mut lines = Vec::new();
        let paragraphs: Vec<&str> = text.split('\n').collect();
        for (pi, &paragraph) in paragraphs.iter().enumerate() {
            // dwm pushes a line for every explicit newline, including empty
            // and whitespace-only paragraphs.
            let explicit_break = pi + 1 < paragraphs.len();
            if paragraph.is_empty() {
                if explicit_break {
                    lines.push(String::new());
                    if lines.len() >= max_lines {
                        return lines;
                    }
                }
                continue;
            }
            let mut current = String::new();
            let mut last_space: Option<usize> = None;
            for ch in paragraph.chars() {
                if current.len() + ch.len_utf8() >= 1024 && !current.is_empty() {
                    lines.push(current.trim_end().to_string());
                    if lines.len() >= max_lines {
                        return lines;
                    }
                    current.clear();
                    last_space = None;
                }
                let mut candidate = current.clone();
                candidate.push(ch);
                if font.text_width(&candidate) as i32 <= width {
                    if ch == ' ' || ch == '\t' {
                        last_space = Some(current.len());
                    }
                    current = candidate;
                    continue;
                }
                if let Some(index) = last_space {
                    let line = current[..index].trim_end().to_string();
                    if !line.is_empty() {
                        lines.push(line);
                    }
                    if lines.len() >= max_lines {
                        return lines;
                    }
                    current = current[index..].trim_start().to_string();
                    current.push(ch);
                    last_space = None;
                } else if !current.is_empty() {
                    lines.push(current.trim_end().to_string());
                    if lines.len() >= max_lines {
                        return lines;
                    }
                    current = ch.to_string();
                } else {
                    current = ch.to_string();
                }
            }
            if (explicit_break || !current.is_empty()) && lines.len() < max_lines {
                lines.push(current.trim_end().to_string());
            }
            if lines.len() >= max_lines {
                break;
            }
        }
        lines
    }

    fn text_block_height(&self, has_summary: bool, body_lines: usize) -> i32 {
        if self.gl.is_none() || (!has_summary && body_lines == 0) {
            return 0;
        }
        let gl = self.gl.as_ref().unwrap();
        let line_h = gl.font.height.max(1);
        let body_line_h = (gl.font.pixel_size.ceil() as i32 + NOTIFY_BODY_LINE_GAP).max(1);
        let mut height = gl.font.ascender().max(1) + gl.font.descender().max(0);
        if has_summary && body_lines > 0 {
            height += line_h + 2;
        }
        if body_lines > 1 {
            height += (body_lines - 1) as i32 * body_line_h;
        }
        height
    }

    fn clockpad_gap(&self) -> i32 {
        let gap = CLOCKPAD / 4;
        gap.max(1)
    }

    fn time_column_width(&self) -> i32 {
        self.time_text_width("00").max(1)
    }

    fn time_height(&self, bar_h: i32) -> i32 {
        let Some(gl) = &self.gl else {
            return (bar_h as f32 * 0.58).max(1.0) as i32;
        };
        let line_h = gl.time_font.height.max(1);
        3 * line_h + 2 * self.clockpad_gap()
    }

    /// Text/image/time area, without the input and action rows.
    fn history_content_height(&self, n: &Entry, bar_h: i32) -> i32 {
        let col = self.time_column_width();
        let mut body_w = NOTIFY_MAX_W - 2 * NOTIFY_PADDING - col - NOTIFY_HISTORY_TIME_GAP;
        if let Some(image) = &n.data.image {
            let (w, _) = self.image_display_size(image);
            body_w -= w + 12;
        }
        let lines = self.wrap_lines(&n.data.body, body_w.max(1), NOTIFY_HISTORY_BODY_MAX_LINES);
        let text_h = self.text_block_height(!n.data.summary.is_empty(), lines.len());
        let img_h = n
            .data
            .image
            .as_ref()
            .map(|img| self.image_display_size(img).1)
            .unwrap_or(0);
        self.time_height(bar_h).max(bar_h).max(text_h).max(img_h)
    }

    fn history_entry_content_height(&self, n: &Entry, bar_h: i32) -> i32 {
        let mut height = self.history_content_height(n, bar_h);
        if n.data.input_enabled {
            height += NOTIFY_INPUT_ROW_H;
        }
        if n.data.actions.len() >= 4 {
            height += NOTIFY_BUTTON_H;
        }
        height
    }

    fn history_entry_height(&self, n: &Entry, bar_h: i32, has_next: bool) -> i32 {
        self.history_entry_content_height(n, bar_h) + if has_next { NOTIFY_PADDING } else { 0 }
    }

    fn history_entries_height(&self, bar_h: i32) -> i32 {
        let last = self.history.len().saturating_sub(1);
        self.history
            .iter()
            .enumerate()
            .map(|(i, n)| self.history_entry_height(n, bar_h, i < last))
            .sum()
    }

    fn update_layout(&mut self, bar_h: i32) {
        if self.gl.is_none() {
            return;
        }
        if let Some(data) = self.current.as_ref().map(|n| n.data.clone()) {
            let pad = NOTIFY_PADDING;
            let (img_w, img_h) = data
                .image
                .as_ref()
                .map(|img| self.image_display_size(img))
                .unwrap_or((0, 0));
            let mut text_w = self
                .text_width(&data.summary)
                .max(self.text_width(&data.body));
            if data.input_enabled {
                text_w = text_w
                    .max(self.text_width(&data.input_placeholder))
                    .max(self.text_width(&data.input_text));
            }
            let actions = (data.actions.len() / 2).min(16);
            let visible = if self.hovered { actions } else { 0 };
            let mut action_w = 0;
            for i in 0..visible {
                action_w += self.text_width(&data.actions[i * 2 + 1]);
            }
            if visible > 1 {
                action_w += (visible as i32 - 1) * 16;
            }
            text_w = text_w.max(action_w);
            if img_w > 0 {
                text_w += img_w + 12;
            }
            let content_w = text_w.min(NOTIFY_MAX_W - 2 * pad);
            let notify_w = (content_w + 2 * pad).max(100);
            let content_w = notify_w - 2 * pad;
            let body_w = (content_w - if img_w > 0 { img_w + 12 } else { 0 }).max(1);
            let max_lines = if self.hovered {
                NOTIFY_POPUP_BODY_HOVER_MAX_LINES
            } else {
                NOTIFY_POPUP_BODY_MAX_LINES
            };
            let lines = self.wrap_lines(&data.body, body_w, max_lines);
            let text_h = self.text_block_height(!data.summary.is_empty(), lines.len());
            let content_h = text_h.max(img_h);
            let text_y = (content_h - text_h) / 2;
            let image_y = (content_h - img_h) / 2;
            let input_y = if data.input_enabled {
                pad + content_h
            } else {
                0
            };
            let action_y = if visible > 0 {
                pad + content_h
                    + if data.input_enabled {
                        NOTIFY_INPUT_ROW_H
                    } else {
                        0
                    }
            } else {
                0
            };
            let h = (content_h
                + if data.input_enabled {
                    NOTIFY_INPUT_ROW_H
                } else {
                    0
                }
                + if visible > 0 { NOTIFY_BUTTON_H } else { 0 }
                + 2 * pad)
                .max(50);

            let mut action_cells = Vec::new();
            if visible > 0 {
                let label_w: Vec<i32> = (0..visible)
                    .map(|i| self.text_width(&data.actions[i * 2 + 1]))
                    .collect();
                // dwm's action_w already includes the 16px separators. Each
                // cell uses its label plus a separator except the last one.
                let total = action_w.max(visible as i32);
                let mut used = 0;
                for i in 0..visible {
                    let weight = label_w[i] + if i + 1 < visible { 16 } else { 0 };
                    let cell = if i + 1 == visible {
                        content_w - used
                    } else {
                        ((content_w as i64 * weight.max(1) as i64) / total as i64)
                            .max(1)
                            .min(content_w.saturating_sub(used) as i64)
                            as i32
                    };
                    let cell = cell.max(0).min(content_w - used);
                    action_cells.push((pad + used, cell));
                    used += cell;
                }
            }

            self.notify_width = notify_w;
            self.notify_height = h;
            let current = self.current.as_mut().unwrap();
            current.text_y = text_y;
            current.image_y = image_y;
            current.input_y = input_y;
            current.action_y = action_y;
            current.action_x = action_cells.iter().map(|(x, _)| *x).collect();
            current.action_w = action_cells.into_iter().map(|(_, w)| w).collect();
        } else if self.is_history_active() {
            self.notify_width = NOTIFY_MAX_W;
            let content = self.history_entries_height(bar_h);
            let h = (content + 2 * NOTIFY_PADDING)
                .max(bar_h)
                .min(NOTIFY_HISTORY_MAX_H);
            self.notify_height = h;
            let max = self.max_scroll(bar_h);
            self.history_scroll = self.history_scroll.clamp(0, max);
            self.history_scroll_target = self.history_scroll_target.clamp(0, max);
            if max == 0 {
                self.history_scroll = 0;
                self.history_scroll_target = 0;
            }
        } else {
            self.notify_width = 0;
            self.notify_height = 0;
        }
        self.frame_valid = false;
    }

    fn history_surface_height(&self, bar_h: i32) -> u32 {
        self.history_entries_height(bar_h)
            .saturating_add(2 * NOTIFY_PADDING)
            .max(self.notify_height)
            .max(1) as u32
    }

    pub fn needs_draw(&self, w: u32, h: u32, x: i32, y: i32, bh: i32) -> bool {
        !self.frame_valid
            || self.presentation != Some((w, h, x, y))
            || self.frame_key != self.compute_key(bh)
    }

    fn compute_key(&self, bh: i32) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        bh.hash(&mut hasher);
        self.notify_width.hash(&mut hasher);
        self.notify_height.hash(&mut hasher);
        self.hovered.hash(&mut hasher);
        self.hover.hash(&mut hasher);
        self.input_focus.hash(&mut hasher);
        self.history_scroll.hash(&mut hasher);
        self.history_hover_entry.hash(&mut hasher);
        self.history_hover_action.hash(&mut hasher);
        self.is_history_active().hash(&mut hasher);
        if let Some(n) = &self.current {
            hash_entry(n, &mut hasher);
            n.action_x.hash(&mut hasher);
            n.action_w.hash(&mut hasher);
            n.input_y.hash(&mut hasher);
            n.action_y.hash(&mut hasher);
        }
        for n in &self.history {
            hash_entry(n, &mut hasher);
        }
        hasher.finish()
    }

    pub fn draw(
        &mut self,
        drw: &mut Drw,
        screen: i32,
        visual: *mut xlib::Visual,
        win: u64,
        x: i32,
        y: i32,
        bh: i32,
    ) -> Result<()> {
        if !self.is_active() || visual.is_null() {
            return Ok(());
        }
        let dpy = drw.dpy();
        self.prepare(dpy, screen, visual)?;
        let history = self.is_history_active();
        let (w, viewport_h) = self.popup_size(bh);
        let surface_h = if history {
            self.history_surface_height(bh)
        } else {
            viewport_h
        };
        // The frame/mask are viewport-sized; only the GL foreground scrolls.
        self.frame.resize(dpy, visual, w, viewport_h)?;
        let key = self.compute_key(bh);
        if self.frame_valid
            && key == self.frame_key
            && self.presentation == Some((w, viewport_h, x, y))
        {
            self.present(drw, win, x, y, w, viewport_h, false);
            return Ok(());
        }
        drw.resize(w, surface_h);
        {
            let gl = self
                .gl
                .as_mut()
                .ok_or("notification GL state is unavailable")?;
            gl.pbuffer.make_current()?;
            gl.surface.resize(w, surface_h)?;
        }
        let c = compat()?;
        unsafe {
            gl::Viewport(0, 0, w as i32, surface_h as i32);
            c.matrix_mode(0x1701);
            c.load_identity();
            c.ortho(0.0, w as f64, surface_h as f64, 0.0, -1.0, 1.0);
            c.matrix_mode(0x1700);
            c.load_identity();
            gl::Disable(gl::DEPTH_TEST);
            gl::Disable(0x0C11); // GL_SCISSOR_TEST
            gl::ClearColor(0.0, 0.0, 0.0, 0.0);
            gl::Clear(gl::COLOR_BUFFER_BIT);
        }
        if history {
            let pad = NOTIFY_PADDING;
            let content_w = (w as i32 - 2 * pad).max(1);
            let content_h = (surface_h as i32 - 2 * pad).max(1);
            unsafe {
                gl::Enable(0x0C11); // GL_SCISSOR_TEST
                gl::Scissor(pad, pad, content_w, content_h);
            }
            self.draw_history(bh);
            unsafe {
                gl::Disable(0x0C11);
            }
            let gl = self
                .gl
                .as_mut()
                .ok_or("notification GL state is unavailable")?;
            gl.surface.readback()?;
            self.frame.composite_history(
                gl.surface.picture(),
                self.history_scroll,
                viewport_h,
                surface_h,
            );
        } else {
            self.draw_popup();
            let gl = self
                .gl
                .as_mut()
                .ok_or("notification GL state is unavailable")?;
            gl.surface.readback()?;
            self.frame.composite_popup(gl.surface.picture());
        }
        self.frame_key = key;
        self.frame_valid = true;
        self.present(drw, win, x, y, w, viewport_h, true);
        Ok(())
    }

    fn present(
        &mut self,
        drw: &Drw,
        win: u64,
        x: i32,
        y: i32,
        w: u32,
        h: u32,
        geometry_changed: bool,
    ) {
        let dpy = drw.dpy();
        // Both popup and history frames are fully composited into
        // `frame_picture` before presentation, so one path covers both.
        let source = self.frame.frame_picture;
        unsafe {
            xlib::XGrabServer(dpy);
            if geometry_changed || self.presentation != Some((w, h, x, y)) {
                xlib::XMoveResizeWindow(dpy, win, x, y, w, h);
            }
            xlib::XFlush(dpy);
        }
        let visual = self.frame.visual;
        let dest = unsafe {
            let format = xrender::XRenderFindVisualFormat(dpy, visual);
            if format.is_null() || source == 0 {
                0
            } else {
                xrender::XRenderCreatePicture(dpy, win, format, 0, ptr::null())
            }
        };
        if dest != 0 {
            unsafe {
                let clear = xrender::XRenderColor {
                    red: 0,
                    green: 0,
                    blue: 0,
                    alpha: 0,
                };
                xrender::XRenderFillRectangle(dpy, xrender::PictOpSrc, dest, &clear, 0, 0, w, h);
                xrender::XRenderComposite(
                    dpy,
                    xrender::PictOpSrc,
                    source,
                    0,
                    dest,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    w,
                    h,
                );
                xrender::XRenderFreePicture(dpy, dest);
            }
        }
        unsafe {
            xlib::XUngrabServer(dpy);
            xlib::XFlush(dpy);
        }
        self.presentation = Some((w, h, x, y));
    }

    fn draw_popup(&mut self) {
        let Some(n) = self.current.as_ref() else {
            return;
        };
        let pad = NOTIFY_PADDING;
        let (img_w, img_h) = n
            .data
            .image
            .as_ref()
            .map(|img| self.image_display_size(img))
            .unwrap_or((0, 0));
        let (line_h, body_line_h, ascender) = self.layout_metrics();
        let text_x = pad + if img_w > 0 { img_w + 12 } else { 0 };
        let text_width = (self.notify_width - text_x - pad).max(1);
        let body_lines =
            self.wrap_lines(&n.data.body, text_width, if self.hovered { 4 } else { 2 });
        let single = img_w == 0
            && !n.data.input_enabled
            && !(self.hovered && n.data.actions.len() >= 2)
            && usize::from(!n.data.summary.is_empty()) + body_lines.len() == 1;
        let mut text_x = text_x;
        if single {
            let width = if !n.data.summary.is_empty() {
                self.text_width(&n.data.summary)
            } else {
                body_lines
                    .first()
                    .map(|line| self.text_width(line))
                    .unwrap_or(0)
            };
            text_x += (text_width - width) / 2;
        }
        let mut baseline = pad + n.text_y + ascender;
        if img_w > 0 {
            if let Some(image) = &n.data.image {
                self.draw_image(image, pad, pad + n.image_y, img_w, img_h, FG, false);
            }
        }
        let gl = self.gl.as_mut().unwrap();
        let _ = gl.font.draw_text(
            &n.data.summary,
            text_x,
            baseline,
            text_width as u32,
            FG,
            1.0,
        );
        if !n.data.summary.is_empty() {
            baseline += line_h + 2;
        }
        self.draw_body(
            text_x,
            baseline,
            text_width as u32,
            &body_lines,
            body_line_h,
            BODY,
        );

        if n.data.input_enabled {
            let max_width = (self.notify_width - 2 * pad).max(1);
            let y = n.input_y + (NOTIFY_INPUT_ROW_H - line_h).max(0) / 2 + ascender;
            let mut visible = String::new();
            let mut cursor_w = 0;
            if self.input_focus {
                // dwm draws the blinking cursor first, then the dimmed
                // placeholder immediately to its right when nothing is typed.
                visible = n.data.input_text.clone();
                cursor_w = self.text_width("|");
                while !visible.is_empty() && self.text_width(&visible) + cursor_w > max_width {
                    let first = visible.chars().next().unwrap();
                    visible.drain(..first.len_utf8());
                }
            }
            let gl = self.gl.as_mut().unwrap();
            if self.input_focus {
                let _ =
                    gl.font
                        .draw_text(&format!("{visible}|"), pad, y, max_width as u32, FG, 1.0);
                if visible.is_empty() && !n.data.input_placeholder.is_empty() {
                    let _ = gl.font.draw_text(
                        &n.data.input_placeholder,
                        pad + cursor_w,
                        y,
                        (max_width - cursor_w).max(0) as u32,
                        PLACEHOLDER,
                        1.0,
                    );
                }
            } else {
                let value = if n.data.input_text.is_empty() {
                    &n.data.input_placeholder
                } else {
                    &n.data.input_text
                };
                let color = if n.data.input_text.is_empty() {
                    PLACEHOLDER
                } else {
                    CONTROL_TEXT
                };
                let _ = gl
                    .font
                    .draw_text(value, pad, y, max_width as u32, color, 1.0);
            }
        }
        if self.hovered {
            let actions = (n.data.actions.len() / 2).min(16);
            for i in 0..actions {
                if i >= n.action_x.len() {
                    break;
                }
                let label = &n.data.actions[i * 2 + 1];
                let label_w = self.text_width(label);
                let x = n.action_x[i] + n.action_w[i] - label_w.min(n.action_w[i]);
                let y = n.action_y + (NOTIFY_BUTTON_H - line_h).max(0) / 2 + ascender;
                let color = if self.hover == i as i32 { FG } else { ACTION };
                let gl = self.gl.as_mut().unwrap();
                let _ = gl
                    .font
                    .draw_text(label, x, y, n.action_w[i].max(0) as u32, color, 1.0);
            }
        }
    }

    fn draw_history(&mut self, bar_h: i32) {
        let pad = NOTIFY_PADDING;
        let time_col = self.time_column_width();
        let media_x = pad + time_col + NOTIFY_HISTORY_TIME_GAP;
        let content_w = self.notify_width - 2 * pad;
        let (line_h, body_line_h, ascender) = self.layout_metrics();
        let surface_h = self.history_surface_height(bar_h) as i32;
        let entries_len = self.history.len();
        let last = entries_len.saturating_sub(1);
        let mut y = pad;
        let entries: Vec<Entry> = self.history.iter().cloned().collect();
        for (i, n) in entries.iter().enumerate() {
            let entry_h = self.history_entry_height(n, bar_h, i < last);
            let content_h = self.history_content_height(n, bar_h);
            if y + entry_h <= pad {
                y += entry_h;
                continue;
            }
            if y >= surface_h - pad {
                break;
            }
            let dimmed = n.action_used || (n.data.actions.len() < 2 && !n.data.input_enabled);
            let (img_w, img_h) = n
                .data
                .image
                .as_ref()
                .map(|img| self.image_display_size(img))
                .unwrap_or((0, 0));
            let image_x = media_x;
            let image_y = y + (content_h - img_h) / 2;
            let mut text_x = image_x
                + if img_w > 0 {
                    img_w + 12
                } else {
                    NOTIFY_HISTORY_TEXT_ONLY_OFFSET
                };
            if img_w > 0 {
                if let Some(image) = &n.data.image {
                    self.draw_image(
                        image,
                        image_x,
                        image_y,
                        img_w,
                        img_h,
                        if dimmed { DIM_MEDIA } else { FG },
                        true,
                    );
                }
            }
            let body_w = (content_w
                - time_col
                - NOTIFY_HISTORY_TIME_GAP
                - if img_w > 0 { img_w + 12 } else { 0 })
            .max(1);
            let lines = self.wrap_lines(&n.data.body, body_w, NOTIFY_HISTORY_BODY_MAX_LINES);
            let text_h = self.text_block_height(!n.data.summary.is_empty(), lines.len());
            let text_y = y + (content_h - text_h).max(0) / 2;
            let mut baseline = text_y + ascender;
            self.draw_time(&n.data.received_time, pad, y, content_h, dimmed, bar_h);
            let gl = self.gl.as_mut().unwrap();
            let _ = gl.font.draw_text(
                &n.data.summary,
                text_x,
                baseline,
                body_w as u32,
                if dimmed { DIM_SUMMARY } else { FG },
                1.0,
            );
            if !n.data.summary.is_empty() {
                baseline += line_h + 2;
            }
            self.draw_body(
                text_x,
                baseline,
                body_w as u32,
                &lines,
                body_line_h,
                if dimmed { DIM_BODY } else { BODY },
            );
            text_x = pad;
            let _ = text_x;
            let mut controls_y = y + content_h;
            if n.data.input_enabled {
                let value = if n.data.input_text.is_empty() {
                    &n.data.input_placeholder
                } else {
                    &n.data.input_text
                };
                let color = if !n.data.input_text.is_empty() {
                    CONTROL_TEXT
                } else {
                    PLACEHOLDER
                };
                let gl = self.gl.as_mut().unwrap();
                let _ = gl.font.draw_text(
                    value,
                    pad,
                    controls_y + (NOTIFY_INPUT_ROW_H - line_h).max(0) / 2 + ascender,
                    content_w as u32,
                    color,
                    1.0,
                );
                controls_y += NOTIFY_INPUT_ROW_H;
            }
            if n.data.actions.len() >= 4 {
                let actions = (n.data.actions.len() / 2).min(16);
                let cell = content_w / actions as i32;
                for i in 0..actions {
                    let label = &n.data.actions[i * 2 + 1];
                    let label_w = self.text_width(label);
                    let x = pad + i as i32 * cell + cell - label_w.min(cell);
                    let color = if self.history_hover_action == i as i32 {
                        FG
                    } else {
                        ACTION
                    };
                    let gl = self.gl.as_mut().unwrap();
                    let _ = gl.font.draw_text(
                        label,
                        x,
                        controls_y + (NOTIFY_BUTTON_H - line_h).max(0) / 2 + ascender,
                        cell as u32,
                        color,
                        1.0,
                    );
                }
            }
            y += entry_h;
        }
    }

    fn draw_body(
        &self,
        x: i32,
        mut baseline: i32,
        width: u32,
        lines: &[String],
        line_h: i32,
        color: (f32, f32, f32),
    ) {
        let Some(gl) = self.gl.as_ref() else {
            return;
        };
        for line in lines {
            let _ = gl.font.draw_text(line, x, baseline, width, color, 1.0);
            baseline += line_h;
        }
    }

    fn draw_time(&self, time: &str, x: i32, y: i32, content_h: i32, dimmed: bool, _bar_h: i32) {
        if self.gl.is_none() || time.len() < 8 {
            return;
        }
        let col_w = self.time_column_width();
        let line_h = self.gl.as_ref().unwrap().time_font.height.max(1);
        let time_ascender = self.gl.as_ref().unwrap().time_font.ascender();
        let gap = self.clockpad_gap();
        let stack_h = 3 * line_h + 2 * gap;
        let stack_y = y + (content_h - stack_h).max(0) / 2;
        let color = if dimmed { DIM_TIME } else { TIME };
        for (group, offset) in [0usize, 3, 6].iter().enumerate() {
            let text = &time[*offset..(*offset + 2).min(time.len())];
            let w = self.time_text_width(text);
            let Some(gl) = self.gl.as_ref() else {
                return;
            };
            let _ = gl.time_font.draw_text(
                text,
                x + (col_w - w as i32).max(0) / 2,
                stack_y + (group as i32) * (line_h + gap) + time_ascender,
                col_w as u32,
                color,
                1.0,
            );
            if group < 2 {
                let rule_w = 12.min(col_w);
                let rule_y = stack_y + group as i32 * (line_h + gap) + line_h + (gap - 1) / 2;
                let c = compat().expect("GL compatibility entry points");
                unsafe {
                    gl::Disable(gl::TEXTURE_2D);
                    gl::Enable(gl::BLEND);
                    if gl::BlendFuncSeparate::is_loaded() {
                        gl::BlendFuncSeparate(
                            gl::SRC_ALPHA,
                            gl::ONE_MINUS_SRC_ALPHA,
                            gl::ONE,
                            gl::ONE_MINUS_SRC_ALPHA,
                        );
                    } else {
                        gl::BlendFunc(gl::SRC_ALPHA, gl::ONE_MINUS_SRC_ALPHA);
                    }
                    c.color4f(color.0, color.1, color.2, 1.0);
                    c.begin(gl::QUADS);
                    c.vertex2f((x + (col_w - rule_w) / 2) as f32, rule_y as f32);
                    c.vertex2f((x + (col_w + rule_w) / 2) as f32, rule_y as f32);
                    c.vertex2f((x + (col_w + rule_w) / 2) as f32, (rule_y + 1) as f32);
                    c.vertex2f((x + (col_w - rule_w) / 2) as f32, (rule_y + 1) as f32);
                    c.end();
                    gl::Disable(gl::BLEND);
                }
            }
        }
    }

    fn draw_image(
        &self,
        image: &ImageData,
        x: i32,
        y: i32,
        w: i32,
        h: i32,
        color: (f32, f32, f32),
        separate: bool,
    ) {
        if image.pixels.is_empty() || w <= 0 || h <= 0 {
            return;
        }
        // dwm's `notification_image_texture_create()` bilinearly samples the
        // source into a display-sized buffer before the GL texture is uploaded.
        let (dw, dh) = (w as u32, h as u32);
        let src_w = image.width as usize;
        let src_h = image.height as usize;
        let mut bytes = Vec::with_capacity((dw * dh * 4) as usize);
        for dy in 0..dh {
            let sy = ((dy as f64 + 0.5) * image.height as f64 / dh as f64) - 0.5;
            let sy = sy.max(0.0);
            let y0 = (sy as usize).min(src_h - 1);
            let y1 = (y0 + 1).min(src_h - 1);
            let fy = sy - y0 as f64;
            for dx in 0..dw {
                let sx = ((dx as f64 + 0.5) * image.width as f64 / dw as f64) - 0.5;
                let sx = sx.max(0.0);
                let x0 = (sx as usize).min(src_w - 1);
                let x1 = (x0 + 1).min(src_w - 1);
                let fx = sx - x0 as f64;
                let p00 = image.pixels[y0 * src_w + x0];
                let p10 = image.pixels[y0 * src_w + x1];
                let p01 = image.pixels[y1 * src_w + x0];
                let p11 = image.pixels[y1 * src_w + x1];
                let mut pixel = 0u32;
                for shift in [0, 8, 16, 24] {
                    let top = ((p00 >> shift) & 0xff) as f64 * (1.0 - fx)
                        + ((p10 >> shift) & 0xff) as f64 * fx;
                    let bottom = ((p01 >> shift) & 0xff) as f64 * (1.0 - fx)
                        + ((p11 >> shift) & 0xff) as f64 * fx;
                    let channel = (top * (1.0 - fy) + bottom * fy).round() as u32;
                    pixel |= channel << shift;
                }
                bytes.extend_from_slice(&pixel.to_ne_bytes());
            }
        }
        let mut texture = 0;
        unsafe {
            gl::GenTextures(1, &mut texture);
            gl::BindTexture(gl::TEXTURE_2D, texture);
            gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MIN_FILTER, gl::LINEAR as i32);
            gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MAG_FILTER, gl::LINEAR as i32);
            gl::PixelStorei(gl::UNPACK_ALIGNMENT, 4);
            gl::TexImage2D(
                gl::TEXTURE_2D,
                0,
                gl::RGBA as i32,
                dw as i32,
                dh as i32,
                0,
                gl::BGRA,
                gl::UNSIGNED_BYTE,
                bytes.as_ptr() as *const _,
            );
            gl::Enable(gl::TEXTURE_2D);
            gl::Enable(gl::BLEND);
            if separate && gl::BlendFuncSeparate::is_loaded() {
                gl::BlendFuncSeparate(
                    gl::SRC_ALPHA,
                    gl::ONE_MINUS_SRC_ALPHA,
                    gl::ONE,
                    gl::ONE_MINUS_SRC_ALPHA,
                );
            } else {
                gl::BlendFunc(gl::SRC_ALPHA, gl::ONE_MINUS_SRC_ALPHA);
            }
            let c = compat().expect("GL compatibility entry points");
            c.color4f(color.0, color.1, color.2, 1.0);
            c.begin(gl::QUADS);
            c.tex_coord2f(0.0, 0.0);
            c.vertex2f(x as f32, y as f32);
            c.tex_coord2f(1.0, 0.0);
            c.vertex2f((x + w) as f32, y as f32);
            c.tex_coord2f(1.0, 1.0);
            c.vertex2f((x + w) as f32, (y + h) as f32);
            c.tex_coord2f(0.0, 1.0);
            c.vertex2f(x as f32, (y + h) as f32);
            c.end();
            gl::BindTexture(gl::TEXTURE_2D, 0);
            gl::Disable(gl::BLEND);
            gl::Disable(gl::TEXTURE_2D);
            gl::DeleteTextures(1, &texture);
        }
    }
}

fn clear_controls(data: &mut NotificationData) {
    data.actions.clear();
    data.input_enabled = false;
    data.input_action.clear();
    data.input_placeholder.clear();
    data.input_text.clear();
}

fn hash_entry<T: Hasher>(n: &Entry, hasher: &mut T) {
    n.data.id.hash(hasher);
    n.data.app_name.hash(hasher);
    n.data.summary.hash(hasher);
    n.data.body.hash(hasher);
    n.data.actions.hash(hasher);
    n.data.input_enabled.hash(hasher);
    n.data.input_action.hash(hasher);
    n.data.input_placeholder.hash(hasher);
    n.data.input_text.hash(hasher);
    n.data.received_time.hash(hasher);
    n.action_used.hash(hasher);
    n.data
        .image
        .as_ref()
        .map(|i| i.pixels.as_ptr() as usize)
        .hash(hasher);
}

// `GlFont` caches glyphs behind a `RefCell`, so measuring text only needs a
// shared reference even when called from layout code.
fn unsafe_font_width(font: &GlFont, text: &str) -> u32 {
    font.text_width(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vertical_alpha_matches_dwm_stops() {
        assert_eq!(vertical_alpha(0, 100), 255);
        assert_eq!(vertical_alpha(50, 100), 227);
        assert_eq!(vertical_alpha(99, 100), 128);
        assert!(vertical_alpha(50, 100) > vertical_alpha(90, 100));
    }

    #[test]
    fn popup_background_matches_dwm() {
        // XRender's 16-bit channels are rounded down to 8 bits by the server.
        assert_eq!(POPUP_BACKGROUND.0 / 257, 30);
        assert_eq!(POPUP_BACKGROUND.1 / 257, 33);
        assert_eq!(POPUP_BACKGROUND.2 / 257, 43);
        assert_eq!(POPUP_BACKGROUND.3, 65535);
    }

    #[test]
    fn motion_opens_history_after_entering_visualizer_padding() {
        let mut manager = NotificationManager::new(None);
        let data = parse_notification(1, "app", "", "summary", "body", Vec::new(), HashMap::new());
        manager.history.push_front(Entry::new(data));
        assert!(!manager.is_history_active());
        // No prior enter(): the pointer reached the clock-sized hit region by
        // moving in from the animated visualizer padding.
        assert!(manager.motion(0, 0, 100, 20, 20));
        assert!(manager.is_history_active());
    }

    #[test]
    fn icon_fit_keeps_aspect() {
        assert_eq!(fit_size(200, 100, 260, 60), (120, 60));
        assert_eq!(fit_size(10, 10, 260, 60), (10, 10));
        assert_eq!(fit_size(201, 100, 260, 60), (120, 60));
    }

    #[test]
    fn input_hint_gets_dwms_submit_action() {
        let hints = HashMap::from([("x-andwm-input".to_string(), OwnedValue::from(true))]);
        let data = parse_notification(1, "app", "", "summary", "", Vec::new(), hints);
        assert!(data.input_enabled);
        assert_eq!(data.input_action, "submit");

        let empty: OwnedValue = zbus::zvariant::Value::from("")
            .try_into()
            .expect("empty string value");
        let hints = HashMap::from([("x-andwm-input-action".to_string(), empty)]);
        let data = parse_notification(1, "app", "", "summary", "", Vec::new(), hints);
        assert!(data.input_enabled);
        assert_eq!(data.input_action, "submit");
    }

    #[test]
    fn signal_bodies_are_flat_not_structs() {
        let ctxt = Context::new_dbus(NATIVE_ENDIAN, 0);
        let action = to_bytes_for_signature(ctxt, "us", &(7u32, "act")).expect("us body");
        let bytes = action.bytes();
        assert_eq!(bytes.len(), 4 + 4 + 3 + 1);
        assert_eq!(&bytes[0..4], &7u32.to_ne_bytes());
        assert_eq!(u32::from_ne_bytes(bytes[4..8].try_into().unwrap()), 3);
        assert_eq!(&bytes[8..], b"act\0");

        let closed = to_bytes_for_signature(ctxt, "uu", &(7u32, 2u32)).expect("uu body");
        assert_eq!(closed.bytes().len(), 8);
    }
}
