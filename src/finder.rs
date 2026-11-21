//! Finder: the modal application launcher ported from AnDWM's `dwm.c`.
//!
//! Keeps the full feature set: desktop discovery, fuzzy ranking and recency,
//! math and translation/OCR results, OpenGL text/icons with Kawase bloom,
//! smooth scrolling, filter animation, aggressive ARGB opacity, and the
//! separate white marker window.

use std::collections::hash_map::DefaultHasher;
use std::env;
use std::error::Error;
use std::ffi::{CStr, CString, c_char, c_double, c_int};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::ptr;
use std::time::{Duration, Instant};

use x11::keysym::{
    XK_BackSpace, XK_Delete, XK_Down, XK_End, XK_Escape, XK_Home, XK_KP_Enter, XK_Left, XK_Return,
    XK_Right, XK_Up,
};
use x11::xft::{FcPattern, XftFont, XftFontClose, XftFontOpenName};
use x11::xlib;
use x11::xrender;

use crate::bar::{CLOCKPAD, CLRBORDER, scheme_norm, scheme_title};
use crate::config::{FINDER_APP_DIRS, FINDER_MARKER_WIDTH, FINDER_ROWS, FINDER_WIDTH};
use crate::drw::Drw;
use crate::finder_math;
use crate::finder_net::{FinderNet, NetResult};
use crate::gl::{
    Bloom, BloomTransform, GlFont, GlFontSpec, GlPbuffer, GlSurface, Result as GlResult,
};
use crate::text::FONTS;

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

const MAX_APPS: usize = 512;
const MAX_QUERY: usize = 2048;
const EDGE: i32 = 15;

/// GLX pbuffers are recreated by Mesa's software renderer with an internal
/// SHM image whenever their size changes, which raises BadMatch on the second
/// size. Keep one pbuffer large enough for every popup layout and drive the
/// current layout with the viewport instead, as the GL surface does.
const GL_PBUFFER_MAX_WIDTH: u32 = 550;
const GL_PBUFFER_MAX_HEIGHT: u32 = 2048;
const ICON_GAP: i32 = 8;
const ICON_SIZE: i32 = 22;
/// AnDWM `scheme[SchemeTitle][ColFg]` (#f8f8f2).
const FG: (f32, f32, f32) = (248.0 / 255.0, 248.0 / 255.0, 242.0 / 255.0);
/// AnDWM's `finder_text` (#B8B5C8).
const FINDER_TEXT: (f32, f32, f32) = (184.0 / 255.0, 181.0 / 255.0, 200.0 / 255.0);
const CURSOR_BLINK: Duration = Duration::from_millis(500);
const FILTER_ANIM: Duration = Duration::from_millis(180);
const FILTER_ALPHA_DELAY_MS: f32 = 50.0;
const FILTER_TEXT_BLUR: f32 = 2.0;
const FILTER_IMAGE_BLUR: f32 = 20.0;
const SCROLL_TICK: Duration = Duration::from_millis(10);
const TRANSLATE_DEBOUNCE: Duration = Duration::from_millis(500);
const RESULT_FADE: Duration = Duration::from_millis(220);
const GLOW_FADE: Duration = Duration::from_millis(300);
const GLOW_TICK: Duration = Duration::from_millis(30);
const QUERY_POSE: Duration = Duration::from_millis(180);
/// Network results arrive on a channel, but the main loop still has to poll.
/// A finite deadline keeps an in-flight translation from spinning at 0 ms.
const NET_POLL: Duration = Duration::from_millis(30);
const GLOW_PERIOD_MS: f64 = 1400.0;

/// dwm's dedicated Finder result fontset, before every configured font is
/// resized to 16 pt.
const RESULT_FONT_NAME: &str = "Iosevka Medium:style:medium:size=16";

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcNameParse(name: *const c_char) -> *mut FcPattern;
    fn FcNameUnparse(pattern: *mut FcPattern) -> *mut c_char;
    fn FcStrFree(name: *mut c_char);
    fn FcPatternDel(pattern: *mut FcPattern, object: *const c_char) -> c_int;
    fn FcPatternAddDouble(pattern: *mut FcPattern, object: *const c_char, value: c_double)
    -> c_int;
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
    fn FcPatternDestroy(pattern: *mut FcPattern);
}

#[derive(Clone)]
struct App {
    name: String,
    exec: String,
    file: String,
    icon_name: String,
    icon_tex: u32,
    icon_loaded: bool,
    recent: i32,
    score: i32,
}

#[derive(Clone, Copy)]
struct FilterAnim {
    from_y: f32,
    to_y: f32,
    from_alpha: f32,
    to_alpha: f32,
    from_scale_x: f32,
    to_scale_x: f32,
    from_scale_y: f32,
    to_scale_y: f32,
    from_blur: f32,
    to_blur: f32,
    active: bool,
    outgoing: bool,
}

impl Default for FilterAnim {
    fn default() -> Self {
        Self {
            from_y: 0.0,
            to_y: 0.0,
            from_alpha: 0.0,
            to_alpha: 0.0,
            from_scale_x: 1.0,
            to_scale_x: 1.0,
            from_scale_y: 1.0,
            to_scale_y: 1.0,
            from_blur: 0.0,
            to_blur: 0.0,
            active: false,
            outgoing: false,
        }
    }
}

/// Resolved Xft faces for one GL font instance, mirroring dwm's
/// `gl_font_create_scaled()` inputs.
struct FontBundle {
    specs: Vec<GlFontSpec>,
    height: i32,
    lcd_order: u8,
}

// Field order is drop order: textures need a current context, so the font is
// released before the pbuffer that owns it.
struct GlState {
    font: GlFont,
    query_font: GlFont,
    result_font: GlFont,
    /// Measured advance of one representative character, used by the geometry
    /// estimate before GL text is actually drawn.
    query_char_width: u32,
    result_char_width: u32,
    surface: GlSurface,
    bloom: Bloom,
    pbuffer: GlPbuffer,
}

/// The two-layer offscreen frame used by dwm: an opaque background that
/// receives the 12-stop opacity ramp, and the final pixmap that the GL overlay
/// is composited over before the whole frame is copied to the ARGB window.
struct FrameSurface {
    dpy: *mut xlib::Display,
    visual: *mut xlib::Visual,
    bg_pixmap: xlib::Pixmap,
    bg_picture: xrender::Picture,
    /// Cached GL-over-background composite, without the blinking caret.
    base_pixmap: xlib::Pixmap,
    base_picture: xrender::Picture,
    /// Presentation frame: a cheap copy of `base_pixmap` plus the caret.
    pixmap: xlib::Pixmap,
    picture: xrender::Picture,
    width: u32,
    height: u32,
}

impl FrameSurface {
    fn new(dpy: *mut xlib::Display, visual: *mut xlib::Visual) -> FrameSurface {
        FrameSurface {
            dpy,
            visual,
            bg_pixmap: 0,
            bg_picture: 0,
            base_pixmap: 0,
            base_picture: 0,
            pixmap: 0,
            picture: 0,
            width: 0,
            height: 0,
        }
    }

    fn resize(&mut self, width: u32, height: u32) -> Result<()> {
        if self.picture != 0 && (self.width, self.height) == (width, height) {
            return Ok(());
        }
        self.destroy();
        unsafe {
            let format = xrender::XRenderFindStandardFormat(self.dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                return Err("XRender has no ARGB32 picture format".into());
            }
            for (pixmap, picture) in [
                (&mut self.bg_pixmap, &mut self.bg_picture),
                (&mut self.base_pixmap, &mut self.base_picture),
                (&mut self.pixmap, &mut self.picture),
            ] {
                *pixmap = xlib::XCreatePixmap(
                    self.dpy,
                    xlib::XDefaultRootWindow(self.dpy),
                    width,
                    height,
                    32,
                );
                if *pixmap == 0 {
                    return Err("cannot create finder frame pixmap".into());
                }
                *picture = xrender::XRenderCreatePicture(self.dpy, *pixmap, format, 0, ptr::null());
                if *picture == 0 {
                    return Err("cannot create finder frame picture".into());
                }
            }
        }
        self.width = width;
        self.height = height;
        Ok(())
    }

    fn fill(&self, x: i32, y: i32, w: u32, h: u32, color: (u16, u16, u16, u16)) {
        unsafe {
            let value = xrender::XRenderColor {
                red: color.0,
                green: color.1,
                blue: color.2,
                alpha: color.3,
            };
            xrender::XRenderFillRectangle(
                self.dpy,
                xrender::PictOpSrc,
                self.bg_picture,
                &value,
                x,
                y,
                w,
                h,
            );
        }
    }

    /// Refresh the presentation frame from the cached GL composite. This is a
    /// server-side XRender copy, so caret blinks and unrelated bar redraws never
    /// wake the GL context or re-run the bloom passes.
    fn copy_base(&self) {
        if self.base_picture == 0 || self.picture == 0 {
            return;
        }
        unsafe {
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpSrc,
                self.base_picture,
                0,
                self.picture,
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

    /// Draw the caret with XRender instead of GL. The rectangle is already in
    /// final screen coordinates, including the waiting-query transform.
    fn draw_caret(&self, rect: (i32, i32, i32, i32)) {
        if self.picture == 0 {
            return;
        }
        let (x, y, w, h) = rect;
        if w <= 0 || h <= 0 {
            return;
        }
        let color = xrender::XRenderColor {
            red: (FG.0 * 65535.0).round() as u16,
            green: (FG.1 * 65535.0).round() as u16,
            blue: (FG.2 * 65535.0).round() as u16,
            alpha: 0xffff,
        };
        unsafe {
            xrender::XRenderFillRectangle(
                self.dpy,
                xrender::PictOpSrc,
                self.picture,
                &color,
                x,
                y,
                w as u32,
                h as u32,
            );
        }
    }

    fn destroy(&mut self) {
        unsafe {
            if self.bg_picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.bg_picture);
            }
            if self.base_picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.base_picture);
            }
            if self.picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.picture);
            }
            if self.bg_pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.bg_pixmap);
            }
            if self.base_pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.base_pixmap);
            }
            if self.pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.pixmap);
            }
        }
        self.bg_pixmap = 0;
        self.bg_picture = 0;
        self.base_pixmap = 0;
        self.base_picture = 0;
        self.pixmap = 0;
        self.picture = 0;
        self.width = 0;
        self.height = 0;
    }
}

impl Drop for FrameSurface {
    fn drop(&mut self) {
        self.destroy();
    }
}

/// Geometry needed to move and map one cached Finder frame.
#[derive(Clone, Copy)]
struct PresentGeom {
    x: i32,
    y: i32,
    bh: i32,
    w: u32,
    h: u32,
}

/// Everything the finder needs while it is closed is cheap: the app list and
/// recent history are loaded once, GL resources are created lazily on open and
/// released on close.
pub struct Finder {
    active: bool,
    apps: Vec<App>,
    order: Vec<usize>,
    visible: usize,
    query: String,
    cursor: usize,
    view_start: usize,
    selected: usize,
    scroll: usize,
    scroll_visual: f64,
    scroll_started: Instant,
    cursor_base: Instant,
    cursor_visible: bool,
    dirty: bool,
    loading: bool,
    /// True once the full-size background-only frame has reached the ARGB
    /// window. Desktop discovery is held back until this happens, so opening
    /// Finder never shows a clock-sized patch while the app list is scanned.
    initial_background_presented: bool,
    icons_pending: bool,
    recent: Vec<String>,
    net: FinderNet,
    math_result: Option<String>,
    math_help: bool,
    math_started: Option<Instant>,
    translate_active: bool,
    translate_result: String,
    translate_started: Option<Instant>,
    translate_pending: bool,
    translate_due: Option<Instant>,
    translate_target_en: bool,
    translate_outgoing: String,
    translate_outgoing_started: Option<Instant>,
    glow_started: Option<Instant>,
    glow_from: f32,
    glow_fade_started: Option<Instant>,
    glow_fade_from: f32,
    query_pose_initialized: bool,
    query_pose_waiting: bool,
    query_pose: f32,
    query_pose_from: f32,
    query_pose_to: f32,
    query_pose_started: Instant,
    ocr_mode: bool,
    filter: Vec<FilterAnim>,
    filter_start_present: Vec<bool>,
    filter_start_y: Vec<f32>,
    filter_start_alpha: Vec<f32>,
    filter_start_scale_x: Vec<f32>,
    filter_start_scale_y: Vec<f32>,
    filter_start_blur: Vec<f32>,
    filter_started: Option<Instant>,
    filter_display_rows: usize,
    filter_animating: bool,
    frame: FrameSurface,
    frame_cache_key: u64,
    frame_cache_valid: bool,
    /// Bumped only when the expensive app/icon/order part of the frame changes.
    /// Hashing every app on every bar refresh was the remaining idle CPU cost.
    frame_content_epoch: u64,
    /// Caret rectangle in final frame coordinates, cached with the GL frame so
    /// blinking only needs a cheap XRender fill.
    cached_caret: Option<(i32, i32, i32, i32)>,
    gl: Option<GlState>,
    presented: (u32, u32, i32, i32, i32),
    /// Placeholder text from the last painted frame. Bar-only redraws (MPRIS
    /// title scrolling, status samples) must not repaint the Finder popup.
    last_clock_text: String,
    marker_row: i32,
}

impl Finder {
    pub fn new() -> Self {
        let recent = Self::load_recent();
        Finder {
            active: false,
            apps: Vec::new(),
            order: Vec::new(),
            visible: 0,
            query: String::new(),
            cursor: 0,
            view_start: 0,
            selected: 0,
            scroll: 0,
            scroll_visual: 0.0,
            scroll_started: Instant::now(),
            cursor_base: Instant::now(),
            cursor_visible: true,
            dirty: false,
            loading: false,
            initial_background_presented: false,
            icons_pending: false,
            recent,
            net: FinderNet::new(),
            math_result: None,
            math_help: false,
            math_started: None,
            translate_active: false,
            translate_result: String::new(),
            translate_started: None,
            translate_pending: false,
            translate_due: None,
            translate_target_en: false,
            translate_outgoing: String::new(),
            translate_outgoing_started: None,
            glow_started: None,
            glow_from: 0.0,
            glow_fade_started: None,
            glow_fade_from: 0.0,
            query_pose_initialized: false,
            query_pose_waiting: false,
            query_pose: 0.0,
            query_pose_from: 0.0,
            query_pose_to: 0.0,
            query_pose_started: Instant::now(),
            ocr_mode: false,
            filter: Vec::new(),
            filter_start_present: Vec::new(),
            filter_start_y: Vec::new(),
            filter_start_alpha: Vec::new(),
            filter_start_scale_x: Vec::new(),
            filter_start_scale_y: Vec::new(),
            filter_start_blur: Vec::new(),
            filter_started: None,
            filter_display_rows: 0,
            filter_animating: false,
            frame: FrameSurface::new(ptr::null_mut(), ptr::null_mut()),
            frame_cache_key: 0,
            frame_cache_valid: false,
            frame_content_epoch: 0,
            cached_caret: None,
            gl: None,
            presented: (0, 0, 0, 0, 0),
            last_clock_text: String::new(),
            marker_row: 0,
        }
    }

    pub fn is_active(&self) -> bool {
        self.active
    }

    pub fn dirty(&self) -> bool {
        self.dirty
    }

    /// Cheap pre-check used by the WM before rebuilding a Finder frame. Bar
    /// animations can redraw the bars many times a second without changing
    /// anything inside the popup, so those refreshes must not touch GL or even
    /// copy the cached frame.
    pub fn needs_draw(&self, w: u32, h: u32, x: i32, y: i32, bh: i32, clock_text: &str) -> bool {
        if self.dirty || self.presented != (w, h, x, y, bh) || self.glow_animating() {
            return true;
        }
        self.query.is_empty() && self.last_clock_text != clock_text
    }

    fn bump_content_epoch(&mut self) {
        self.frame_content_epoch = self.frame_content_epoch.wrapping_add(1);
    }

    pub fn marker_row(&self) -> i32 {
        self.marker_row
    }

    // -----------------------------------------------------------------------
    // App discovery, ranking and recency
    // -----------------------------------------------------------------------

    fn expand(path: &str) -> String {
        if let Some(home) = env::var_os("HOME")
            && let Some(rest) = path.strip_prefix("~/")
        {
            return Path::new(&home).join(rest).to_string_lossy().into_owned();
        }
        path.to_string()
    }

    fn recent_path() -> Option<PathBuf> {
        if let Some(dir) = env::var_os("XDG_STATE_HOME") {
            let p = PathBuf::from(dir);
            if p.is_absolute() {
                return Some(p.join("dwm").join("finder-recent"));
            }
        }
        env::var_os("HOME").map(|h| Path::new(&h).join(".local/state/dwm/finder-recent"))
    }

    fn load_recent() -> Vec<String> {
        let Some(path) = Self::recent_path() else {
            return Vec::new();
        };
        fs::read_to_string(path)
            .unwrap_or_default()
            .lines()
            .take(10)
            .map(|l| l.trim_end_matches(['\r', '\n']).to_string())
            .filter(|l| !l.is_empty())
            .collect()
    }

    fn save_recent(&self) {
        let Some(path) = Self::recent_path() else {
            return;
        };
        if let Some(parent) = path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        let mut text = String::new();
        for item in &self.recent {
            text.push_str(item);
            text.push('\n');
        }
        let tmp = path.with_extension("tmp");
        if fs::write(&tmp, text).is_ok() {
            let _ = fs::rename(&tmp, &path);
        }
    }

    fn strip_field_codes(exec: &str) -> String {
        let bytes = exec.as_bytes();
        let mut out = String::new();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'%' {
                if i + 1 < bytes.len() && b"fFuUdiCk".contains(&bytes[i + 1]) {
                    i += 2;
                } else {
                    i += 1;
                }
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out
    }

    fn load_apps(&mut self) {
        self.apps.clear();
        for dir in FINDER_APP_DIRS {
            if self.apps.len() >= MAX_APPS {
                break;
            }
            let expanded = Self::expand(dir);
            let Ok(entries) = fs::read_dir(&expanded) else {
                continue;
            };
            for entry in entries.flatten() {
                if self.apps.len() >= MAX_APPS {
                    break;
                }
                let name = entry.file_name().to_string_lossy().into_owned();
                if !name.contains(".desktop") {
                    continue;
                }
                let path = entry.path();
                let Ok(text) = fs::read_to_string(&path) else {
                    continue;
                };
                let mut app = App {
                    name: String::new(),
                    exec: String::new(),
                    file: path.to_string_lossy().into_owned(),
                    icon_name: String::new(),
                    icon_tex: 0,
                    icon_loaded: false,
                    recent: 0,
                    score: 0,
                };
                let mut hidden = false;
                for line in text.lines() {
                    if let Some(v) = line.strip_prefix("Name=") {
                        if app.name.is_empty() {
                            app.name = v.to_string();
                        }
                    } else if let Some(v) = line.strip_prefix("Exec=") {
                        if app.exec.is_empty() {
                            app.exec = v.to_string();
                        }
                    } else if let Some(v) = line.strip_prefix("Icon=") {
                        if app.icon_name.is_empty() {
                            app.icon_name = v.to_string();
                        }
                    } else if line.starts_with("NoDisplay=true") || line.starts_with("Hidden=true")
                    {
                        hidden = true;
                    }
                }
                if hidden {
                    app.name.clear();
                }
                app.name = app.name.trim_end_matches(['\r', '\n']).to_string();
                app.exec = app.exec.trim_end_matches(['\r', '\n']).to_string();
                app.icon_name = app.icon_name.trim_end_matches(['\r', '\n']).to_string();
                app.exec = Self::strip_field_codes(&app.exec);
                if app.name.is_empty() || app.exec.is_empty() {
                    continue;
                }
                if let Some(pos) = self.recent.iter().position(|r| *r == app.file) {
                    app.recent = (self.recent.len() - pos) as i32;
                }
                self.apps.push(app);
            }
        }
        self.apps.sort_by(|a, b| {
            b.recent
                .cmp(&a.recent)
                .then_with(|| a.name.to_lowercase().cmp(&b.name.to_lowercase()))
        });
        self.ensure_filter_slots();
        self.rank();
    }

    fn name_score(name: &str, query: &str) -> i32 {
        let lower_name = name.to_lowercase();
        let lower_query = query.to_lowercase();
        if lower_name == lower_query {
            return 100_000;
        }
        if lower_name.starts_with(&lower_query) {
            return 90_000;
        }
        let Some(pos) = lower_name.find(&lower_query) else {
            return 0;
        };
        let boundary = pos > 0 && !name.as_bytes()[pos - 1].is_ascii_alphanumeric();
        (if boundary { 70_000 } else { 50_000 }) - (pos as i32) * 10
    }

    fn rank(&mut self) {
        self.order.clear();
        if self.math_result.is_some() || self.math_help {
            self.visible = 0;
            return;
        }
        for (i, app) in self.apps.iter_mut().enumerate() {
            let name_hit = if self.query.is_empty() {
                true
            } else {
                app.name.to_lowercase().contains(&self.query.to_lowercase())
                    || app.exec.to_lowercase().contains(&self.query.to_lowercase())
            };
            if !name_hit {
                continue;
            }
            app.score = if self.query.is_empty() {
                0
            } else {
                let s = Self::name_score(&app.name, &self.query);
                if s != 0 {
                    s
                } else if app.exec.to_lowercase().contains(&self.query.to_lowercase()) {
                    10_000
                } else {
                    0
                }
            };
            self.order.push(i);
        }
        self.order.sort_by(|&a, &b| {
            let aa = &self.apps[a];
            let bb = &self.apps[b];
            bb.score
                .cmp(&aa.score)
                .then_with(|| bb.recent.cmp(&aa.recent))
                .then_with(|| aa.name.to_lowercase().cmp(&bb.name.to_lowercase()))
        });
        self.visible = self.order.len();
        self.bump_content_epoch();
    }

    fn launch(&mut self) {
        let Some(&idx) = self.order.get(self.selected) else {
            return;
        };
        let (file, exec) = {
            let app = &self.apps[idx];
            (app.file.clone(), app.exec.clone())
        };
        let mut child = Command::new("gio");
        child.arg("launch").arg(&file);
        let spawned =
            child.spawn().is_ok() || Command::new("sh").arg("-c").arg(&exec).spawn().is_ok();
        let _ = spawned;
        if let Some(pos) = self.recent.iter().position(|r| *r == file) {
            self.recent.remove(pos);
        }
        self.recent.insert(0, file);
        self.recent.truncate(10);
        self.save_recent();
        self.close();
    }

    // -----------------------------------------------------------------------
    // Icon lookup and GL texture upload
    // -----------------------------------------------------------------------

    fn icon_path(name: &str) -> Option<PathBuf> {
        if name.is_empty() {
            return None;
        }
        if name.starts_with('/') {
            return Some(PathBuf::from(name));
        }
        let home = env::var_os("HOME").map(PathBuf::from);
        if name.contains('.') {
            let mut bases = Vec::new();
            if let Some(home) = &home {
                bases.push(home.join(".local/share/icons").join(name));
            }
            bases.push(PathBuf::from("/usr/local/share/icons").join(name));
            bases.push(PathBuf::from("/usr/share/icons").join(name));
            bases.push(PathBuf::from("/usr/share/pixmaps").join(name));
            for p in bases {
                if p.exists() {
                    return Some(p);
                }
            }
        }
        const SIZES: &[&str] = &[
            "scalable", "512x512", "384x384", "256x256", "192x192", "128x128", "96x96", "64x64",
            "48x48", "32x32", "24x24", "22x22", "16x16", "512", "384", "256", "192", "128", "96",
            "64", "48", "32", "24", "22", "16",
        ];
        const EXTS: &[&str] = &["png", "svg", "xpm"];
        let mut theme_bases = Vec::new();
        if let Some(home) = &home {
            theme_bases.push(home.join(".local/share/icons"));
        }
        theme_bases.push(PathBuf::from("/usr/local/share/icons"));
        theme_bases.push(PathBuf::from("/usr/share/icons"));
        for base in theme_bases {
            let Ok(themes) = fs::read_dir(&base) else {
                continue;
            };
            for theme in themes.flatten() {
                let tname = theme.file_name().to_string_lossy().into_owned();
                if tname.starts_with('.') {
                    continue;
                }
                for size in SIZES {
                    for ext in EXTS {
                        let p = theme
                            .path()
                            .join(size)
                            .join("apps")
                            .join(format!("{name}.{ext}"));
                        if p.exists() {
                            return Some(p);
                        }
                    }
                }
            }
        }
        for ext in EXTS {
            let p = PathBuf::from("/usr/share/pixmaps").join(format!("{name}.{ext}"));
            if p.exists() {
                return Some(p);
            }
        }
        None
    }

    /// Decodes and uploads at most one visible icon per call, like dwm's
    /// `finder_load_next_icon()`. Theme lookup and image decoding are slow
    /// enough to delay a frame when done for every row at once; one icon per
    /// event-loop pass keeps the popup responsive while it fills in.
    ///
    /// Returns true when an icon was attempted, so the caller keeps the pending
    /// flag set until a pass finds nothing left to load.
    fn load_next_icon(&mut self) -> bool {
        let Some(gl) = self.gl.as_mut() else {
            return true;
        };
        gl.pbuffer.make_current().ok();
        let first = self.scroll_visual.max(0.0) as usize;
        let last = (self.scroll_visual + FINDER_ROWS as f64 + 1.0).ceil() as usize;
        for i in first..last.min(self.visible) {
            let idx = self.order[i];
            if self.apps[idx].icon_loaded {
                continue;
            }
            self.apps[idx].icon_loaded = true;
            let Some(path) = Self::icon_path(&self.apps[idx].icon_name) else {
                return true;
            };
            let Ok(img) = image::open(&path) else {
                return true;
            };
            // dwm scales icons to FINDER_ICON_SIZE before uploading them.
            // Uploading a larger source and letting GL scale it with LINEAR
            // produces the soft, blurred icons the port currently shows.
            let img = img.resize_exact(
                ICON_SIZE as u32,
                ICON_SIZE as u32,
                image::imageops::FilterType::Lanczos3,
            );
            let rgba = img.to_rgba8();
            let (w, h) = rgba.dimensions();
            unsafe {
                let mut tex = 0;
                gl::GenTextures(1, &mut tex);
                if tex != 0 {
                    gl::BindTexture(gl::TEXTURE_2D, tex);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MIN_FILTER, gl::LINEAR as i32);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MAG_FILTER, gl::LINEAR as i32);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_WRAP_S, gl::CLAMP_TO_EDGE as i32);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_WRAP_T, gl::CLAMP_TO_EDGE as i32);
                    gl::TexImage2D(
                        gl::TEXTURE_2D,
                        0,
                        gl::RGBA as i32,
                        w as i32,
                        h as i32,
                        0,
                        gl::RGBA,
                        gl::UNSIGNED_BYTE,
                        rgba.as_raw().as_ptr() as *const _,
                    );
                    self.apps[idx].icon_tex = tex;
                    self.bump_content_epoch();
                }
            }
            return true;
        }
        false
    }

    // -----------------------------------------------------------------------
    // Open / close and state transitions
    // -----------------------------------------------------------------------

    pub fn open(&mut self) {
        if self.active {
            return;
        }
        self.active = true;
        self.query.clear();
        self.cursor = 0;
        self.view_start = 0;
        self.selected = 0;
        self.scroll = 0;
        self.scroll_visual = 0.0;
        self.scroll_started = Instant::now();
        self.cursor_base = Instant::now();
        self.cursor_visible = true;
        self.math_result = None;
        self.math_help = false;
        self.math_started = None;
        self.translate_active = false;
        self.translate_result.clear();
        self.translate_started = None;
        self.translate_pending = false;
        self.translate_due = None;
        self.translate_target_en = false;
        self.translate_outgoing.clear();
        self.translate_outgoing_started = None;
        self.glow_started = None;
        self.glow_from = 0.0;
        self.glow_fade_started = None;
        self.glow_fade_from = 0.0;
        self.query_pose_initialized = false;
        self.query_pose_waiting = false;
        self.query_pose = 0.0;
        self.query_pose_from = 0.0;
        self.query_pose_to = 0.0;
        self.query_pose_started = Instant::now();
        self.ocr_mode = false;
        self.filter.clear();
        self.filter_started = None;
        self.filter_display_rows = 0;
        self.filter_animating = false;
        self.net.cancel();
        self.apps.clear();
        self.visible = 0;
        self.order.clear();
        self.loading = true;
        self.initial_background_presented = false;
        self.presented = (0, 0, 0, 0, 0);
        self.last_clock_text.clear();
        self.frame_cache_valid = false;
        self.cached_caret = None;
        self.dirty = true;
    }

    pub fn close(&mut self) {
        if !self.active {
            return;
        }
        self.active = false;
        self.net.cancel();
        self.initial_background_presented = false;
        self.translate_active = false;
        self.translate_result.clear();
        self.translate_started = None;
        self.translate_pending = false;
        self.translate_due = None;
        self.translate_outgoing.clear();
        self.translate_outgoing_started = None;
        self.glow_started = None;
        self.glow_fade_started = None;
        self.query_pose_initialized = false;
        self.query.clear();
        self.cursor = 0;
        self.view_start = 0;
        self.selected = 0;
        self.scroll = 0;
        self.scroll_visual = 0.0;
        self.math_result = None;
        self.math_help = false;
        self.math_started = None;
        self.filter.clear();
        self.filter_started = None;
        self.filter_display_rows = 0;
        self.filter_animating = false;
        self.visible = 0;
        self.ocr_mode = false;
        self.marker_row = 0;
        self.frame_cache_valid = false;
        self.cached_caret = None;
        self.dirty = true;
    }

    pub fn toggle(&mut self) {
        if self.active {
            self.close();
        } else {
            self.open();
        }
    }

    fn query_has_thai(query: &str) -> bool {
        query
            .chars()
            .any(|ch| ('\u{0e00}'..='\u{0e7f}').contains(&ch))
    }

    fn glow_pulse(&self, now: Instant) -> f32 {
        // A recorded fade starts from the pulse value captured by stop_glow(),
        // so it stays visible after translate_pending is cleared.
        if let Some(fade_started) = self.glow_fade_started {
            let p = (now.saturating_duration_since(fade_started).as_secs_f32()
                / GLOW_FADE.as_secs_f32())
            .clamp(0.0, 1.0);
            return self.glow_fade_from * (1.0 - p * p * (3.0 - 2.0 * p));
        }
        if !self.translate_pending {
            return 0.0;
        }
        let Some(started) = self.glow_started else {
            return 0.0;
        };
        if now < started {
            return 0.0;
        }
        let phase = now.duration_since(started).as_secs_f64() * (2.0 * std::f64::consts::PI)
            / GLOW_PERIOD_MS
            * 1000.0;
        (0.5 - 0.5 * phase.cos()) as f32
    }

    /// Whether the pulse or its fade still needs 30 fps frames.
    fn glow_animating(&self) -> bool {
        (self.translate_pending && self.glow_started.is_some()) || self.glow_fade_started.is_some()
    }

    /// Time bucket for the animated glow. Unlike `anim_step` this is not
    /// clamped: dwm keeps pulsing for as long as the translation is pending,
    /// which can outlast one 1400 ms period.
    fn glow_step(started: Option<Instant>, now: Instant) -> u64 {
        started
            .map(|s| (now.saturating_duration_since(s).as_millis() / GLOW_TICK.as_millis()) as u64)
            .unwrap_or(u64::MAX)
    }

    fn stop_glow(&mut self, now: Instant) {
        if !self.translate_pending || self.glow_started.is_none() {
            return;
        }
        self.glow_fade_from = self.glow_pulse(now);
        self.glow_fade_started = Some(now);
    }

    /// Called when the debounce expires and the translation worker actually
    /// starts. dwm leaves `finder_translate_started_ms` untouched here, so the
    /// same pulse continues across the debounce boundary. Restarting it made
    /// the first half-cycle jump back to 0% at 500 ms.
    fn translation_worker_started(&mut self) {
        self.translate_pending = true;
    }

    /// Cancel translation and keep the last result as an outgoing row, exactly
    /// like dwm's `finder_translation_cancel`.
    fn translation_cancel(&mut self) {
        let now = Instant::now();
        self.stop_glow(now);
        if self.translate_active && !self.translate_result.is_empty() {
            self.translate_outgoing = std::mem::take(&mut self.translate_result);
            self.translate_outgoing_started = Some(now);
        }
        self.net.cancel();
        self.translate_active = false;
        self.translate_pending = false;
        self.translate_due = None;
        self.translate_result.clear();
        self.translate_started = None;
        self.glow_started = None;
    }

    fn translation_update(&mut self) {
        self.translation_cancel();
        if !self.active
            || self.math_result.is_some()
            || self.math_help
            || finder_math::is_math_expression(self.query.trim())
            || self.query.is_empty()
            || (!self.ocr_mode && self.visible != 0)
        {
            return;
        }
        let now = Instant::now();
        self.translate_active = true;
        self.translate_pending = true;
        self.translate_target_en = Self::query_has_thai(&self.query);
        self.glow_from = 0.0;
        self.glow_started = Some(now);
        self.glow_fade_started = None;
        self.glow_fade_from = 0.0;
        self.translate_started = Some(now);
        self.translate_due = Some(now + TRANSLATE_DEBOUNCE);
    }

    /// Only a pending translation keeps the enlarged waiting query. Math is
    /// evaluated synchronously, so its result uses the same settled query band
    /// and tight result row as a finished translation.
    fn query_is_waiting(&self) -> bool {
        self.translate_pending
    }

    /// Smoothly grows the query band/letterboxing while a calculation or
    /// translation is pending, matching dwm's `finder_query_pose_update`.
    fn query_pose_update(&mut self, now: Instant) -> f32 {
        let waiting = self.query_is_waiting();
        if !self.query_pose_initialized {
            self.query_pose_initialized = true;
            self.query_pose_waiting = waiting;
            self.query_pose_from = 0.0;
            self.query_pose_to = if waiting { 1.0 } else { 0.0 };
            self.query_pose = 0.0;
            self.query_pose_started = now;
        } else {
            if waiting != self.query_pose_waiting {
                self.query_pose_waiting = waiting;
                self.query_pose_from = self.query_pose;
                self.query_pose_to = if waiting { 1.0 } else { 0.0 };
                self.query_pose_started = now;
            }
            let p = (now
                .saturating_duration_since(self.query_pose_started)
                .as_secs_f32()
                / QUERY_POSE.as_secs_f32())
            .clamp(0.0, 1.0);
            let eased = p * p * (3.0 - 2.0 * p);
            self.query_pose =
                self.query_pose_from + (self.query_pose_to - self.query_pose_from) * eased;
        }
        self.query_pose
    }

    // -----------------------------------------------------------------------
    // Input
    // -----------------------------------------------------------------------

    pub(crate) fn key_char(sym: u32, state: u16) -> Option<char> {
        const SHIFT: u16 = 1;
        // Xkb can report function/modifier keys with a Unicode keysym such as
        // 0x0100ffe1 (Shift_L) or 0x0100ff0d (Enter). Normalize those back to
        // their code point before deciding whether they are printable text.
        let sym = if (0x01000000..=0x0110ffff).contains(&sym) {
            sym & 0x00ffffff
        } else {
            sym
        };
        if sym > 0x10ffff {
            return None;
        }
        if (0x20..=0x7e).contains(&sym) {
            let ch = char::from_u32(sym)?;
            if state & SHIFT == 0 {
                return Some(ch);
            }
            if ch.is_ascii_lowercase() {
                return ch.to_ascii_uppercase().into();
            }
            // XLookupString maps Shift+<punctuation> to the upper symbol on a
            // US layout. Reproduce that for the keys used by the math helper.
            let shifted = match ch {
                '`' => '~',
                '1' => '!',
                '2' => '@',
                '3' => '#',
                '4' => '$',
                '5' => '%',
                '6' => '^',
                '7' => '&',
                '8' => '*',
                '9' => '(',
                '0' => ')',
                '-' => '_',
                '=' => '+',
                '[' => '{',
                ']' => '}',
                '\\' => '|',
                ';' => ':',
                '\'' => '"',
                ',' => '<',
                '.' => '>',
                '/' => '?',
                _ => ch,
            };
            return Some(shifted);
        }
        if (0xffb0..=0xffb9).contains(&sym) {
            return char::from_u32('0' as u32 + (sym - 0xffb0)).into();
        }
        // X11 reserves 0xff00..=0xffff for modifiers, function keys and other
        // non-printing keysyms (0xffe1 is Shift_L, not a fullwidth pound sign).
        if (0xff00..=0xffff).contains(&sym) {
            return None;
        }
        char::from_u32(sym).filter(|ch| !ch.is_control())
    }

    fn cursor_prev(s: &str, mut p: usize) -> usize {
        if p == 0 {
            return 0;
        }
        p -= 1;
        while p > 0 && s.as_bytes()[p] & 0xc0 == 0x80 {
            p -= 1;
        }
        p
    }

    fn cursor_next(s: &str, p: usize) -> usize {
        let mut p = (p + 1).min(s.len());
        while p < s.len() && s.as_bytes()[p] & 0xc0 == 0x80 {
            p += 1;
        }
        p
    }

    pub fn keypress(&mut self, sym: u32, state: u16) -> bool {
        if !self.active {
            return false;
        }
        match sym {
            XK_Escape => {
                self.close();
                return true;
            }
            XK_Return | XK_KP_Enter => {
                self.launch();
                return true;
            }
            XK_Up => {
                self.selected = self.selected.saturating_sub(1);
                self.ensure_selection_visible();
                self.dirty = true;
                return true;
            }
            XK_Down => {
                if self.selected + 1 < self.visible {
                    self.selected += 1;
                }
                self.ensure_selection_visible();
                self.dirty = true;
                return true;
            }
            XK_Left => {
                let new = Self::cursor_prev(&self.query, self.cursor);
                if new != self.cursor {
                    self.cursor = new;
                    self.cursor_base = Instant::now();
                    self.dirty = true;
                }
                return true;
            }
            XK_Right => {
                let new = Self::cursor_next(&self.query, self.cursor);
                if new != self.cursor {
                    self.cursor = new;
                    self.cursor_base = Instant::now();
                    self.dirty = true;
                }
                return true;
            }
            XK_Home => {
                self.cursor = 0;
                self.cursor_base = Instant::now();
                self.dirty = true;
                return true;
            }
            XK_End => {
                self.cursor = self.query.len();
                self.cursor_base = Instant::now();
                self.dirty = true;
                return true;
            }
            XK_BackSpace => {
                if self.cursor > 0 {
                    let prev = Self::cursor_prev(&self.query, self.cursor);
                    self.query.replace_range(prev..self.cursor, "");
                    self.cursor = prev;
                    self.query_changed();
                }
                return true;
            }
            XK_Delete => {
                if self.cursor < self.query.len() {
                    let next = Self::cursor_next(&self.query, self.cursor);
                    self.query.replace_range(self.cursor..next, "");
                    self.query_changed();
                }
                return true;
            }
            _ => {}
        }
        if let Some(ch) = Self::key_char(sym, state)
            && self.query.len() + ch.len_utf8() < MAX_QUERY
        {
            self.query.insert(self.cursor, ch);
            self.cursor += ch.len_utf8();
            self.query_changed();
        }
        true
    }

    fn query_changed(&mut self) {
        self.filter_prepare();
        let previous_math = self.math_result.clone();
        let previous_help = self.math_help;
        let trimmed = self.query.trim_end().trim_end_matches('=');
        if trimmed.eq_ignore_ascii_case("math") {
            self.math_help = true;
            self.math_result = None;
        } else {
            self.math_help = false;
            self.math_result = finder_math::evaluate(trimmed);
        }
        let now = Instant::now();
        let math_changed = self.math_result.as_deref() != previous_math.as_deref()
            || self.math_help != previous_help;
        let math_active = self.math_result.is_some() || self.math_help;
        self.math_started = if !math_active {
            None
        } else if math_changed {
            Some(now)
        } else {
            self.math_started
        };
        self.rank();
        self.selected = 0;
        self.filter_start();
        self.translation_update();
        self.cursor_base = Instant::now();
        self.cursor_visible = true;
        self.dirty = true;
        self.icons_pending = true;
    }

    fn ensure_selection_visible(&mut self) {
        let max_scroll = self.visible.saturating_sub(FINDER_ROWS);
        if self.selected < self.scroll {
            self.set_scroll(self.selected);
        } else if self.selected >= self.scroll + FINDER_ROWS {
            self.set_scroll(self.selected - FINDER_ROWS + 1);
        }
        let _ = max_scroll;
    }

    pub fn buttonpress(&mut self, detail: u8, y: i32, bh: i32) -> bool {
        if !self.active {
            return false;
        }
        match detail {
            4 => {
                self.set_scroll(self.scroll.saturating_sub(1));
                self.selected = self.selected.saturating_sub(1).max(self.scroll);
                self.dirty = true;
                self.icons_pending = true;
            }
            5 => {
                self.set_scroll(self.scroll + 1);
                self.selected = (self.selected + 1).min(self.scroll + FINDER_ROWS - 1);
                self.dirty = true;
                self.icons_pending = true;
            }
            1 => {
                let row = y.div_euclid(bh.max(1));
                if row > 0 && row < self.display_rows() as i32 {
                    self.selected = (self.scroll_visual + row as f64 - 1.0).max(0.0) as usize;
                    self.launch();
                }
            }
            _ => {}
        }
        true
    }

    pub fn motion(&mut self, root_y: i32, bar_y: i32, bh: i32) -> bool {
        if !self.active || self.math_result.is_some() || self.math_help {
            return false;
        }
        let row = (root_y - bar_y).div_euclid(bh.max(1));
        if row <= 0 || row >= self.display_rows() as i32 {
            return false;
        }
        let target = (self.scroll_visual + row as f64 - 1.0).max(0.0) as usize;
        if target != self.selected {
            self.selected = target;
            self.dirty = true;
        }
        true
    }

    // -----------------------------------------------------------------------
    // Animation ticks
    // -----------------------------------------------------------------------

    fn set_scroll(&mut self, value: usize) {
        let max = self.visible.saturating_sub(FINDER_ROWS);
        let value = value.min(max);
        if value == self.scroll {
            return;
        }
        if self.filter_animating {
            self.filter_animating = false;
            self.filter.clear();
        }
        let was_moving = (self.scroll_visual - self.scroll as f64).abs() >= 0.001;
        self.scroll = value;
        if !was_moving {
            self.scroll_started = Instant::now();
        }
        self.dirty = true;
    }

    fn ensure_filter_slots(&mut self) {
        let len = self.apps.len();
        if self.filter.len() != len {
            self.filter.resize(len, FilterAnim::default());
        }
        macro_rules! resize_slot {
            ($values:expr, $fill:expr) => {{
                let values = &mut $values;
                if values.len() != len {
                    values.resize(len, $fill);
                }
            }};
        }
        resize_slot!(self.filter_start_present, false);
        resize_slot!(self.filter_start_y, 0.0);
        resize_slot!(self.filter_start_alpha, 0.0);
        resize_slot!(self.filter_start_scale_x, 1.0);
        resize_slot!(self.filter_start_scale_y, 1.0);
        resize_slot!(self.filter_start_blur, 0.0);
    }

    fn filter_progress(started: Option<Instant>) -> f32 {
        let Some(started) = started else {
            return 1.0;
        };
        (started.elapsed().as_secs_f32() / FILTER_ANIM.as_secs_f32()).clamp(0.0, 1.0)
    }

    fn filter_eval(anim: &FilterAnim, progress: f32) -> (f32, f32, f32, f32, f32) {
        let move_ease = 1.0 - (1.0 - progress).powi(3);
        let alpha_p = ((progress * FILTER_ANIM.as_secs_f32() * 1000.0 - FILTER_ALPHA_DELAY_MS)
            / (FILTER_ANIM.as_secs_f32() * 1000.0 - FILTER_ALPHA_DELAY_MS))
            .clamp(0.0, 1.0);
        let alpha_ease = alpha_p * alpha_p * (3.0 - 2.0 * alpha_p);
        let eased = progress * progress * (3.0 - 2.0 * progress);
        let mix = |a: f32, b: f32, t: f32| a + (b - a) * t;
        (
            anim.from_y + (anim.to_y - anim.from_y) * move_ease,
            mix(anim.from_alpha, anim.to_alpha, alpha_ease),
            mix(anim.from_scale_x, anim.to_scale_x, eased),
            mix(anim.from_scale_y, anim.to_scale_y, eased),
            mix(anim.from_blur, anim.to_blur, eased),
        )
    }

    fn capture_filter_pose(&mut self, index: usize, pose: (f32, f32, f32, f32, f32)) {
        let (y, alpha, scale_x, scale_y, blur) = pose;
        if index >= self.apps.len() || alpha <= 0.001 || !(-1.0..=FINDER_ROWS as f32).contains(&y) {
            return;
        }
        self.filter_start_present[index] = true;
        self.filter_start_y[index] = y;
        self.filter_start_alpha[index] = alpha;
        self.filter_start_scale_x[index] = scale_x;
        self.filter_start_scale_y[index] = scale_y;
        self.filter_start_blur[index] = blur;
    }

    /// Sample every row that is currently on screen, including outgoing rows
    /// from an in-flight transition, before reranking the edited query.
    fn filter_prepare(&mut self) {
        self.ensure_filter_slots();
        let progress = Self::filter_progress(self.filter_started);
        for values in &mut self.filter_start_present {
            *values = false;
        }
        let animating = self.filter_animating;
        for index in 0..self.filter.len() {
            let anim = self.filter[index];
            if !animating || !anim.active || !anim.outgoing {
                continue;
            }
            let pose = Self::filter_eval(&anim, progress);
            self.capture_filter_pose(index, pose);
        }
        for rank in 0..self.visible.min(self.order.len()) {
            let index = self.order[rank];
            let pose = if animating && self.filter.get(index).is_some_and(|a| a.active) {
                Self::filter_eval(&self.filter[index], progress)
            } else {
                let y = rank as f32 - self.scroll_visual as f32;
                (y, 1.0, 1.0, 1.0, 0.0)
            };
            self.capture_filter_pose(index, pose);
        }
        for anim in &mut self.filter {
            *anim = FilterAnim::default();
        }
        self.filter_started = None;
        self.filter_animating = false;
        self.filter_display_rows = 0;
    }

    /// Retarget the captured poses to the newly ranked list. Apps that dropped
    /// out stay as outgoing rows until their fade completes.
    fn filter_start(&mut self) {
        self.ensure_filter_slots();
        let target_rows = self.visible.min(FINDER_ROWS);
        for rank in 0..target_rows.min(self.order.len()) {
            let index = self.order[rank];
            let present = self.filter_start_present[index];
            self.filter[index] = FilterAnim {
                from_y: if present {
                    self.filter_start_y[index]
                } else {
                    rank as f32 + 0.35
                },
                to_y: rank as f32,
                from_alpha: if present {
                    self.filter_start_alpha[index]
                } else {
                    0.0
                },
                to_alpha: 1.0,
                from_scale_x: if present {
                    self.filter_start_scale_x[index]
                } else {
                    0.9
                },
                to_scale_x: 1.0,
                from_scale_y: if present {
                    self.filter_start_scale_y[index]
                } else {
                    0.7
                },
                to_scale_y: 1.0,
                from_blur: if present {
                    self.filter_start_blur[index]
                } else {
                    FILTER_TEXT_BLUR
                },
                to_blur: 0.0,
                active: true,
                outgoing: false,
            };
        }
        for index in 0..self.filter.len() {
            if self.filter[index].active || !self.filter_start_present[index] {
                continue;
            }
            self.filter[index] = FilterAnim {
                from_y: self.filter_start_y[index],
                to_y: self.filter_start_y[index],
                from_alpha: self.filter_start_alpha[index],
                to_alpha: 0.0,
                from_scale_x: self.filter_start_scale_x[index],
                to_scale_x: 1.1,
                from_scale_y: self.filter_start_scale_y[index],
                to_scale_y: 1.3,
                from_blur: self.filter_start_blur[index],
                to_blur: FILTER_TEXT_BLUR,
                active: true,
                outgoing: true,
            };
        }
        let mut rows = target_rows;
        for anim in &self.filter {
            if anim.active && anim.outgoing {
                let need = (anim.from_y.max(0.0) + 1.0).ceil().max(0.0) as usize;
                rows = rows.max(need.min(FINDER_ROWS));
            }
        }
        self.filter_display_rows = rows;
        self.scroll = 0;
        self.scroll_visual = 0.0;
        self.scroll_started = Instant::now();
        self.filter_started = Some(Instant::now());
        self.filter_animating = true;
    }

    pub fn tick(&mut self) -> Result<bool> {
        if !self.active {
            // OCR starts while Finder is closed. Poll its worker here so the
            // result can open the modal popup with the recognized text as the
            // initial query, matching dwm's finder_ocr_finish().
            if !self.ocr_mode {
                return Ok(false);
            }
            if let Some(result) = self.net.poll() {
                match result {
                    NetResult::Ocr(text) => {
                        self.open();
                        self.apply_ocr_text(text);
                    }
                    NetResult::Error(_) | NetResult::Translate(_) => {
                        self.ocr_mode = false;
                    }
                }
                self.dirty = true;
            }
            return Ok(self.dirty);
        }
        if self.loading {
            if self.initial_background_presented {
                self.load_apps();
                self.loading = false;
                self.icons_pending = true;
                self.dirty = true;
            } else {
                // Let draw() present the full-size progressive background
                // first. Scanning .desktop files here would delay that frame
                // and leave the old clock content in the resized window.
                self.dirty = true;
            }
        }
        let now = Instant::now();
        let pose_before = self.query_pose;
        let pose = self.query_pose_update(now);
        if (pose - pose_before).abs() >= 0.001 {
            self.dirty = true;
        }
        if (now - self.cursor_base).as_millis() % CURSOR_BLINK.as_millis() == 0
            || now.duration_since(self.cursor_base) >= CURSOR_BLINK
        {
            let visible =
                ((now - self.cursor_base).as_millis() / CURSOR_BLINK.as_millis()) % 2 == 0;
            if visible != self.cursor_visible {
                self.cursor_visible = visible;
                self.dirty = true;
            }
        }
        if now.duration_since(self.scroll_started) >= SCROLL_TICK
            && (self.scroll_visual - self.scroll as f64).abs() >= 0.001
        {
            let elapsed = now.duration_since(self.scroll_started).as_secs_f64();
            self.scroll_started = now;
            let fraction = 1.0 - (-elapsed / 0.025).exp();
            let delta = self.scroll as f64 - self.scroll_visual;
            self.scroll_visual += delta * fraction;
            if (self.scroll as f64 - self.scroll_visual).abs() < 0.01 {
                self.scroll_visual = self.scroll as f64;
            }
            self.icons_pending = true;
            self.dirty = true;
        }
        if let Some(started) = self.filter_started {
            let p = started.elapsed().as_secs_f32() / FILTER_ANIM.as_secs_f32();
            if p >= 1.0 {
                self.filter_animating = false;
                self.filter_display_rows = 0;
                self.filter_started = None;
                for anim in &mut self.filter {
                    *anim = FilterAnim::default();
                }
            }
            self.dirty = true;
        }
        if let Some(fade_started) = self.glow_fade_started
            && now.saturating_duration_since(fade_started) >= GLOW_FADE
        {
            self.glow_fade_started = None;
            self.glow_fade_from = 0.0;
            self.dirty = true;
        }
        // dwm clears the fading outgoing translation row when its 220 ms
        // animation ends. Without this the retired result keeps its line count
        // and the popup never shrinks back to the typed-query height.
        if let Some(started) = self.translate_outgoing_started
            && now.saturating_duration_since(started) >= RESULT_FADE
        {
            self.translate_outgoing.clear();
            self.translate_outgoing_started = None;
            self.dirty = true;
        }
        if let Some(due) = self.translate_due
            && now >= due
        {
            self.translate_due = None;
            let text = self.query.clone();
            let target_en = self.translate_target_en;
            if !text.is_empty() && self.net.translate(&text, target_en).is_ok() {
                self.translation_worker_started();
            } else {
                self.translate_pending = false;
                self.translate_started = Some(now);
            }
            self.dirty = true;
        }
        if let Some(result) = self.net.poll() {
            self.stop_glow(now);
            self.translate_pending = false;
            match result {
                NetResult::Translate(text) => {
                    self.translate_result = text;
                    self.translate_started = Some(now);
                }
                NetResult::Ocr(text) => {
                    self.apply_ocr_text(text);
                }
                NetResult::Error(message) => {
                    if self.ocr_mode {
                        self.ocr_mode = false;
                    } else {
                        self.translate_result = message;
                        self.translate_started = Some(now);
                    }
                }
            }
            self.dirty = true;
        }
        if self.icons_pending {
            if self.gl.is_some() {
                if self.load_next_icon() {
                    self.dirty = true;
                } else {
                    self.icons_pending = false;
                }
            } else {
                // The first tick after open can happen before draw() creates
                // the GL pbuffer. Keep the load pending so the first visible
                // frame still gets its icons instead of waiting for a scroll.
                self.dirty = true;
            }
            self.frame_cache_valid = false;
        }
        // The pulse is purely time-driven: nothing in the mutable state changes
        // between wakeups, so a start/end step comparison inside this pass can
        // never see it. Mark the frame dirty on every tick while it is alive;
        // next_tick() paces those ticks at 30 ms.
        if self.glow_animating() {
            self.dirty = true;
        }
        Ok(self.dirty)
    }

    /// Next wakeup needed by Finder's own animations. dwm uses 0 ms while a
    /// frame or network result is pending, 10 ms for scroll/filter/pose easing,
    /// 30 ms for the slower glow and result fades, and 500 ms for the caret.
    pub fn next_tick(&self, now: Instant) -> Instant {
        if !self.active {
            return now + CURSOR_BLINK;
        }
        if self.dirty || self.loading {
            return now;
        }
        // Deadlines combine instead of short-circuiting. The old early return
        // on `translate_due` skipped the glow deadline during the 500 ms
        // debounce, so the pulse only advanced on caret blinks (~1 fps).
        let mut next = now + CURSOR_BLINK;
        if let Some(due) = self.translate_due {
            next = next.min(due.max(now));
        }
        if self.net.is_busy() {
            next = next.min(now + NET_POLL);
        }
        if self.glow_animating() {
            next = next.min(now + GLOW_TICK);
        }
        let scrolling = (self.scroll_visual - self.scroll as f64).abs() >= 0.001;
        let pose_moving =
            self.query_pose_initialized && (self.query_pose - self.query_pose_to).abs() >= 0.001;
        if self.filter_animating || scrolling || pose_moving {
            next = next.min(now + SCROLL_TICK);
        }
        let fading = [
            self.math_started,
            self.translate_started,
            self.translate_outgoing_started,
        ]
        .into_iter()
        .flatten()
        .any(|started| started.elapsed() < RESULT_FADE);
        if self.translate_pending || fading || self.glow_fade_started.is_some() {
            next = next.min(now + GLOW_TICK);
        }
        next
    }

    pub fn ocr(&mut self, dpy: *mut xlib::Display) -> Result<()> {
        if self.active {
            return Ok(());
        }
        self.ocr_mode = true;
        if let Err(err) = self.net.ocr_region(dpy) {
            self.ocr_mode = false;
            return Err(err.into());
        }
        Ok(())
    }

    /// Clears the pending-OCR marker when the region grab or capture fails.
    pub fn clear_ocr(&mut self) {
        self.ocr_mode = false;
    }

    /// OCR replaces the query, then normal matching and translation rules take
    /// over so the recognized text behaves exactly like typed text.
    fn apply_ocr_text(&mut self, text: String) {
        self.filter_prepare();
        self.ocr_mode = false;
        self.query = text;
        self.cursor = self.query.len();
        self.view_start = 0;
        self.math_result = None;
        self.math_help = false;
        self.math_started = None;
        self.rank();
        self.selected = 0;
        self.filter_start();
        self.translation_update();
        self.cursor_base = Instant::now();
        self.cursor_visible = true;
        self.icons_pending = true;
    }

    // -----------------------------------------------------------------------
    // Layout and rendering
    // -----------------------------------------------------------------------

    pub fn display_rows(&self) -> usize {
        // The first frame is painted before desktop discovery, so reserve the
        // normal app-list height while `loading`. Otherwise the popup would
        // open at clock height and only grow once the names arrive, which is
        // exactly the stale clock-sized patch the background must avoid.
        if self.loading {
            return 1 + FINDER_ROWS;
        }
        if self.math_result.is_some() {
            return 2;
        }
        if self.math_help {
            return 1 + HELP.len();
        }
        let rows = self.visible.saturating_sub(self.scroll);
        let mut app_rows = if self.translate_active {
            0
        } else {
            rows.min(FINDER_ROWS)
        };
        if self.translate_active {
            let width = self.popup_width();
            app_rows = app_rows
                .max(self.result_line_count(&self.translate_result, width))
                .max(self.result_line_count(&self.translate_outgoing, width));
        }
        if self.filter_animating {
            app_rows = app_rows.max(self.filter_display_rows);
        }
        1 + app_rows
    }

    fn math_result_text(result: &str) -> String {
        format!("= {result}")
    }

    /// Text drawn in the result row. Math keeps its `=` prefix, but every
    /// result now uses the same width rules, wrapping and result font.
    fn result_texts(&self) -> Vec<String> {
        let mut texts = Vec::new();
        if let Some(result) = &self.math_result {
            texts.push(Self::math_result_text(result));
        }
        texts.push(self.translate_result.clone());
        texts.push(self.translate_outgoing.clone());
        texts
    }

    /// Widens the popup for long result strings and a pending translated query.
    /// Use the GL font's measured advances once they exist; before the first
    /// frame the fallback keeps the same conservative layout.
    pub fn popup_width(&self) -> u32 {
        let mut width = FINDER_WIDTH.max(1) as u32;
        let result_char = self.result_char_width() as usize;
        for text in self.result_texts() {
            for line in Self::wrap_chars(&text, (width as usize / result_char).max(1), 32) {
                let w = line.chars().count() as u32 * result_char as u32 + 2 * EDGE as u32;
                width = width.max(w);
            }
        }
        if self.translate_pending {
            let query_char = self.query_char_width() as u32;
            width = width.max(self.query.chars().count() as u32 * query_char + 2 * EDGE as u32);
        }
        width.min(550)
    }

    pub fn popup_size(&self, bh: u32) -> (u32, u32) {
        let rows = self.display_rows();
        let w = self.popup_width().max(1);
        let bh = bh.max(1);
        let line_h = self.result_line_height(bh);
        // Math and translation both draw one settled query row followed by
        // tight result-font lines, so they must share this height formula.
        let result_mode = self.translate_active || self.math_result.is_some();
        let h = if result_mode {
            bh + line_h * rows.saturating_sub(1) as u32
        } else {
            bh * rows as u32
        } + EDGE as u32;
        (w, h)
    }

    fn result_line_height(&self, bh: u32) -> u32 {
        // `finder_result_line_height()` uses the result GL font's height; the
        // bar height is only the fallback before the first GL frame.
        self.gl
            .as_ref()
            .map(|gl| (gl.result_font.height - 5).max(1) as u32)
            .unwrap_or_else(|| (bh as i32 - 5).max(1) as u32)
    }

    fn result_char_width(&self) -> usize {
        self.gl
            .as_ref()
            .map(|gl| gl.result_char_width.max(1) as usize)
            .unwrap_or(9)
    }

    fn query_char_width(&self) -> u32 {
        self.gl
            .as_ref()
            .map(|gl| gl.query_char_width.max(1))
            .unwrap_or(14)
    }

    fn result_line_width(width: u32) -> i32 {
        (width as i32 - 2 * EDGE).max(1)
    }

    fn result_line_count(&self, text: &str, width: u32) -> usize {
        if text.is_empty() {
            return 0;
        }
        let char_width = self.result_char_width();
        Self::wrap_chars(
            text,
            (Self::result_line_width(width) as usize / char_width).max(1),
            32,
        )
        .len()
    }

    fn wrap_chars(text: &str, max_chars: usize, max_lines: usize) -> Vec<String> {
        Self::wrap_lines(text, max_chars.max(1) as u32, max_lines, |s| {
            s.chars().count() as u32
        })
    }

    unsafe fn fc_string(pattern: *const FcPattern, object: &str) -> Option<String> {
        let object = CString::new(object).ok()?;
        let mut value: *mut c_char = ptr::null_mut();
        let found = unsafe { FcPatternGetString(pattern, object.as_ptr(), 0, &mut value) } == 0;
        if !found || value.is_null() {
            return None;
        }
        Some(
            unsafe { CStr::from_ptr(value) }
                .to_string_lossy()
                .into_owned(),
        )
    }

    unsafe fn fc_int(pattern: *const FcPattern, object: &str) -> Option<i32> {
        let object = CString::new(object).ok()?;
        let mut value = 0;
        let found = unsafe { FcPatternGetInteger(pattern, object.as_ptr(), 0, &mut value) } == 0;
        found.then_some(value)
    }

    unsafe fn fc_double(pattern: *const FcPattern, object: &str) -> Option<f64> {
        let object = CString::new(object).ok()?;
        let mut value = 0.0;
        let found = unsafe { FcPatternGetDouble(pattern, object.as_ptr(), 0, &mut value) } == 0;
        found.then_some(value)
    }

    /// dwm.c 17106-17117: one result font at 16 pt, then every configured
    /// font with its FC_SIZE replaced by 16.
    fn resized_font_name(name: &str, size: f64) -> Option<String> {
        let name = CString::new(name).ok()?;
        unsafe {
            let pattern = FcNameParse(name.as_ptr());
            if pattern.is_null() {
                return None;
            }
            FcPatternDel(pattern, c"size".as_ptr());
            FcPatternAddDouble(pattern, c"size".as_ptr(), size);
            let resized = FcNameUnparse(pattern);
            FcPatternDestroy(pattern);
            if resized.is_null() {
                return None;
            }
            let text = CStr::from_ptr(resized).to_string_lossy().into_owned();
            FcStrFree(resized);
            Some(text)
        }
    }

    /// Resolve the configured Xft fontset into the file/index/pixel-size specs
    /// used by dwm's `gl_font_create_scaled`, plus its Xft height and LCD order.
    fn font_bundle(
        dpy: *mut xlib::Display,
        screen: i32,
        size: Option<f64>,
        scale: f64,
    ) -> Result<FontBundle> {
        let scale = if scale > 0.0 { scale } else { 1.0 };
        let names: Vec<String> = if let Some(size) = size {
            let mut names = vec![RESULT_FONT_NAME.to_string()];
            names.extend(
                FONTS
                    .iter()
                    .filter_map(|name| Self::resized_font_name(name, size)),
            );
            names
        } else {
            FONTS.iter().map(|name| (*name).to_string()).collect()
        };
        let mut lcd_order = match unsafe { xrender::XRenderQuerySubpixelOrder(dpy, screen) } {
            1 => 1,
            2 => 2,
            _ => 0,
        };
        let mut specs = Vec::new();
        let mut height = 0;
        for (i, name) in names.iter().enumerate() {
            let Ok(name) = CString::new(name.as_str()) else {
                continue;
            };
            let xft: *mut XftFont = unsafe { XftFontOpenName(dpy, screen, name.as_ptr()) };
            if xft.is_null() {
                continue;
            }
            let pattern = unsafe { (*xft).pattern };
            let unscaled_h = unsafe { (*xft).ascent + (*xft).descent };
            if i == 0 {
                height = (unscaled_h as f64 * scale).round() as i32;
                if !pattern.is_null() {
                    let order = unsafe { Self::fc_int(pattern, "rgba") }.unwrap_or(0);
                    lcd_order = match order {
                        1 | 2 => order as u8,
                        3 | 4 | 5 => 0,
                        _ => lcd_order,
                    };
                }
            }
            let file = if pattern.is_null() {
                None
            } else {
                unsafe { Self::fc_string(pattern, "file") }
            };
            if let Some(file) = file {
                let index = if pattern.is_null() {
                    0
                } else {
                    unsafe { Self::fc_int(pattern, "index") }.unwrap_or(0)
                };
                let face_size = if pattern.is_null() {
                    unscaled_h as f64
                } else {
                    unsafe { Self::fc_double(pattern, "pixelsize") }
                        .filter(|size| *size > 0.0)
                        .unwrap_or(unscaled_h as f64)
                };
                specs.push(GlFontSpec {
                    file,
                    index,
                    pixel_size: face_size * scale,
                });
            }
            unsafe { XftFontClose(dpy, xft) };
        }
        if specs.is_empty() {
            return Err("no configured Xft font could be resolved for Finder GL text".into());
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

    fn ensure_gl(
        &mut self,
        dpy: *mut xlib::Display,
        screen: i32,
        visual: *mut xlib::Visual,
        w: u32,
        h: u32,
    ) -> Result<()> {
        let need_new = self.gl.is_none();
        if need_new {
            let pbuffer = GlPbuffer::new(dpy, screen, GL_PBUFFER_MAX_WIDTH, GL_PBUFFER_MAX_HEIGHT)?;
            let bloom = Bloom::new()?;
            let surface = GlSurface::new(dpy, visual, w, h)?;
            let main = Self::font_bundle(dpy, screen, None, 1.0)?;
            let query = Self::font_bundle(dpy, screen, None, 1.15)?;
            let result = Self::font_bundle(dpy, screen, Some(16.0), 1.0)?;
            let font = GlFont::new(&main.specs, main.height, main.lcd_order)?;
            let mut query_font = GlFont::new(&query.specs, query.height, query.lcd_order)?;
            let mut result_font = GlFont::new(&result.specs, result.height, result.lcd_order)?;
            let query_char_width = query_font.text_width("M").max(1);
            let result_char_width = result_font.text_width("M").max(1);
            self.gl = Some(GlState {
                font,
                query_font,
                result_font,
                query_char_width,
                result_char_width,
                surface,
                bloom,
                pbuffer,
            });
            self.frame_cache_valid = false;
        }
        let gl = self.gl.as_mut().ok_or("finder GL state is unavailable")?;
        gl.pbuffer.make_current()?;
        gl.surface.resize(w, h)?;
        Ok(())
    }

    fn quad(c: &crate::gl::CompatGl, x: f32, y: f32, w: f32, h: f32, color: (f32, f32, f32, f32)) {
        unsafe {
            gl::Disable(gl::TEXTURE_2D);
            gl::Enable(gl::BLEND);
            gl::BlendFunc(gl::SRC_ALPHA, gl::ONE_MINUS_SRC_ALPHA);
            c.color4f(color.0, color.1, color.2, color.3);
            c.begin(gl::QUADS);
            c.vertex2f(x, y);
            c.vertex2f(x + w, y);
            c.vertex2f(x + w, y + h);
            c.vertex2f(x, y + h);
            c.end();
            gl::Disable(gl::BLEND);
        }
    }

    fn draw_icon(c: &crate::gl::CompatGl, tex: u32, x: i32, y: i32, size: i32, alpha: f32) {
        if tex == 0 {
            return;
        }
        unsafe {
            gl::Enable(gl::TEXTURE_2D);
            gl::Enable(gl::BLEND);
            gl::BlendFuncSeparate(
                gl::SRC_ALPHA,
                gl::ONE_MINUS_SRC_ALPHA,
                gl::ONE,
                gl::ONE_MINUS_SRC_ALPHA,
            );
            gl::BindTexture(gl::TEXTURE_2D, tex);
            c.color4f(1.0, 1.0, 1.0, alpha);
            c.begin(gl::QUADS);
            c.tex_coord2f(0.0, 0.0);
            c.vertex2f(x as f32, y as f32);
            c.tex_coord2f(1.0, 0.0);
            c.vertex2f((x + size) as f32, y as f32);
            c.tex_coord2f(1.0, 1.0);
            c.vertex2f((x + size) as f32, (y + size) as f32);
            c.tex_coord2f(0.0, 1.0);
            c.vertex2f(x as f32, (y + size) as f32);
            c.end();
            gl::BindTexture(gl::TEXTURE_2D, 0);
            gl::Disable(gl::BLEND);
            gl::Disable(gl::TEXTURE_2D);
        }
    }

    /// UTF-8 boundary at which `text` stops fitting in `max_width`, using the
    /// caller's width function. Binary search keeps OCR-sized results cheap.
    fn fit_prefix_end<F>(text: &str, max_width: u32, width: &mut F) -> usize
    where
        F: FnMut(&str) -> u32,
    {
        let boundaries: Vec<usize> = text
            .char_indices()
            .map(|(i, _)| i)
            .chain(std::iter::once(text.len()))
            .collect();
        if boundaries.len() <= 1 {
            return 0;
        }
        if width(text) <= max_width {
            return text.len();
        }
        let mut lo = 0usize;
        let mut hi = boundaries.len() - 1;
        while lo + 1 < hi {
            let mid = lo + (hi - lo) / 2;
            if width(&text[..boundaries[mid]]) <= max_width {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        boundaries[lo]
    }

    /// Word wrapping shared by layout and drawing. Overlong words are split at
    /// UTF-8 boundaries instead of being truncated to themselves forever.
    fn wrap_lines<F>(text: &str, max_width: u32, max_lines: usize, mut width: F) -> Vec<String>
    where
        F: FnMut(&str) -> u32,
    {
        if text.is_empty() || max_width == 0 || max_lines == 0 {
            return Vec::new();
        }
        let mut lines = Vec::new();
        let mut current = String::new();
        for word in text.split_whitespace() {
            let candidate = if current.is_empty() {
                word.to_string()
            } else {
                format!("{current} {word}")
            };
            if width(&candidate) <= max_width {
                current = candidate;
                continue;
            }
            if !current.is_empty() {
                lines.push(std::mem::take(&mut current));
                if lines.len() >= max_lines {
                    return lines;
                }
            }
            let mut remaining = word;
            loop {
                if remaining.is_empty() {
                    current.clear();
                    break;
                }
                if width(remaining) <= max_width {
                    current = remaining.to_string();
                    break;
                }
                let fit = Self::fit_prefix_end(remaining, max_width, &mut width);
                let end = if fit == 0 {
                    remaining.chars().next().map(char::len_utf8).unwrap_or(0)
                } else {
                    fit
                };
                if end == 0 {
                    break;
                }
                lines.push(remaining[..end].to_string());
                if lines.len() >= max_lines {
                    return lines;
                }
                remaining = remaining[end..].trim_start();
            }
        }
        if !current.is_empty() && lines.len() < max_lines {
            lines.push(current);
        }
        lines
    }

    fn wrap_text(font: &mut GlFont, text: &str, max_width: u32, max_lines: usize) -> Vec<String> {
        Self::wrap_lines(text, max_width, max_lines, |s| font.text_width(s))
    }

    /// First UTF-8 boundary from which `query[start..cursor]` fits in `budget`.
    /// Used when the caret has crossed the right edge: it advances `start` by
    /// the smallest amount that brings the caret back into view.
    fn query_view_start_with<F>(query: &str, cursor: usize, budget: i64, mut width: F) -> usize
    where
        F: FnMut(&str) -> i64,
    {
        let mut cursor = cursor.min(query.len());
        while cursor > 0 && !query.is_char_boundary(cursor) {
            cursor -= 1;
        }
        if width(query) <= budget {
            return 0;
        }

        let mut boundaries: Vec<usize> = query[..cursor].char_indices().map(|(i, _)| i).collect();
        boundaries.push(cursor);
        boundaries.dedup();

        let mut low = 0;
        let mut high = boundaries.len() - 1;
        while low < high {
            let mid = low + (high - low) / 2;
            if width(&query[boundaries[mid]..cursor]) <= budget {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        boundaries[low]
    }

    /// Regular text-field scrolling. Keep the existing viewport while the
    /// caret is inside it; shift left only when the caret passes the right
    /// edge, and shift right by one caret step when it passes the left edge.
    fn query_view_update_with<F>(
        query: &str,
        cursor: usize,
        view_start: usize,
        budget: i64,
        mut width: F,
    ) -> usize
    where
        F: FnMut(&str) -> i64,
    {
        let mut cursor = cursor.min(query.len());
        while cursor > 0 && !query.is_char_boundary(cursor) {
            cursor -= 1;
        }
        if width(query) <= budget {
            return 0;
        }

        let mut start = view_start.min(cursor);
        while start > 0 && !query.is_char_boundary(start) {
            start -= 1;
        }
        if width(&query[start..cursor]) > budget {
            return Self::query_view_start_with(query, cursor, budget, width);
        }
        start
    }

    /// Returns the viewport start, the UTF-8 slice that is actually painted,
    /// and the caret offset inside that slice. Using one measured slice for
    /// both drawing and caret layout keeps the caret after the final visible
    /// character when the query is longer than the popup.
    fn query_visible_slice<F>(
        query: &str,
        cursor: usize,
        view_start: usize,
        view_width: u32,
        draw_width: u32,
        mut width: F,
    ) -> (usize, String, usize)
    where
        F: FnMut(&str) -> u32,
    {
        let view_budget = view_width.saturating_sub(4).max(1) as i64;
        let start = Self::query_view_update_with(query, cursor, view_start, view_budget, |text| {
            width(text) as i64
        });
        let suffix = &query[start..];
        let draw_budget = draw_width.saturating_sub(4).max(1);
        let mut visible_end = Self::fit_prefix_end(suffix, draw_budget, &mut |text| width(text));
        if visible_end == 0 && !suffix.is_empty() {
            visible_end = suffix.chars().next().map(char::len_utf8).unwrap_or(0);
        }
        let display = suffix[..visible_end].to_string();
        let mut caret_end = cursor.saturating_sub(start).min(display.len());
        while caret_end > 0 && !display.is_char_boundary(caret_end) {
            caret_end -= 1;
        }
        (start, display, caret_end)
    }

    fn draw_result(
        c: &crate::gl::CompatGl,
        font: &mut GlFont,
        text: &str,
        started: Option<Instant>,
        outgoing: bool,
        color: (f32, f32, f32),
        w: u32,
        h: u32,
        bh: u32,
        max_lines: usize,
    ) {
        let now = Instant::now();
        let progress = started
            .map(|s| {
                ((now.saturating_duration_since(s).as_secs_f32() * 1000.0)
                    / FILTER_ANIM.as_secs_f32()
                    / 1000.0)
                    .clamp(0.0, 1.0)
            })
            .unwrap_or(1.0);
        let eased = progress * progress * (3.0 - 2.0 * progress);
        let move_eased = 1.0 - (1.0 - progress).powi(3);
        let alpha = if outgoing { 1.0 - eased } else { eased };
        if alpha <= 0.001 || text.is_empty() {
            return;
        }
        let scale_x = if outgoing {
            1.0 + 0.1 * eased
        } else {
            0.9 + 0.1 * eased
        };
        let scale_y = if outgoing {
            1.0 + 0.3 * eased
        } else {
            0.7 + 0.3 * eased
        };
        let row_y = bh as f32
            + if outgoing {
                0.0
            } else {
                (1.0 - move_eased) * 0.35 * bh as f32
            };
        let result_h = (font.height - 5).max(1) as u32;
        let line_h = font.height.max(1);
        let available = w.saturating_sub(2 * EDGE as u32).max(1);
        let lines = Self::wrap_text(font, text, available, max_lines.max(1));
        for (row, line) in lines.iter().enumerate() {
            let text_w = font.text_width(line);
            let x = EDGE
                + if text_w < available {
                    ((available - text_w) / 2) as i32
                } else {
                    0
                };
            let y = row_y.round() as i32 + row as i32 * result_h as i32;
            let baseline = y + (result_h as i32 - line_h) / 2 + font.ascender();
            let center_y = y as f32 + result_h as f32 / 2.0;
            unsafe {
                c.push_matrix();
                c.translatef(w as f32 / 2.0, center_y, 0.0);
                c.scalef(scale_x, scale_y, 1.0);
                c.translatef(-(w as f32 / 2.0), -center_y, 0.0);
            }
            let _: GlResult = font.draw_text(line, x, baseline, available, color, alpha);
            unsafe {
                c.pop_matrix();
            }
            if y as u32 >= h.saturating_sub(EDGE as u32) {
                break;
            }
        }
    }

    fn draw_app(
        c: &crate::gl::CompatGl,
        gl: &mut GlState,
        index: usize,
        name: &str,
        icon_tex: u32,
        row_y: f64,
        alpha: f32,
        scale_x: f32,
        scale_y: f32,
        blur: f32,
        selected: bool,
        w: u32,
        h: u32,
        bh: u32,
    ) {
        if alpha <= 0.001 || scale_x <= 0.001 || scale_y <= 0.001 {
            return;
        }
        let color = if selected { FG } else { FINDER_TEXT };
        let icon_x = EDGE + CLOCKPAD / 2;
        let text_x = icon_x + ICON_SIZE + ICON_GAP;
        let text_w = w.saturating_sub(text_x as u32 + EDGE as u32).max(1);
        let y = row_y.round() as i32;
        let baseline = y + (bh as i32 - gl.font.height) / 2 + gl.font.ascender();
        let transform = BloomTransform {
            center_y: (row_y + bh as f64 / 2.0) as f32,
            offset_y: 0.0,
            scale_x,
            scale_y,
        };
        if blur > 0.001 && gl.bloom.ready() {
            let _: GlResult<bool> = gl.bloom.render(
                w,
                h,
                blur * (FILTER_IMAGE_BLUR / FILTER_TEXT_BLUR),
                alpha,
                Some(transform),
                || {
                    Self::draw_icon(
                        c,
                        icon_tex,
                        icon_x,
                        y + (bh as i32 - ICON_SIZE) / 2,
                        ICON_SIZE,
                        alpha,
                    )
                },
            );
            let _: GlResult<bool> = gl.bloom.render(w, h, blur, alpha, Some(transform), || {
                let _ = gl
                    .font
                    .draw_text(name, text_x, baseline, text_w, color, 1.0);
            });
            return;
        }
        unsafe {
            c.push_matrix();
            c.translatef(w as f32 / 2.0, (row_y + bh as f64 / 2.0) as f32, 0.0);
            c.scalef(scale_x, scale_y, 1.0);
            c.translatef(-(w as f32 / 2.0), -((row_y + bh as f64 / 2.0) as f32), 0.0);
        }
        Self::draw_icon(
            c,
            icon_tex,
            icon_x,
            y + (bh as i32 - ICON_SIZE) / 2,
            ICON_SIZE,
            alpha,
        );
        let _: GlResult = gl
            .font
            .draw_text(name, text_x, baseline, text_w, color, alpha);
        unsafe {
            c.pop_matrix();
        }
    }

    /// Progress bucket for a time-based effect. Once the effect settles the
    /// value is constant, so an idle Finder keeps a valid GL-frame cache key.
    fn anim_step(started: Option<Instant>, duration: Duration) -> u64 {
        started
            .map(|s| {
                let elapsed = s.elapsed().as_millis().min(duration.as_millis());
                (elapsed / 16) as u64
            })
            .unwrap_or(u64::MAX)
    }

    fn quantize(value: f64) -> i64 {
        (value * 1000.0).round() as i64
    }

    /// Everything that changes the GL-rendered part of the popup. `cursor_visible`
    /// is deliberately absent: the caret is painted with XRender from the cached
    /// rectangle, so a blink never re-runs GL.
    fn frame_key(&self, now: Instant, bh: i32, w: u32, h: u32, clock_text: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        (bh, w, h).hash(&mut hasher);
        self.query.hash(&mut hasher);
        self.cursor.hash(&mut hasher);
        self.view_start.hash(&mut hasher);
        Self::quantize(self.query_pose as f64).hash(&mut hasher);
        self.math_result.hash(&mut hasher);
        self.math_help.hash(&mut hasher);
        Self::anim_step(self.math_started, FILTER_ANIM).hash(&mut hasher);
        self.translate_active.hash(&mut hasher);
        self.translate_pending.hash(&mut hasher);
        self.translate_result.hash(&mut hasher);
        self.translate_outgoing.hash(&mut hasher);
        Self::anim_step(self.translate_started, FILTER_ANIM).hash(&mut hasher);
        Self::anim_step(self.translate_outgoing_started, FILTER_ANIM).hash(&mut hasher);
        self.glow_started.is_some().hash(&mut hasher);
        self.glow_fade_started.is_some().hash(&mut hasher);
        // The pulse phase itself must invalidate the cached GL frame; hashing
        // only the on/off state made it advance at the caret blink rate.
        Self::glow_step(self.glow_started, now).hash(&mut hasher);
        Self::glow_step(self.glow_fade_started, now).hash(&mut hasher);
        self.glow_from.to_bits().hash(&mut hasher);
        self.glow_fade_from.to_bits().hash(&mut hasher);
        self.filter_animating.hash(&mut hasher);
        if self.filter_animating {
            Self::anim_step(self.filter_started, FILTER_ANIM).hash(&mut hasher);
            for anim in &self.filter {
                for value in [
                    anim.from_y,
                    anim.to_y,
                    anim.from_alpha,
                    anim.to_alpha,
                    anim.from_scale_x,
                    anim.to_scale_x,
                    anim.from_scale_y,
                    anim.to_scale_y,
                    anim.from_blur,
                    anim.to_blur,
                ] {
                    value.to_bits().hash(&mut hasher);
                }
                anim.active.hash(&mut hasher);
                anim.outgoing.hash(&mut hasher);
            }
        }
        self.selected.hash(&mut hasher);
        self.visible.hash(&mut hasher);
        // App names, icon textures, rank order and row count are replaced by one
        // epoch. It changes only when those arrays actually change, so an idle
        // frame key stays constant without walking every installed desktop app.
        self.frame_content_epoch.hash(&mut hasher);
        Self::quantize(self.scroll_visual).hash(&mut hasher);
        clock_text.hash(&mut hasher);
        hasher.finish()
    }

    /// Glow transform for the waiting query. It must match the text matrix:
    /// scale around `bh / 2`, then shift down by `6 * query_pose`.
    fn query_bloom_transform(bh: f32, query_pose: f32, query_scale: f32) -> BloomTransform {
        BloomTransform {
            center_y: bh / 2.0,
            offset_y: 6.0 * query_pose,
            scale_x: query_scale,
            scale_y: query_scale,
        }
    }

    /// Converts a pre-transform GL rectangle into final frame coordinates.
    fn transformed_rect(
        rect: (i32, i32, i32, i32),
        scale: f32,
        pose: f32,
        frame: (i32, i32),
    ) -> (i32, i32, i32, i32) {
        let (x, y, w, h) = rect;
        let (frame_w, frame_h) = frame;
        let half_w = frame_w as f32 / 2.0;
        let half_h = frame_h as f32 / 2.0;
        let sx = half_w + scale * (x as f32 - half_w);
        let sy = half_h + 6.0 * pose + scale * (y as f32 - half_h);
        (
            sx.round() as i32,
            sy.round() as i32,
            ((w as f32 * scale).round() as i32).max(1),
            ((h as f32 * scale).round() as i32).max(1),
        )
    }

    /// Lays out the query band and body in the shared drawable, applies dwm's
    /// accelerating 12-stop opacity ramp, and stores the result in `base_pixmap`.
    /// Shared by the immediate background-only frame and the full GL frame.
    fn paint_background(
        &self,
        drw: &Drw,
        visual: *mut xlib::Visual,
        w: u32,
        h: u32,
        bh: i32,
        query_pose: f32,
    ) -> Result<()> {
        let border = CLRBORDER;
        let border_rgb = [
            ((border >> 16) & 0xff) as f32 / 255.0,
            ((border >> 8) & 0xff) as f32 / 255.0,
            (border & 0xff) as f32 / 255.0,
            1.0,
        ];
        let shrink = ((40.0 * query_pose).round() as i32).min((bh - 1).max(0));
        let query_y = shrink / 2;
        let query_h = (bh - shrink).max(1);
        drw.fill_rect(0, 0, w, h, border_rgb);
        if shrink > 0 {
            drw.fill_rect(0, 0, w, bh as u32, scheme_norm().bg);
        }
        drw.fill_rect(0, query_y, w, query_h as u32, scheme_title().bg);
        drw.fill_rect(0, bh, w, h.saturating_sub(bh as u32), scheme_norm().bg);
        drw.map_picture(drw.picture(), self.frame.bg_pixmap, visual, 0, 0, w, h, 3);
        unsafe {
            let dpy = drw.dpy();
            let format = xrender::XRenderFindStandardFormat(dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                return Err("XRender has no ARGB32 picture format".into());
            }
            xrender::XRenderComposite(
                dpy,
                xrender::PictOpSrc,
                self.frame.bg_picture,
                0,
                self.frame.base_picture,
                0,
                0,
                0,
                0,
                0,
                0,
                w,
                h,
            );
        }
        Ok(())
    }

    /// Atomically moves/resizes and presents the cached frame. Shared by the
    /// GL-cache-miss path and the cheap cached-frame path.
    fn present(&mut self, drw: &Drw, win: u64, geom: PresentGeom, clock_text: &str) -> Result<()> {
        let PresentGeom { x, y, bh, w, h } = geom;
        let dpy = drw.dpy();
        let changed = self.presented != (w, h, x, y, bh);
        unsafe {
            xlib::XGrabServer(dpy);
            if changed {
                xlib::XMoveResizeWindow(dpy, win, x, y, w, h);
            }
            xlib::XFlush(dpy);
        }
        drw.map_picture(self.frame.picture, win, self.frame.visual, 0, 0, w, h, 0);
        unsafe {
            xlib::XUngrabServer(dpy);
            xlib::XFlush(dpy);
        }
        self.presented = (w, h, x, y, bh);
        self.last_clock_text = clock_text.to_string();
        self.dirty = false;
        self.marker_row = if self.selected < self.visible {
            (self.selected.saturating_sub(self.scroll) + 1) as i32
        } else {
            0
        };
        Ok(())
    }

    /// Draws one finder frame: a faded XRender background, a transparent GL
    /// overlay composited over it, and one atomic geometry/presentation swap.
    pub fn draw(
        &mut self,
        drw: &mut Drw,
        screen: i32,
        visual: *mut xlib::Visual,
        win: u64,
        x: i32,
        y: i32,
        bh: i32,
        clock_text: &str,
    ) -> Result<()> {
        if !self.active || visual.is_null() {
            return Ok(());
        }
        let dpy = drw.dpy();
        let (w, h) = self.popup_size(bh as u32);
        let geom = PresentGeom { x, y, bh, w, h };
        if self.frame.dpy.is_null() {
            self.frame.dpy = dpy;
            self.frame.visual = visual;
        }
        let size_before = (self.frame.width, self.frame.height);
        self.frame.resize(w, h)?;
        if size_before != (w, h) {
            self.frame_cache_valid = false;
        }
        if self.loading && !self.initial_background_presented {
            // Paint and present the full-size faded background before any
            // desktop-file scan or GL setup. `display_rows()` reserves the app
            // height while loading, so the ARGB window is already Finder-sized
            // and never exposes a clock-sized patch in its top-left corner.
            drw.resize(w, h);
            self.paint_background(drw, visual, w, h, bh, 0.0)?;
            self.frame.copy_base();
            self.present(drw, win, geom, clock_text)?;
            self.initial_background_presented = true;
            self.dirty = true;
            self.frame_cache_valid = false;
            return Ok(());
        }
        let now = Instant::now();
        if self.icons_pending {
            // A deferred load means the cached frame predates the icons.
            self.frame_cache_valid = false;
        }
        let mut key = self.frame_key(now, bh, w, h, clock_text);
        if self.frame_cache_valid && key == self.frame_cache_key {
            // Nothing that affects the GL frame changed. Reuse the composited
            // pixmap and only repaint the caret with XRender, so an idle Finder
            // (including unrelated bar redraws and blinks) leaves the GPU alone.
            self.frame.copy_base();
            if self.cursor_visible
                && !self.query.is_empty()
                && let Some(rect) = self.cached_caret
            {
                self.frame.draw_caret(rect);
            }
            return self.present(drw, win, geom, clock_text);
        }

        // The shared Xft drawable is resized by each bar section before its own
        // draw, so the Finder must do the same before laying out its background.
        drw.resize(w, h);
        let gl_was_none = self.gl.is_none();
        self.ensure_gl(dpy, screen, visual, w, h)?;
        if self.icons_pending && gl_was_none {
            // On a cold start tick() could not touch an icon because the GL
            // pbuffer did not exist yet. Load the first one here; later rows are
            // loaded one per tick so no single frame waits for every icon.
            let more = self.load_next_icon();
            self.icons_pending = more;
            self.frame_cache_valid = false;
            key = self.frame_key(now, bh, w, h, clock_text);
            if more {
                self.dirty = true;
            }
        }
        let c = crate::gl::compat()?;
        let query_pose = self.query_pose_update(now);

        // Background first, then the transparent GL overlay. The helper also
        // applies dwm's accelerating 12-stop opacity ramp.
        self.paint_background(drw, visual, w, h, bh, query_pose)?;

        let query = self.query.clone();
        let cursor = self.cursor;
        let view_start = self.view_start;
        let mut new_view_start = view_start;
        let pulse = self.glow_pulse(now);
        let result_max_lines = self.display_rows().saturating_sub(1);
        let placeholder = if query.is_empty() {
            clock_text.to_string()
        } else {
            String::new()
        };
        let selected = self.selected;
        let MathSnapshot {
            result: math_result,
            started: math_started,
            help: math_help,
        } = MathSnapshot::from(&self.math_result, self.math_started, self.math_help);
        let translation = self.translate_result.clone();
        let outgoing = self.translate_outgoing.clone();
        let outgoing_started = self.translate_outgoing_started;
        let translate_active = self.translate_active;
        let translate_pending = self.translate_pending;
        let filter_animating = self.filter_animating;
        let filter_progress = Self::filter_progress(self.filter_started);
        let filter = self.filter.clone();
        let order = self.order.clone();
        let scroll_visual = self.scroll_visual;
        let cursor_visible = self.cursor_visible && !query.is_empty();

        {
            let gl = self.gl.as_mut().ok_or("finder GL state is unavailable")?;
            gl.pbuffer.make_current()?;
            unsafe {
                gl::Viewport(0, 0, w as i32, h as i32);
                c.matrix_mode(0x1701);
                c.load_identity();
                c.ortho(0.0, w as f64, h as f64, 0.0, -1.0, 1.0);
                c.matrix_mode(0x1700);
                c.load_identity();
                gl::Disable(gl::DEPTH_TEST);
                gl::Disable(gl::TEXTURE_2D);
                gl::Disable(gl::SCISSOR_TEST);
                gl::ClearColor(0.0, 0.0, 0.0, 0.0);
                gl::Clear(gl::COLOR_BUFFER_BIT);
            }

            let use_query_font = query_pose >= 0.999;
            let query_scale = if use_query_font {
                1.0
            } else {
                1.0 + 0.15 * query_pose
            };
            let font_scale = if translate_pending {
                1.15
            } else if use_query_font {
                1.15
            } else {
                query_scale
            };
            let available = w.saturating_sub(2 * EDGE as u32).max(1);
            let draw_w = (available as f32 / query_scale).ceil().max(1.0) as u32;
            let view_w = (available as f32 / font_scale).floor().max(1.0) as u32;
            let query_scroll = !query.is_empty() && gl.font.text_width(&query) > view_w;
            // Pick the viewport with the font-scale-adjusted width, then trim
            // the displayed slice to the width the GL text renderer can actually
            // paint. The caret is measured from that same slice, so it always
            // lands after the last rendered character instead of being clamped
            // back inside the popup margin.
            let (display, _, caret_end) = if query.is_empty() {
                (placeholder.clone(), 0, 0)
            } else {
                let query_font = if use_query_font {
                    &mut gl.query_font
                } else {
                    &mut gl.font
                };
                let (start, visible, caret) =
                    Self::query_visible_slice(&query, cursor, view_start, view_w, draw_w, |text| {
                        query_font.text_width(text)
                    });
                new_view_start = start;
                (visible, start, caret)
            };
            let query_text = if query.is_empty() {
                &placeholder
            } else {
                &display
            };

            let (query_w, line_h, baseline, caret_local_x, caret_local_y) = {
                let query_font = if use_query_font {
                    &mut gl.query_font
                } else {
                    &mut gl.font
                };
                let query_w = query_font.text_width(query_text);
                let line_h = query_font.height.max(1).min(bh);
                let baseline = (bh - line_h) / 2 + query_font.ascender();
                let caret_local_x = if query.is_empty() {
                    0
                } else {
                    query_font.text_width(&display[..caret_end]) as i32
                        + if caret_end == display.len() { 2 } else { 1 }
                };
                (query_w, line_h, baseline, caret_local_x, (bh - line_h) / 2)
            };
            let center_query = !query_scroll || translate_active;
            let query_x = EDGE
                + if center_query && query_w < available {
                    ((available - query_w) / 2) as i32
                } else {
                    0
                };
            let caret_x = query_x + caret_local_x;
            self.cached_caret = Some(Self::transformed_rect(
                (caret_x.min(w as i32 - 2), caret_local_y, 2, line_h),
                query_scale,
                query_pose,
                (w as i32, bh),
            ));

            if pulse > 0.001 {
                let top = ((bh as f32 - line_h as f32) / 2.0).max(0.0);
                let transform = Self::query_bloom_transform(bh as f32, query_pose, query_scale);
                let _: GlResult<bool> = gl.bloom.render(w, h, 8.0, pulse, Some(transform), || {
                    Self::quad(
                        c,
                        query_x as f32,
                        top,
                        query_w as f32,
                        line_h as f32,
                        (1.0, 1.0, 1.0, 1.0),
                    );
                });
            }

            let query_font = if use_query_font {
                &mut gl.query_font
            } else {
                &mut gl.font
            };
            unsafe {
                c.push_matrix();
                c.translatef(w as f32 / 2.0, bh as f32 / 2.0 + 6.0 * query_pose, 0.0);
                c.scalef(query_scale, query_scale, 1.0);
                c.translatef(-(w as f32 / 2.0), -(bh as f32 / 2.0), 0.0);
            }
            let _: GlResult = query_font.draw_text(query_text, query_x, baseline, draw_w, FG, 1.0);
            unsafe {
                c.pop_matrix();
            }

            if let Some(result) = &math_result {
                Self::draw_result(
                    c,
                    &mut gl.result_font,
                    &Self::math_result_text(result),
                    math_started,
                    false,
                    FG,
                    w,
                    h,
                    bh as u32,
                    result_max_lines,
                );
            } else if math_help {
                for (i, line) in HELP.iter().enumerate() {
                    let _: GlResult = gl.font.draw_text(
                        line,
                        EDGE,
                        (i as i32 + 1) * bh + gl.font.ascender(),
                        available,
                        FINDER_TEXT,
                        1.0,
                    );
                }
            } else if translate_active {
                if !outgoing.is_empty() {
                    Self::draw_result(
                        c,
                        &mut gl.result_font,
                        &outgoing,
                        outgoing_started,
                        true,
                        (1.0, 1.0, 1.0),
                        w,
                        h,
                        bh as u32,
                        result_max_lines,
                    );
                }
                if !translation.is_empty() {
                    Self::draw_result(
                        c,
                        &mut gl.result_font,
                        &translation,
                        self.translate_started,
                        false,
                        (1.0, 1.0, 1.0),
                        w,
                        h,
                        bh as u32,
                        result_max_lines,
                    );
                }
            } else {
                unsafe {
                    gl::Enable(gl::SCISSOR_TEST);
                    gl::Scissor(0, EDGE, w as i32, (h as i32 - 2 * EDGE).max(0));
                }
                if filter_animating {
                    for pass in [true, false] {
                        for (index, anim) in filter.iter().enumerate() {
                            if !anim.active || anim.outgoing != pass {
                                continue;
                            }
                            let (y, alpha, scale_x, scale_y, blur) =
                                Self::filter_eval(anim, filter_progress);
                            if !(-1.0..=FINDER_ROWS as f32).contains(&y) {
                                continue;
                            }
                            let row_rank = order.iter().position(|&i| i == index);
                            let is_selected = !pass && row_rank == Some(selected);
                            let name = self.apps[index].name.clone();
                            let tex = self.apps[index].icon_tex;
                            Self::draw_app(
                                c,
                                gl,
                                index,
                                &name,
                                tex,
                                bh as f64 + y as f64 * bh as f64,
                                alpha,
                                scale_x,
                                scale_y,
                                blur,
                                is_selected,
                                w,
                                h,
                                bh as u32,
                            );
                        }
                    }
                } else {
                    let first = scroll_visual.max(0.0) as usize;
                    for rank in first..self.visible.min(order.len()) {
                        let row_y = bh as f64 + (rank as f64 - scroll_visual) * bh as f64;
                        if row_y >= h as f64 - EDGE as f64 {
                            break;
                        }
                        let index = order[rank];
                        let name = self.apps[index].name.clone();
                        let tex = self.apps[index].icon_tex;
                        Self::draw_app(
                            c,
                            gl,
                            index,
                            &name,
                            tex,
                            row_y,
                            1.0,
                            1.0,
                            1.0,
                            0.0,
                            rank == selected,
                            w,
                            h,
                            bh as u32,
                        );
                    }
                }
                unsafe {
                    gl::Disable(gl::SCISSOR_TEST);
                }
            }
            gl.surface.readback()?;
        }

        self.view_start = new_view_start;
        let gl = self.gl.as_ref().ok_or("finder GL state is unavailable")?;
        drw.blend_picture(
            gl.surface.picture(),
            self.frame.base_pixmap,
            visual,
            0,
            0,
            w,
            h,
        );
        self.frame_cache_key = key;
        self.frame_cache_valid = true;
        self.frame.copy_base();
        if cursor_visible && let Some(rect) = self.cached_caret {
            self.frame.draw_caret(rect);
        }
        self.present(drw, win, geom, clock_text)?;
        let _ = FINDER_MARKER_WIDTH;
        Ok(())
    }

    pub fn query_pose(&self) -> f32 {
        self.query_pose
    }

    pub fn refresh_pose(&mut self) {
        let _ = self.query_pose_update(Instant::now());
    }
}

#[derive(Clone)]
struct MathSnapshot {
    result: Option<String>,
    started: Option<Instant>,
    help: bool,
}

impl MathSnapshot {
    fn from(result: &Option<String>, started: Option<Instant>, help: bool) -> MathSnapshot {
        MathSnapshot {
            result: result.clone(),
            started,
            help,
        }
    }
}

const HELP: &[&str] = &[
    "Operators: + - * / % ^ ! ( )",
    "Functions: sqrt cbrt abs exp ln log2 log10",
    "           pow hypot mod atan2 min max",
    "           sin cos tan asin acos atan",
    "           floor ceil round trunc gcd lcm",
    "           fact bitor bitand bitxor bitnot",
    "           shl shr deg rad",
    "Constants: pi e tau phi epsilon",
    "           byte_max word_max dword_max",
    "           int_max int_min uint_max",
    "           kb mb gb tb true false",
    "Numbers: hex 0x..., decimal, scientific",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_desktop_field_codes() {
        assert_eq!(Finder::strip_field_codes("firefox %U"), "firefox ");
        assert_eq!(Finder::strip_field_codes("app -f %f -c %c"), "app -f  -c c");
    }

    #[test]
    fn ranks_exact_prefix_and_substring() {
        let q = "fire";
        assert_eq!(Finder::name_score("Fire", q), 100_000);
        assert_eq!(Finder::name_score("Firefox", q), 90_000);
        assert!(Finder::name_score("Mozilla Firefox", q) >= 49_980);
        assert_eq!(Finder::name_score("Chromium", q), 0);
    }

    #[test]
    fn cursor_steps_utf8() {
        let s = "กบ";
        assert_eq!(Finder::cursor_next(s, 0), 3);
        assert_eq!(Finder::cursor_prev(s, 3), 0);
    }

    #[test]
    fn icon_load_stays_pending_until_gl_exists() {
        let mut finder = Finder::new();
        finder.active = true;
        finder.loading = false;
        finder.icons_pending = true;
        finder.dirty = false;
        finder.frame_cache_valid = true;
        assert!(finder.gl.is_none());

        finder.tick().unwrap();

        // A cold start creates the GL pbuffer in draw(), so tick() must not
        // consume the pending icon load before that context is available.
        assert!(finder.icons_pending);
        assert!(finder.dirty);
        assert!(!finder.frame_cache_valid);
    }

    #[test]
    fn key_char_ignores_modifiers_and_enter() {
        for sym in [
            XK_Return,
            XK_KP_Enter,
            0xffe1, // Shift_L
            0xffe2, // Shift_R
            0x0100ff0d,
            0x0100ffe1,
            0x0100000d,
        ] {
            assert_eq!(Finder::key_char(sym, 0), None, "keysym {sym:#x}");
        }
        assert_eq!(Finder::key_char('2' as u32, 1), Some('@'));
        assert_eq!(Finder::key_char('a' as u32, 1), Some('A'));
        assert_eq!(Finder::key_char(0x01000e01, 0), Some('ก'));
    }

    #[test]
    fn popup_height_grows_with_rows() {
        let f = Finder::new();
        let (w, h) = f.popup_size(38);
        assert_eq!(w, FINDER_WIDTH as u32);
        assert_eq!(h, 38 * f.display_rows() as u32 + EDGE as u32);
    }

    #[test]
    fn cold_open_reserves_full_popup_until_background_is_presented() {
        let mut f = Finder::new();
        f.open();

        assert!(f.loading);
        assert!(!f.initial_background_presented);
        assert_eq!(f.display_rows(), 1 + FINDER_ROWS);
        assert_eq!(
            f.popup_size(38).1,
            38 * (1 + FINDER_ROWS) as u32 + EDGE as u32
        );

        // Desktop discovery must wait for draw() to show the full-size
        // background; otherwise the first frame is a clock-sized patch.
        f.tick().unwrap();
        assert!(f.loading);
        assert_eq!(f.visible, 0);
        assert!(f.dirty);

        f.initial_background_presented = true;
        f.tick().unwrap();
        assert!(!f.loading);
        assert!(f.icons_pending);
    }

    #[test]
    fn initial_background_marker_resets_between_opens() {
        let mut f = Finder::new();
        f.open();
        f.initial_background_presented = true;
        f.close();
        assert!(!f.initial_background_presented);
        f.open();
        assert!(!f.initial_background_presented);
    }

    #[test]
    fn long_result_word_wraps_into_multiple_lines() {
        let text = "abcdefghij".repeat(7);
        let lines = Finder::wrap_chars(&text, 10, 32);
        assert_eq!(lines.len(), 7);
        assert!(lines.iter().all(|line| line.chars().count() <= 10));
        assert_eq!(lines.concat(), text);
    }

    #[test]
    fn long_result_increases_popup_height_without_exceeding_width_cap() {
        let mut f = Finder::new();
        f.active = true;
        f.translate_active = true;
        let short_height = f.popup_size(38).1;

        f.translate_result = "x".repeat(300);
        let (width, height) = f.popup_size(38);

        assert!(width <= 550);
        assert!(height > short_height);
        assert!(f.display_rows() > 2);
    }

    #[test]
    fn query_view_follows_cursor_to_latest_text() {
        let query = "hello world";
        let width = |s: &str| s.chars().count() as i64 * 10;
        let start = Finder::query_view_start_with(query, query.len(), 70, width);
        assert_eq!(start, 4);
        assert_eq!(&query[start..], "o world");

        let earlier = Finder::query_view_start_with(query, 6, 70, width);
        assert_eq!(earlier, 0);
        assert_eq!(&query[earlier..6], "hello ");
    }

    #[test]
    fn query_view_starts_at_zero_when_text_fits() {
        let query = "hello world";
        let start = Finder::query_view_start_with(query, query.len(), 110, |s| {
            s.chars().count() as i64 * 10
        });
        assert_eq!(start, 0);
    }

    #[test]
    fn query_view_keeps_utf8_boundaries() {
        let query = "กกกกก";
        let start =
            Finder::query_view_start_with(query, query.len(), 9, |s| s.chars().count() as i64 * 3);
        assert_eq!(start, 6);
        assert!(query.is_char_boundary(start));
        assert_eq!(&query[start..], "กกก");
    }

    #[test]
    fn query_view_scrolls_minimally_at_both_edges() {
        let query = "hello world";
        let width = |s: &str| s.chars().count() as i64 * 10;

        let right = Finder::query_view_update_with(query, query.len(), 0, 70, width);
        assert_eq!(right, 4);
        assert_eq!(&query[right..], "o world");

        let inside = Finder::query_view_update_with(query, 8, right, 70, width);
        assert_eq!(inside, right);

        let left = Finder::query_view_update_with(query, 3, right, 70, width);
        assert_eq!(left, 3);

        let back = Finder::query_view_update_with(query, 8, left, 70, width);
        assert_eq!(back, left);

        let fits = Finder::query_view_update_with(query, query.len(), left, 110, width);
        assert_eq!(fits, 0);
    }

    #[test]
    fn query_visible_slice_caret_after_last_visible_character() {
        let query = "hello world this is a very long query";
        let width = |s: &str| s.chars().count() as u32 * 8;

        let (start, display, caret) =
            Finder::query_visible_slice(query, query.len(), 0, 270, 270, width);
        assert!(display.ends_with("query"));
        assert_eq!(caret, display.len());
        assert!(width(&display) <= 266);
        assert!(query.is_char_boundary(start));

        // The waiting font uses a narrower viewport than the GL clip width.
        // The caret still has to sit after the last painted glyph.
        let (start, display, caret) =
            Finder::query_visible_slice(query, query.len(), start, 234, 270, width);
        assert_eq!(start, 9);
        assert_eq!(display, "ld this is a very long query");
        assert_eq!(caret, display.len());
    }

    #[test]
    fn translation_cancel_retires_result() {
        let mut f = Finder::new();
        f.active = true;
        f.translate_active = true;
        f.translate_pending = true;
        f.translate_result = "こんにちは".to_string();
        f.glow_started = Some(Instant::now());
        f.translation_cancel();
        assert!(f.translate_result.is_empty());
        assert_eq!(f.translate_outgoing, "こんにちは");
        assert!(f.translate_outgoing_started.is_some());
        assert!(!f.translate_active);
        assert!(!f.translate_pending);
        assert!(f.translate_due.is_none());
    }

    #[test]
    fn query_is_waiting_only_for_pending_translation() {
        let mut f = Finder::new();
        f.math_help = true;
        assert!(!f.query_is_waiting());

        f.math_help = false;
        f.math_result = Some("4".to_string());
        assert!(!f.query_is_waiting());

        f.translate_pending = true;
        assert!(f.query_is_waiting());
    }

    #[test]
    fn math_result_uses_translator_result_layout() {
        let mut math = Finder::new();
        math.active = true;
        math.math_result = Some("4".to_string());
        math.math_started = Some(Instant::now());

        let mut translate = Finder::new();
        translate.active = true;
        translate.translate_active = true;
        translate.translate_result = "= 4".to_string();
        translate.translate_started = Some(Instant::now());

        assert_eq!(math.display_rows(), translate.display_rows());
        assert_eq!(math.popup_size(38), translate.popup_size(38));
    }

    #[test]
    fn outgoing_translation_expires_and_shrinks_popup() {
        let mut f = Finder::new();
        f.active = true;
        f.translate_active = true;
        f.translate_outgoing = "a retired translation result".to_string();
        f.translate_outgoing_started =
            Some(Instant::now() - RESULT_FADE - Duration::from_millis(1));
        assert!(f.display_rows() >= 2);
        let (_, before) = f.popup_size(38);

        assert!(f.tick().unwrap());
        assert!(f.translate_outgoing.is_empty());
        assert_eq!(f.translate_outgoing_started, None);
        assert_eq!(f.display_rows(), 1);
        let (_, after) = f.popup_size(38);
        assert!(after < before);
    }

    #[test]
    fn frame_key_ignores_cursor_blink() {
        let mut f = Finder::new();
        let now = Instant::now();
        let key = f.frame_key(now, 38, 300, 93, "12:00");
        f.cursor_visible = !f.cursor_visible;
        assert_eq!(f.frame_key(now, 38, 300, 93, "12:00"), key);

        f.query = "hello world".to_string();
        assert_ne!(f.frame_key(now, 38, 300, 93, "12:00"), key);
    }

    #[test]
    fn animation_keys_settle_when_done() {
        let now = Instant::now();
        let old = Finder::anim_step(
            Some(now - RESULT_FADE - Duration::from_secs(2)),
            RESULT_FADE,
        );
        let older = Finder::anim_step(
            Some(now - RESULT_FADE - Duration::from_secs(5)),
            RESULT_FADE,
        );
        assert_eq!(old, older);
    }

    #[test]
    fn next_tick_does_not_busy_loop_while_waiting() {
        let mut f = Finder::new();
        f.active = true;
        let now = Instant::now();
        f.translate_due = Some(now + Duration::from_millis(120));
        let next = f.next_tick(now);
        assert!(next > now);
        assert!(next >= now + Duration::from_millis(100));
    }

    #[test]
    fn next_tick_keeps_glow_during_translate_debounce() {
        let mut f = Finder::new();
        f.active = true;
        let now = Instant::now();
        f.translate_pending = true;
        f.glow_started = Some(now);
        f.translate_due = Some(now + TRANSLATE_DEBOUNCE);
        let next = f.next_tick(now);
        assert!(next <= now + GLOW_TICK);
        assert!(next < f.translate_due.unwrap());
    }

    #[test]
    fn glow_frame_key_follows_pulse_then_settles() {
        let mut f = Finder::new();
        let now = Instant::now();
        let idle = f.frame_key(now, 38, 300, 93, "12:00");

        f.translate_pending = true;
        f.glow_started = Some(now - Duration::from_millis(100));
        let first = f.frame_key(now, 38, 300, 93, "12:00");
        assert_ne!(first, idle);

        f.glow_started = Some(now - Duration::from_millis(200));
        assert_ne!(f.frame_key(now, 38, 300, 93, "12:00"), first);

        f.translate_pending = false;
        f.glow_started = None;
        assert_eq!(f.frame_key(now, 38, 300, 93, "12:00"), idle);
    }

    #[test]
    fn translation_worker_start_preserves_glow_phase() {
        let now = Instant::now();
        let mut f = Finder::new();
        f.translate_pending = true;
        f.glow_started = Some(now - Duration::from_millis(450));

        let before = f.glow_pulse(now);
        f.translation_worker_started();

        assert!(f.translate_pending);
        assert_eq!(f.glow_started, Some(now - Duration::from_millis(450)));
        assert!(f.glow_pulse(now + Duration::from_millis(100)) > before);
    }

    #[test]
    fn glow_pulse_fades_after_pending_clears() {
        let mut f = Finder::new();
        let now = Instant::now();
        f.translate_pending = true;
        f.glow_started = Some(now - Duration::from_millis(700));
        let pulse = f.glow_pulse(now);
        assert!(pulse > 0.9);

        f.stop_glow(now);
        f.translate_pending = false;
        assert_eq!(f.glow_pulse(now), pulse);
        assert_eq!(f.glow_pulse(now + GLOW_FADE), 0.0);
    }

    #[test]
    fn glow_tick_keeps_frame_dirty_without_input() {
        let mut f = Finder::new();
        f.active = true;
        f.translate_pending = true;
        f.glow_started = Some(Instant::now() - Duration::from_millis(100));
        f.presented = (300, 93, 490, 14, 38);
        f.last_clock_text = "12:00".to_string();
        f.dirty = false;

        assert!(f.tick().unwrap());
        assert!(f.needs_draw(300, 93, 490, 14, 38, "12:00"));
    }

    #[test]
    fn glow_backdrop_transform_matches_waiting_text() {
        let bh = 38.0f32;
        let pose = 1.0f32;
        let scale = 1.15f32;
        let transform = Finder::query_bloom_transform(bh, pose, scale);
        for y in [0.0f32, 9.0, bh] {
            let text_y = scale * y + bh / 2.0 + 6.0 * pose - scale * bh / 2.0;
            assert!((transform.map_y(y) - text_y).abs() < 0.001);
        }
    }

    #[test]
    fn bar_only_refresh_does_not_need_finder_draw() {
        let mut f = Finder::new();
        f.active = true;
        f.presented = (300, 93, 490, 14, 38);
        f.last_clock_text = "12:00".to_string();
        assert!(!f.needs_draw(300, 93, 490, 14, 38, "12:00"));
        assert!(f.needs_draw(300, 93, 490, 14, 38, "12:01"));
        f.query = "hello".to_string();
        assert!(!f.needs_draw(300, 93, 490, 14, 38, "12:01"));
        assert!(f.needs_draw(300, 93, 491, 14, 38, "12:01"));
    }
}
