use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::c_int;
use std::ptr;

use x11::xcursor::XcursorLibraryLoadCursor;
use x11::xft::XftFont;
use x11::xlib;

use crate::text::{Fontset, Op};

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

/// The single Xlib display used for cursors, fonts and all bar drawing. It is
/// opened once by the window manager and shared with `drw` so geometry and
/// pixels are issued on one connection, like C dwm's single `dpy`.
pub struct CursorLoader {
    dpy: *mut xlib::Display,
}

// Used only on the window manager thread.
unsafe impl Send for CursorLoader {}

impl CursorLoader {
    pub fn open() -> Result<CursorLoader> {
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return Err("XOpenDisplay failed".into());
            }
            Ok(CursorLoader { dpy })
        }
    }

    pub fn display(&self) -> *mut xlib::Display {
        self.dpy
    }

    pub fn screen(&self) -> c_int {
        unsafe { xlib::XDefaultScreen(self.dpy) }
    }

    /// AnDWM's `drw_cur_create`: the cursor called `name` in the user's cursor
    /// theme, or `0` (`None`) when the theme does not have it.
    pub fn load(&self, name: &str) -> u32 {
        let Ok(name) = std::ffi::CString::new(name) else {
            return 0;
        };
        unsafe {
            let cursor = XcursorLibraryLoadCursor(self.dpy, name.as_ptr()) as u32;
            xlib::XSync(self.dpy, xlib::False);
            cursor
        }
    }
}

impl Drop for CursorLoader {
    fn drop(&mut self) {
        unsafe { xlib::XCloseDisplay(self.dpy) };
    }
}

/// dwm's `drw` fontset plus the layout helpers (`bh`, `lrpad`, `TEXTW`).
pub struct Metrics {
    fontset: RefCell<Fontset>,
    /// Font height (ascent + descent), matching dwm's `drw->fonts->h`.
    pub font_h: i32,
    /// Measured widths keyed by text. The bar tick and the scrolling title
    /// measure the same strings many times per frame; Xft glyph walks are
    /// expensive, so reuse results until the cache is reset.
    width_cache: RefCell<HashMap<String, i32>>,
}

/// Bound the cache: the status string changes every second, so unbounded
/// growth would accumulate many near-identical variants over a long session.
const WIDTH_CACHE_MAX: usize = 512;

impl Metrics {
    pub fn new(dpy: *mut xlib::Display, screen: c_int) -> Result<Metrics> {
        let fontset = Fontset::new(dpy, screen).ok_or("no usable font in fontset")?;
        let font_h = fontset.height();
        Ok(Metrics {
            fontset: RefCell::new(fontset),
            font_h,
            width_cache: RefCell::new(HashMap::new()),
        })
    }

    /// The Xft font for a fontset entry, used by `drw`'s text drawing.
    pub fn xft(&self, i: usize) -> *mut XftFont {
        self.fontset.borrow().font(i).xft
    }

    /// dwm's `lrpad`: the font height, used on both sides of text.
    pub fn lrpad(&self) -> i32 {
        self.font_h
    }

    /// dwm's `bh`: font height + 2 + vertpadbar + borderpx * 2.
    pub fn bar_height(&self) -> i32 {
        self.font_h + 2 + VERTPADBAR + BORDERPX * 2
    }

    /// dwm's `drw_fontset_getwidth`: the text advance, without `lrpad`.
    pub fn text_width(&self, text: &str) -> i32 {
        if let Some(width) = self.width_cache.borrow().get(text) {
            return *width;
        }
        let width = self.fontset.borrow_mut().getwidth(text) as i32;
        let mut cache = self.width_cache.borrow_mut();
        if cache.len() >= WIDTH_CACHE_MAX {
            cache.clear();
        }
        cache.insert(text.to_owned(), width);
        width
    }

    /// dwm's `TEXTW`: the text advance plus `lrpad`.
    pub fn textw(&self, text: &str) -> i32 {
        self.text_width(text) + self.lrpad()
    }

    /// Baseline offset of fontset entry `font`, from the top of its glyph run.
    #[allow(dead_code)] // Used by the optional finder/notification surfaces.
    pub fn ascent(&self, font: usize) -> i32 {
        self.fontset.borrow().font(font).ascent
    }

    /// The steps of dwm's `drw_text` for the fontset.
    pub fn text_ops(&self, x: i32, y: i32, w: i32, h: i32, lpad: i32, text: &str) -> Vec<Op> {
        let mut ops = Vec::new();
        self.fontset.borrow_mut().text(
            x,
            y,
            w.max(0) as u32,
            h.max(0) as u32,
            lpad.max(0) as u32,
            text,
            &mut ops,
        );
        ops
    }

    /// Status width in pixels, measuring only visible text runs and ^f offsets.
    pub fn status_width(&self, text: &str) -> i32 {
        let mut w = 0;
        for token in crate::status::parse_status(text) {
            match token {
                crate::status::StatusToken::Text(s) => {
                    w += self.text_width(&s);
                }
                crate::status::StatusToken::ScrollText(s) => {
                    w += (self.text_width(&s) + 2 * MPRIS_SCROLL_PAD).clamp(1, MPRIS_WIDTH);
                }
                crate::status::StatusToken::Forward(f) => {
                    w += f;
                }
                crate::status::StatusToken::Rect(_, _, rw, _) => {
                    w += rw as i32;
                }
                _ => {}
            }
        }
        w
    }

    /// Width of the typed status runs. The scroll field uses the same clamped
    /// width as the markup path so the bar keeps the exact same geometry.
    pub fn status_runs_width(&self, status: &crate::status::Status) -> i32 {
        status
            .runs()
            .iter()
            .map(|run| {
                if run.scroll {
                    (self.text_width(&run.text) + 2 * MPRIS_SCROLL_PAD).clamp(1, MPRIS_WIDTH)
                } else {
                    self.text_width(&run.text)
                }
            })
            .sum()
    }
}

pub use crate::config::BORDERPX;
pub const VERTPADBAR: i32 = 12;

pub fn col(hex: u32) -> [f32; 4] {
    [
        ((hex >> 16) & 0xff) as f32 / 255.0,
        ((hex >> 8) & 0xff) as f32 / 255.0,
        (hex & 0xff) as f32 / 255.0,
        1.0,
    ]
}

/// Which dwm scheme a cell draws with, mapped to the catppuccin colors.
#[derive(Clone, Copy)]
pub struct Scheme {
    pub fg: [f32; 4],
    pub bg: [f32; 4],
}

pub fn scheme_norm() -> Scheme {
    Scheme {
        fg: col(0x585767),
        bg: col(0x1E1D2D),
    }
}

pub fn scheme_title() -> Scheme {
    Scheme {
        fg: col(0xf8f8f2),
        bg: col(0x1E1D2D),
    }
}

pub fn scheme_layout() -> Scheme {
    Scheme {
        fg: col(0xABE9B3),
        bg: col(0x1E1D2D),
    }
}

pub fn scheme_tag(i: usize) -> Scheme {
    let fg = [0x94E2D5, 0xF28FAD, 0xF8BD96, 0xABE9B3, 0xd5aeea][i];
    Scheme {
        fg: col(fg),
        bg: col(0x1E1D2D),
    }
}

pub const CLRBORDER: u32 = 0x1E1D2D;
/// Background of the bar windows. Area uncovered by a resize shows this color
/// instead of black until the next frame is drawn.
pub const BAR_BACKGROUND_PIXEL: u32 = 0xFF00_0000 | CLRBORDER;
/// Fully transparent background of the ARGB center clock window, matching
/// dwm.c 17875's `cwa.background_pixel = 0`. Transparency is only meaningful
/// when the window uses the 32-bit ARGB visual; otherwise the opaque
/// `BAR_BACKGROUND_PIXEL` is used instead.
pub const BAR_TRANSPARENT_PIXEL: u32 = 0;
pub const TAG_LABEL: &str = "\u{f192}";
pub const LAYOUT_SYMBOL: &str = "[]=";
/// config.h `launchers`: the Arch logo, U+F303.
pub const LAUNCHERS: [&str; 1] = ["\u{f303}"];
pub const BARGAP: i32 = 10;
pub const CLOCKPAD: i32 = 24;
pub const KBLAYOUTPAD: i32 = 17;
pub const HORIZPADBAR: i32 = 6;
pub(crate) const MPRIS_WIDTH: i32 = 240;
pub(crate) const MPRIS_CONTROL_W: i32 = 34;
pub(crate) const MPRIS_SCROLL_PAD: i32 = 8;
/// config.h `systrayspacing`: gap before each icon and after the last one,
/// matching dwm's `getsystraywidth()` / `updatesystray()`.
pub const SYSTRAY_SPACING: i32 = 6;
/// Icon cells are capped so a tall bar does not produce oversized tray icons.
pub const TRAY_ICON_MAX: i32 = 24;
pub const TRAY_ICON_MIN: i32 = 16;
pub const TAGS: usize = 5;
pub(crate) const ULINEPAD: i32 = 5;
pub(crate) const ULINESTROKE: i32 = 2;

/// The MPRIS panel's volume slider in a bar `w` wide: `(x, width)`.
pub fn mpris_slider_span(w: i32) -> (i32, i32) {
    let slider_x = MPRIS_CONTROL_W + 12;
    (slider_x, (w - slider_x - 120).max(1))
}

/// The MPRIS panel's volume knob in a bar `w` wide, as `(x, y, width, height)`
/// relative to the panel. The window manager places the marker window here.
pub fn mpris_knob(w: i32, bh: i32, volume: f32, marker_hovered: bool) -> (i32, i32, i32, i32) {
    let (slider_x, slider_w) = mpris_slider_span(w);
    let track_y = bh + bh / 2 - 2;
    let fill_w = (slider_w as f32 * crate::mpris::volume_position(volume)).round() as i32;
    let knob_w = if marker_hovered { 32 } else { 24 };
    let knob_h = if marker_hovered { 20 } else { 16 };
    let mut knob_x = (slider_x + fill_w).clamp(slider_x, slider_x + slider_w);
    if marker_hovered {
        knob_x -= (32 - 24) / 2;
    }
    let knob_y = track_y + 2 - knob_h / 2;
    (knob_x, knob_y, knob_w, knob_h)
}
