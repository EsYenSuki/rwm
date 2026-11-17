//! Port of dwm's drw.c text layer: the fontset, the Xft metrics behind
//! `TEXTW`, and the fallback and ellipsis walk of `drw_text`. Widths come from
//! the same Xft and fontconfig calls the fork makes, so every width matches.
//! Glyphs are rasterized with fontdue and drawn by the OpenGL bar.

use std::ffi::{CString, c_char, c_int, c_void};
use std::ptr;

use x11::xlib::Display;

/// The fork's `fonts[]` in config.def.h order.
pub const FONTS: [&str; 9] = [
    "Iosevka Medium:style:medium:size=11.5",
    "Hack Nerd Font Mono:style:Bold:size=19",
    "Sarasa Gothic SC:style:Regular:size=10",
    "Sarasa Gothic TC:style:Regular:size=10",
    "Sarasa Gothic J:style:Regular:size=10",
    "Sarasa Gothic K:style:Regular:size=10",
    "Noto Sans Thai:style:Regular:size=11.5",
    "Noto Sans Arabic:style:Regular:size=11.5",
    "Noto Sans Devanagari:style:Regular:size=11.5",
];

const NOMATCHES_LEN: usize = 64;
const FC_TRUE: c_int = 1;
const FC_MATCH_PATTERN: c_int = 0;
const FC_RESULT_MATCH: c_int = 0;
const DPI: f64 = 96.0;

#[repr(C)]
struct XftFontRaw {
    ascent: c_int,
    descent: c_int,
    height: c_int,
    max_advance_width: c_int,
    charset: *mut c_void,
    pattern: *mut c_void,
}

#[repr(C)]
#[derive(Default)]
struct XGlyphInfo {
    width: u16,
    height: u16,
    x: i16,
    y: i16,
    x_off: i16,
    y_off: i16,
}

#[link(name = "Xft")]
unsafe extern "C" {
    fn XftFontOpenName(dpy: *mut Display, screen: c_int, name: *const c_char) -> *mut XftFontRaw;
    fn XftFontOpenPattern(dpy: *mut Display, pattern: *mut c_void) -> *mut XftFontRaw;
    fn XftFontMatch(
        dpy: *mut Display,
        screen: c_int,
        pattern: *const c_void,
        result: *mut c_int,
    ) -> *mut c_void;
    fn XftCharExists(dpy: *mut Display, font: *mut XftFontRaw, ucs4: u32) -> c_int;
    fn XftTextExtentsUtf8(
        dpy: *mut Display,
        font: *mut XftFontRaw,
        string: *const u8,
        len: c_int,
        extents: *mut XGlyphInfo,
    );
}

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcNameParse(name: *const u8) -> *mut c_void;
    fn FcPatternDuplicate(p: *const c_void) -> *mut c_void;
    fn FcPatternAddCharSet(p: *mut c_void, object: *const c_char, c: *mut c_void) -> c_int;
    fn FcPatternAddBool(p: *mut c_void, object: *const c_char, value: c_int) -> c_int;
    fn FcConfigSubstitute(config: *mut c_void, p: *mut c_void, kind: c_int) -> c_int;
    fn FcDefaultSubstitute(p: *mut c_void);
    fn FcCharSetCreate() -> *mut c_void;
    fn FcCharSetAddChar(c: *mut c_void, ucs4: u32) -> c_int;
    fn FcCharSetDestroy(c: *mut c_void);
    fn FcPatternGetString(p: *const c_void, object: *const c_char, n: c_int, s: *mut *mut u8) -> c_int;
    fn FcPatternGetDouble(p: *const c_void, object: *const c_char, n: c_int, d: *mut f64) -> c_int;
    fn FcPatternGetInteger(p: *const c_void, object: *const c_char, n: c_int, i: *mut c_int) -> c_int;
}

/// One drawing step produced by `drw_text`, in the order dwm performs it.
pub enum Op {
    /// `XFillRectangle` with the scheme background.
    Fill { x: i32, y: i32, w: u32, h: u32 },
    /// `XftDrawStringUtf8` with the scheme foreground, using fontset entry `font`.
    Text { font: usize, x: i32, baseline: i32, text: String },
}

/// dwm's `Fnt`: one Xft font plus the fontdue copy used for rasterizing.
pub struct Fnt {
    xft: *mut XftFontRaw,
    /// The fontconfig pattern of fonts from a name; dwm's `drw->fonts->pattern`.
    pattern: *mut c_void,
    pub h: i32,
    pub ascent: i32,
    pub px: f32,
    pub glyphs: Option<fontdue::Font>,
}

impl Fnt {
    unsafe fn from_xft(xft: *mut XftFontRaw, pattern: *mut c_void) -> Fnt {
        unsafe {
            let (ascent, descent) = ((*xft).ascent, (*xft).descent);
            let mut px = 0.0f64;
            let mut file: *mut u8 = ptr::null_mut();
            let mut index: c_int = 0;
            let fp = (*xft).pattern;
            if FcPatternGetDouble(fp, c"pixelsize".as_ptr(), 0, &mut px) != FC_RESULT_MATCH {
                let mut size = 0.0f64;
                FcPatternGetDouble(fp, c"size".as_ptr(), 0, &mut size);
                px = size * DPI / 72.0;
            }
            let mut glyphs = None;
            if FcPatternGetString(fp, c"file".as_ptr(), 0, &mut file) == FC_RESULT_MATCH {
                FcPatternGetInteger(fp, c"index".as_ptr(), 0, &mut index);
                let path = std::ffi::CStr::from_ptr(file as *const c_char).to_string_lossy().into_owned();
                if let Ok(data) = std::fs::read(&path) {
                    let settings = fontdue::FontSettings {
                        collection_index: index.max(0) as u32,
                        ..Default::default()
                    };
                    glyphs = fontdue::Font::from_bytes(data, settings).ok();
                }
            }
            Fnt {
                xft,
                pattern,
                h: ascent + descent,
                ascent,
                px: px as f32,
                glyphs,
            }
        }
    }
}

pub struct Fontset {
    dpy: *mut Display,
    screen: c_int,
    fonts: Vec<Fnt>,
    nomatches: [u32; NOMATCHES_LEN],
    nomatch_idx: usize,
    ellipsis_width: u32,
}

impl Fontset {
    /// dwm's `drw_fontset_create`: each font that loads is chained in order.
    pub fn new(dpy: *mut Display, screen: c_int) -> Option<Fontset> {
        let mut fonts = Vec::new();
        for name in FONTS {
            let c = CString::new(name).ok()?;
            unsafe {
                let xft = XftFontOpenName(dpy, screen, c.as_ptr());
                if xft.is_null() {
                    eprintln!("error, cannot load font from name: '{name}'");
                    continue;
                }
                let pattern = FcNameParse(c.as_ptr() as *const u8);
                if pattern.is_null() {
                    eprintln!("error, cannot parse font name to pattern: '{name}'");
                    continue;
                }
                fonts.push(Fnt::from_xft(xft, pattern));
            }
        }
        if fonts.is_empty() {
            return None;
        }
        Some(Fontset {
            dpy,
            screen,
            fonts,
            nomatches: [0; NOMATCHES_LEN],
            nomatch_idx: 0,
            ellipsis_width: 0,
        })
    }

    pub fn font(&self, i: usize) -> &Fnt {
        &self.fonts[i]
    }

    /// dwm's `drw->fonts->h`.
    pub fn height(&self) -> i32 {
        self.fonts[0].h
    }

    /// dwm's `drw_fontset_getwidth`.
    pub fn getwidth(&mut self, text: &str) -> u32 {
        let mut ops = Vec::new();
        self.walk(0, 0, 0, 0, 0, text, false, &mut ops) as u32
    }

    /// dwm's `drw_text` with a background fill and a text layer: appends the
    /// steps to draw into `ops` and returns the same value `drw_text` returns.
    pub fn text(&mut self, x: i32, y: i32, w: u32, h: u32, lpad: u32, text: &str, ops: &mut Vec<Op>) -> i32 {
        self.walk(x, y, w, h, lpad, text, true, ops)
    }

    /// Xft advance of one character in fontset entry `font`.
    pub fn advance(&self, font: usize, ch: char) -> i32 {
        let mut buf = [0u8; 4];
        let s = ch.encode_utf8(&mut buf);
        let mut ext = XGlyphInfo::default();
        unsafe {
            XftTextExtentsUtf8(self.dpy, self.fonts[font].xft, s.as_ptr(), s.len() as c_int, &mut ext);
        }
        ext.x_off as i32
    }

    fn exists(&self, font: usize, cp: u32) -> bool {
        unsafe { XftCharExists(self.dpy, self.fonts[font].xft, cp) != 0 }
    }

    /// Width of one character segment in fontset entry `font`.
    fn extent(&self, font: usize, s: &str) -> u32 {
        let mut ext = XGlyphInfo::default();
        unsafe {
            XftTextExtentsUtf8(self.dpy, self.fonts[font].xft, s.as_ptr(), s.len() as c_int, &mut ext);
        }
        ext.x_off as i32 as u32
    }

    /// Loads a fallback font for `cp` the way dwm's `drw_text` does and appends
    /// it to the chain. Returns its index, or `None` when no font has the glyph.
    fn fallback(&mut self, cp: u32) -> Option<usize> {
        unsafe {
            let charset = FcCharSetCreate();
            FcCharSetAddChar(charset, cp);
            let base = self.fonts[0].pattern;
            let pattern = FcPatternDuplicate(base);
            FcPatternAddCharSet(pattern, c"charset".as_ptr(), charset);
            FcPatternAddBool(pattern, c"scalable".as_ptr(), FC_TRUE);
            FcConfigSubstitute(ptr::null_mut(), pattern, FC_MATCH_PATTERN);
            FcDefaultSubstitute(pattern);
            let mut result: c_int = 0;
            let matched = XftFontMatch(self.dpy, self.screen, pattern, &mut result);
            FcCharSetDestroy(charset);
            if matched.is_null() {
                return None;
            }
            let xft = XftFontOpenPattern(self.dpy, matched);
            if !xft.is_null() {
                let fnt = Fnt::from_xft(xft, ptr::null_mut());
                if XftCharExists(self.dpy, xft, cp) != 0 {
                    self.fonts.push(fnt);
                    return Some(self.fonts.len() - 1);
                }
            }
            self.nomatch_idx += 1;
            self.nomatches[self.nomatch_idx % NOMATCHES_LEN] = cp;
            Some(usize::MAX)
        }
    }

    /// Port of `drw_text`. With `render` false it only measures.
    #[allow(clippy::too_many_arguments)]
    fn walk(
        &mut self,
        x0: i32,
        y: i32,
        w0: u32,
        h: u32,
        lpad: u32,
        text: &str,
        render: bool,
        ops: &mut Vec<Op>,
    ) -> i32 {
        let mut x = x0;
        let mut w = w0;
        if render {
            ops.push(Op::Fill { x, y, w, h });
            x += lpad as i32;
            w = w.saturating_sub(lpad);
        } else {
            w = u32::MAX;
        }
        if render && self.ellipsis_width == 0 {
            self.ellipsis_width = self.getwidth("...");
        }
        let ellipsis_width = self.ellipsis_width;

        let mut rest = text;
        let mut usedfont = 0usize;
        let mut charexists = false;
        let mut overflow = false;
        let mut ellipsis_x = 0i32;
        let mut ellipsis_w = 0u32;

        loop {
            let mut ew: u32 = 0;
            let mut ellipsis_len = 0usize;
            let mut utf8strlen = 0usize;
            let seg_start = rest;
            let mut nextfont: Option<usize> = None;

            while let Some(ch) = rest.chars().next() {
                let cp = ch as u32;
                let clen = ch.len_utf8();
                let mut found = None;
                for ci in 0..self.fonts.len() {
                    charexists = charexists || self.exists(ci, cp);
                    if charexists {
                        found = Some(ci);
                        break;
                    }
                }
                if let Some(curfont) = found {
                    let tmpw = self.extent(curfont, &rest[..clen]);
                    if ew + ellipsis_width <= w {
                        ellipsis_x = x + ew as i32;
                        ellipsis_w = w - ew;
                        ellipsis_len = utf8strlen;
                    }
                    if ew + tmpw > w {
                        overflow = true;
                        if !render {
                            x += tmpw as i32;
                        } else {
                            utf8strlen = ellipsis_len;
                        }
                    } else if curfont == usedfont {
                        utf8strlen += clen;
                        rest = &rest[clen..];
                        ew += tmpw;
                    } else {
                        nextfont = Some(curfont);
                    }
                }
                if overflow || !charexists || nextfont.is_some() {
                    break;
                }
                charexists = false;
            }

            if utf8strlen > 0 {
                if render {
                    let f = &self.fonts[usedfont];
                    let ty = y + (h as i32 - f.h) / 2 + f.ascent;
                    ops.push(Op::Text {
                        font: usedfont,
                        x,
                        baseline: ty,
                        text: seg_start[..utf8strlen].to_string(),
                    });
                }
                x += ew as i32;
                w = w.saturating_sub(ew);
            }
            if render && overflow {
                self.walk(ellipsis_x, y, ellipsis_w, h, 0, "...", true, ops);
            }

            if rest.is_empty() || overflow {
                break;
            } else if let Some(nf) = nextfont {
                charexists = false;
                usedfont = nf;
            } else {
                charexists = true;
                let cp = rest.chars().next().map(|c| c as u32).unwrap_or(0);
                if self.nomatches.contains(&cp) {
                    usedfont = 0;
                } else {
                    match self.fallback(cp) {
                        Some(usize::MAX) => usedfont = 0,
                        Some(i) => usedfont = i,
                        None => {}
                    }
                }
            }
        }

        x + if render { w as i32 } else { 0 }
    }
}

