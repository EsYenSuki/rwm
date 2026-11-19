//! Port of dwm's drw.c text layer: the fontset, the Xft metrics behind
//! `TEXTW`, and the fallback and ellipsis walk of `drw_text`. Drawing is done
//! by `drw.rs` with `XftDrawStringUtf8`, exactly like the C version.

use std::ffi::{CString, c_char, c_int, c_void};
use std::ptr;

use x11::xft::{
    FcCharSet, FcPattern, XftCharExists, XftFont, XftFontMatch, XftFontOpenName, XftFontOpenPattern,
    XftTextExtentsUtf8,
};
use x11::xlib::Display;
use x11::xrender::XGlyphInfo;

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

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcNameParse(name: *const c_char) -> *mut FcPattern;
    fn FcPatternDuplicate(p: *const FcPattern) -> *mut FcPattern;
    fn FcPatternAddCharSet(p: *mut FcPattern, object: *const c_char, c: *mut FcCharSet) -> c_int;
    fn FcPatternAddBool(p: *mut FcPattern, object: *const c_char, value: c_int) -> c_int;
    fn FcConfigSubstitute(config: *mut c_void, p: *mut FcPattern, kind: c_int) -> c_int;
    fn FcDefaultSubstitute(p: *mut FcPattern);
    fn FcCharSetCreate() -> *mut FcCharSet;
    fn FcCharSetAddChar(c: *mut FcCharSet, ucs4: u32) -> c_int;
    fn FcCharSetDestroy(c: *mut FcCharSet);
}

/// One drawing step produced by `drw_text`, in the order dwm performs it.
#[derive(Debug, Clone)]
pub enum Op {
    /// `XFillRectangle` with the scheme background.
    Fill { x: i32, y: i32, w: u32, h: u32 },
    /// `XftDrawStringUtf8` with the scheme foreground, using fontset entry `font`.
    Text { font: usize, x: i32, baseline: i32, text: String },
}

/// dwm's `Fnt`: an Xft font plus the pattern used for fontconfig fallback.
pub struct Fnt {
    dpy: *mut Display,
    pub xft: *mut XftFont,
    /// FcNameParse pattern of a font loaded by name. Fallback needs it.
    pattern: *mut FcPattern,
    pub h: i32,
    pub ascent: i32,
}

impl Drop for Fnt {
    fn drop(&mut self) {
        unsafe {
            x11::xft::XftFontClose(self.dpy, self.xft);
            if !self.pattern.is_null() {
                FcPatternDestroy(self.pattern);
            }
        }
    }
}

impl Fnt {
    unsafe fn from_xft(dpy: *mut Display, xft: *mut XftFont, pattern: *mut FcPattern) -> Fnt {
        let (ascent, descent) = unsafe { ((*xft).ascent, (*xft).descent) };
        Fnt { dpy, xft, pattern, h: ascent + descent, ascent }
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
                let pattern = FcNameParse(c.as_ptr());
                if pattern.is_null() {
                    eprintln!("error, cannot parse font name to pattern: '{name}'");
                    continue;
                }
                fonts.push(Fnt::from_xft(dpy, xft, pattern));
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

    fn exists(&self, font: usize, cp: u32) -> bool {
        unsafe { XftCharExists(self.dpy, self.fonts[font].xft, cp) != 0 }
    }

    /// Width of one character segment in fontset entry `font`.
    fn extent(&self, font: usize, s: &str) -> u32 {
        let mut ext: XGlyphInfo = unsafe { std::mem::zeroed() };
        unsafe {
            XftTextExtentsUtf8(
                self.dpy,
                self.fonts[font].xft,
                s.as_ptr(),
                s.len() as c_int,
                &mut ext,
            );
        }
        ext.xOff as i32 as u32
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
            let mut result = x11::xft::FcResult::NoMatch;
            let matched = XftFontMatch(self.dpy, self.screen, pattern, &mut result);
            FcCharSetDestroy(charset);
            FcPatternDestroy(pattern);
            if matched.is_null() {
                return None;
            }
            let xft = XftFontOpenPattern(self.dpy, matched);
            FcPatternDestroy(matched);
            if !xft.is_null() {
                let fnt = Fnt::from_xft(self.dpy, xft, ptr::null_mut());
                if XftCharExists(self.dpy, xft, cp) != 0 {
                    self.fonts.push(fnt);
                    return Some(self.fonts.len() - 1);
                }
                // `fnt` drops here, closing the font we could not use.
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

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcPatternDestroy(p: *mut FcPattern);
}
