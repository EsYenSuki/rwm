//! Rust port of AnDWM's `drw.c`. Every bar section is drawn with Xlib, Xft and
//! XRender into one offscreen pixmap on the window manager's Xlib display, then
//! copied into the bar window with `XCopyArea` and flushed. There is no CPU
//! canvas, no glyph rasterization and no GPU readback in this path.

use std::collections::HashMap;
use std::ffi::{c_char, c_int};
use std::ptr;

use image::imageops::{FilterType, resize};

use x11::xft::{
    XftColor, XftColorAllocValue, XftColorFree, XftDraw, XftDrawChange, XftDrawCreate,
    XftDrawDestroy, XftDrawSetClip, XftDrawSetClipRectangles, XftDrawStringUtf8,
};
use x11::xlib::{self, Display, Drawable, GC, Pixmap, Visual, XImage, XRectangle, ZPixmap};
use x11::xrender::{self, Picture, XLinearGradient, XPointFixed, XRenderColor};

use crate::bar::{
    BORDERPX, CLIENT_ICON_LEFT_PAD, CLIENT_ICON_SPACING, CLOCKPAD, CLRBORDER, HORIZPADBAR,
    KBLAYOUTPAD, LAUNCHERS, LAYOUT_SYMBOL, MPRIS_CONTROL_W, MPRIS_SCROLL_PAD, MPRIS_WIDTH, Metrics,
    Scheme, TAG_LABEL, TAGS, ULINEPAD, ULINESTROKE, VERTPADBAR, col, mpris_slider_span,
    scheme_layout, scheme_norm, scheme_tag, scheme_title,
};
use crate::status::{Status, StatusToken};
use crate::text::Op;

type Result<T = ()> = std::result::Result<T, Box<dyn std::error::Error>>;

fn fixed(v: f64) -> i32 {
    (v * 65536.0) as i32
}

fn u16color(v: f32) -> u16 {
    (v.clamp(0.0, 1.0) * 65535.0).round() as u16
}

fn color_key(c: [f32; 4]) -> u32 {
    u32::from((c[3].clamp(0.0, 1.0) * 255.0).round() as u8) << 24
        | u32::from((c[0].clamp(0.0, 1.0) * 255.0).round() as u8) << 16
        | u32::from((c[1].clamp(0.0, 1.0) * 255.0).round() as u8) << 8
        | u32::from((c[2].clamp(0.0, 1.0) * 255.0).round() as u8)
}

/// Cached artwork picture: `XRenderComposite` uses it directly, so a new cover
/// only uploads pixels when the artwork (or the panel size) actually changes.
/// Holding the `Arc` keeps its address reserved, so a later cover cannot reuse
/// the same key after the MPRIS snapshot is replaced.
struct CachedArtwork {
    art: std::sync::Arc<crate::mpris::Artwork>,
    w: u32,
    h: u32,
    pixmap: Pixmap,
    picture: Picture,
}

/// The focused client's icon as an XRender picture. `id` is the version of the
/// decoded `_NET_WM_ICON` pixel data; a changed property uploads a new pixmap.
struct CachedClientIcon {
    id: u64,
    w: u32,
    h: u32,
    pixmap: Pixmap,
    picture: Picture,
}

/// The drawing context: one display, one offscreen drawable, one GC, one Xft
/// drawable and one XRender picture, exactly like C's `Drw`.
pub struct Drw {
    dpy: *mut Display,
    screen: c_int,
    root: Drawable,
    visual: *mut Visual,
    colormap: u64,
    depth: u32,
    w: u32,
    h: u32,
    drawable: Pixmap,
    picture: Picture,
    gc: GC,
    xft_draw: *mut XftDraw,
    colors: HashMap<u32, XftColor>,
    artwork: Option<CachedArtwork>,
    client_icon: Option<CachedClientIcon>,
}

impl Drw {
    pub fn dpy(&self) -> *mut Display {
        self.dpy
    }

    pub fn screen(&self) -> c_int {
        self.screen
    }

    pub fn new(dpy: *mut Display, screen: c_int, root: Drawable) -> Result<Drw> {
        unsafe {
            let visual = xlib::XDefaultVisual(dpy, screen);
            if visual.is_null() {
                return Err("no default visual".into());
            }
            let colormap = xlib::XDefaultColormap(dpy, screen);
            let depth = xlib::XDefaultDepth(dpy, screen) as u32;
            let drawable = xlib::XCreatePixmap(dpy, root, 1, 1, depth);
            let format = xrender::XRenderFindVisualFormat(dpy, visual);
            let picture = if format.is_null() {
                0
            } else {
                xrender::XRenderCreatePicture(dpy, drawable, format, 0, ptr::null())
            };
            let gc = xlib::XCreateGC(dpy, root, 0, ptr::null_mut());
            xlib::XSetLineAttributes(dpy, gc, 1, xlib::LineSolid, xlib::CapButt, xlib::JoinMiter);
            let xft_draw = XftDrawCreate(dpy, drawable, visual, colormap);
            if drawable == 0 || gc.is_null() || xft_draw.is_null() {
                return Err("cannot create drawing context".into());
            }
            Ok(Drw {
                dpy,
                screen,
                root,
                visual,
                colormap,
                depth,
                w: 1,
                h: 1,
                drawable,
                picture,
                gc,
                xft_draw,
                colors: HashMap::new(),
                artwork: None,
                client_icon: None,
            })
        }
    }

    /// dwm's `drw_resize`: the new size is used by every following draw call.
    pub fn resize(&mut self, w: u32, h: u32) {
        let (w, h) = (w.max(1), h.max(1));
        if (w, h) == (self.w, self.h) {
            return;
        }
        unsafe {
            if self.picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.picture);
            }
            xlib::XFreePixmap(self.dpy, self.drawable);
            self.drawable = xlib::XCreatePixmap(self.dpy, self.root, w, h, self.depth);
            let format = xrender::XRenderFindVisualFormat(self.dpy, self.visual);
            self.picture = if format.is_null() {
                0
            } else {
                xrender::XRenderCreatePicture(self.dpy, self.drawable, format, 0, ptr::null())
            };
            XftDrawChange(self.xft_draw, self.drawable);
        }
        self.w = w;
        self.h = h;
    }

    /// Allocates a color once, like `drw_clr_create`, and reuses it afterward.
    /// Status strings and theme colors both come through here.
    fn color(&mut self, c: [f32; 4]) -> XftColor {
        let key = color_key(c);
        if let Some(clr) = self.colors.get(&key) {
            return *clr;
        }
        let render = XRenderColor {
            red: u16color(c[0]),
            green: u16color(c[1]),
            blue: u16color(c[2]),
            alpha: u16color(c[3]),
        };
        let mut clr: XftColor = unsafe { std::mem::zeroed() };
        unsafe {
            if XftColorAllocValue(self.dpy, self.visual, self.colormap, &render, &mut clr) == 0 {
                clr.color = XRenderColor {
                    red: 0xffff,
                    green: 0xffff,
                    blue: 0xffff,
                    alpha: 0xffff,
                };
                clr.pixel = xlib::XWhitePixel(self.dpy, self.screen);
            }
        }
        self.colors.insert(key, clr);
        clr
    }

    /// dwm's `drw_rect` with filled = 1.
    fn rect(&mut self, x: i32, y: i32, w: i32, h: i32, c: [f32; 4]) {
        if w <= 0 || h <= 0 {
            return;
        }
        let clr = self.color(c);
        unsafe {
            xlib::XSetForeground(self.dpy, self.gc, clr.pixel);
            xlib::XFillRectangle(self.dpy, self.drawable, self.gc, x, y, w as u32, h as u32);
        }
    }

    /// Translucent fill for the MPRIS volume track, via an XRender solid
    /// picture instead of CPU blending.
    fn rect_alpha(&mut self, x: i32, y: i32, w: i32, h: i32, c: [f32; 4]) {
        if w <= 0 || h <= 0 || self.picture == 0 {
            return;
        }
        let color = XRenderColor {
            red: u16color(c[0]),
            green: u16color(c[1]),
            blue: u16color(c[2]),
            alpha: u16color(c[3]),
        };
        unsafe {
            let solid = xrender::XRenderCreateSolidFill(self.dpy, &color);
            if solid != 0 {
                xrender::XRenderComposite(
                    self.dpy,
                    xrender::PictOpOver,
                    solid,
                    0,
                    self.picture,
                    0,
                    0,
                    0,
                    0,
                    x,
                    y,
                    w as u32,
                    h as u32,
                );
                xrender::XRenderFreePicture(self.dpy, solid);
            }
        }
    }

    fn clear_clip(&self) {
        unsafe {
            XftDrawSetClip(self.xft_draw, ptr::null_mut());
        }
    }

    fn set_clip(&self, x: i32, y: i32, w: i32, h: i32) {
        let r = XRectangle {
            x: x as i16,
            y: y as i16,
            width: w.max(0) as u16,
            height: h.max(0) as u16,
        };
        unsafe {
            XftDrawSetClipRectangles(self.xft_draw, 0, 0, &r, 1);
        }
    }

    /// Draws the `drw_text` steps: `XFillRectangle` for the background and
    /// `XftDrawStringUtf8` for each glyph run.
    fn draw_ops(&mut self, m: &Metrics, ops: &[Op], fg: [f32; 4], bg: Option<[f32; 4]>) {
        let fg = self.color(fg);
        let bg = bg.map(|c| self.color(c));
        for op in ops {
            match *op {
                Op::Fill { x, y, w, h } => {
                    if let Some(bg) = bg {
                        unsafe {
                            xlib::XSetForeground(self.dpy, self.gc, bg.pixel);
                            xlib::XFillRectangle(self.dpy, self.drawable, self.gc, x, y, w, h);
                        }
                    }
                }
                Op::Text {
                    font,
                    x,
                    baseline,
                    ref text,
                } => unsafe {
                    XftDrawStringUtf8(
                        self.xft_draw,
                        &fg,
                        m.xft(font),
                        x,
                        baseline,
                        text.as_ptr(),
                        text.len() as c_int,
                    );
                },
            }
        }
    }

    /// dwm's `drw_text`.
    #[allow(clippy::too_many_arguments)]
    pub fn text(
        &mut self,
        m: &Metrics,
        x: i32,
        y: i32,
        w: i32,
        h: i32,
        lpad: i32,
        text: &str,
        s: Scheme,
    ) {
        self.clear_clip();
        let ops = m.text_ops(x, y, w, h, lpad, text);
        self.draw_ops(m, &ops, s.fg, Some(s.bg));
    }

    /// `drw_text` without the background fill: artwork stays visible behind the
    /// MPRIS controls and the scrolling status text.
    #[allow(clippy::too_many_arguments)]
    pub fn text_transparent(
        &mut self,
        m: &Metrics,
        x: i32,
        y: i32,
        w: i32,
        h: i32,
        lpad: i32,
        text: &str,
        fg: [f32; 4],
    ) {
        let ops = m.text_ops(x, y, w, h, lpad, text);
        self.draw_ops(m, &ops, fg, None);
    }

    /// dwm's `drw_text_scroll_progress`: fill the field, clip it, then draw the
    /// text at `-1/0/+1` cycles so it wraps seamlessly.
    #[allow(clippy::too_many_arguments)]
    fn scroll_text(
        &mut self,
        m: &Metrics,
        x: i32,
        y: i32,
        h: i32,
        text: &str,
        fg: [f32; 4],
        progress: Option<f32>,
        scroll: u32,
    ) {
        let field_w = (m.text_width(text) + 2 * MPRIS_SCROLL_PAD).clamp(1, MPRIS_WIDTH);
        let text_w = m.text_width(text).max(1);
        self.rect(x, y, field_w, h, col(0xA6DA95));
        if let Some(progress) = progress {
            let pw = (field_w as f32 * progress.clamp(0.0, 1.0)).round() as i32;
            self.rect(x, y, pw, h, col(0xB8E9B4));
        }
        let cycle = text_w + 32;
        let offset = if text_w + 2 * MPRIS_SCROLL_PAD > MPRIS_WIDTH {
            scroll as i32 % cycle
        } else {
            0
        };
        self.set_clip(x + MPRIS_SCROLL_PAD, y, field_w - 2 * MPRIS_SCROLL_PAD, h);
        for copy in -1..=1 {
            let tx = x + MPRIS_SCROLL_PAD - offset + copy * cycle;
            if tx < x + field_w && tx + text_w > x + MPRIS_SCROLL_PAD {
                self.text_transparent(m, tx, y, text_w, h, 0, text, fg);
            }
        }
        self.clear_clip();
    }

    /// dwm's `drw_pic`: one `XRenderComposite` of a cached picture.
    fn pic(&self, x: i32, y: i32, w: u32, h: u32, picture: Picture) {
        if picture == 0 || self.picture == 0 {
            return;
        }
        unsafe {
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpOver,
                picture,
                0,
                self.picture,
                0,
                0,
                0,
                0,
                x,
                y,
                w,
                h,
            );
        }
    }

    /// The 3-stop gradient dwm composites over the MPRIS cover art in one pass.
    fn gradient(&mut self, x: i32, y: i32, w: u32, h: u32, bg: [f32; 4]) {
        if self.picture == 0 {
            return;
        }
        let rgb = XRenderColor {
            red: u16color(bg[0]),
            green: u16color(bg[1]),
            blue: u16color(bg[2]),
            alpha: 0xffff,
        };
        let clear = XRenderColor {
            red: rgb.red,
            green: rgb.green,
            blue: rgb.blue,
            alpha: 0,
        };
        let colors = [rgb, rgb, clear];
        let stops = [fixed(0.0), fixed(0.25), fixed(1.0)];
        let linear = XLinearGradient {
            p1: XPointFixed { x: 0, y: 0 },
            p2: XPointFixed {
                x: 0,
                y: fixed(h as f64),
            },
        };
        unsafe {
            let overlay = xrender::XRenderCreateLinearGradient(
                self.dpy,
                &linear,
                stops.as_ptr(),
                colors.as_ptr(),
                stops.len() as c_int,
            );
            if overlay != 0 {
                xrender::XRenderComposite(
                    self.dpy,
                    xrender::PictOpOver,
                    overlay,
                    0,
                    self.picture,
                    0,
                    0,
                    0,
                    0,
                    x,
                    y,
                    w,
                    h,
                );
                xrender::XRenderFreePicture(self.dpy, overlay);
            }
        }
    }

    /// dwm's `drw_map`: copy the drawable into the window and flush, so a resize
    /// never leaves a new window size with old pixels.
    pub fn map(&self, win: Drawable, w: u32, h: u32) {
        unsafe {
            xlib::XCopyArea(self.dpy, self.drawable, win, self.gc, 0, 0, w, h, 0, 0);
            xlib::XFlush(self.dpy);
        }
    }

    /// dwm's `drw_map_alpha` with `fade == 0`. `XCopyArea` requires the source
    /// and destination to have the same depth, so the 32-bit ARGB center window
    /// is painted with `XRenderComposite` from the same offscreen picture
    /// `map()` uses. This is the minimal bridge until the full GL/fade path
    /// replaces it; it keeps the ordinary clock bar visible on an ARGB window.
    pub fn map_argb(&self, win: Drawable, visual: *mut Visual, w: u32, h: u32) {
        self.map_picture(self.picture, win, visual, 0, 0, w, h, 0);
    }

    /// Solid rectangle in the offscreen drawable, used to lay out the Finder
    /// background before its faded picture is composited into the frame.
    pub fn fill_rect(&self, x: i32, y: i32, w: u32, h: u32, rgb: [f32; 4]) {
        let pixel = ((rgb[0].clamp(0.0, 1.0) * 255.0).round() as u32) << 16
            | ((rgb[1].clamp(0.0, 1.0) * 255.0).round() as u32) << 8
            | ((rgb[2].clamp(0.0, 1.0) * 255.0).round() as u32)
            | 0xff00_0000;
        unsafe {
            xlib::XSetForeground(self.dpy, self.gc, pixel as u64);
            xlib::XFillRectangle(self.dpy, self.drawable, self.gc, x, y, w, h);
        }
    }

    /// Composite an ARGB32 source picture (the EGL rendering surface) onto an
    /// ARGB window. `fade == 3` applies dwm's accelerating 12-stop vertical
    /// opacity ramp from `drw_map_alpha`; `fade == 0` is a plain `PictOpSrc`
    /// copy. This is the bridge between the OpenGL finder and the ARGB clock
    /// bar window.
    pub fn map_picture(
        &self,
        src: xrender::Picture,
        win: Drawable,
        visual: *mut Visual,
        x: i32,
        y: i32,
        w: u32,
        h: u32,
        fade: u8,
    ) {
        unsafe {
            let format = xrender::XRenderFindVisualFormat(self.dpy, visual);
            if format.is_null() || src == 0 || w == 0 || h == 0 {
                return;
            }
            let dest = xrender::XRenderCreatePicture(self.dpy, win, format, 0, ptr::null());
            if dest == 0 {
                return;
            }
            let clear = xrender::XRenderColor {
                red: 0,
                green: 0,
                blue: 0,
                alpha: 0,
            };
            xrender::XRenderFillRectangle(self.dpy, xrender::PictOpSrc, dest, &clear, x, y, w, h);
            let mask = if fade == 0 {
                0
            } else {
                Self::fade_mask(self.dpy, fade, h)
            };
            if mask != 0 {
                xrender::XRenderComposite(
                    self.dpy,
                    xrender::PictOpOver,
                    src,
                    mask,
                    dest,
                    x,
                    y,
                    0,
                    0,
                    x,
                    y,
                    w,
                    h,
                );
                xrender::XRenderFreePicture(self.dpy, mask);
            } else {
                xrender::XRenderComposite(
                    self.dpy,
                    xrender::PictOpSrc,
                    src,
                    0,
                    dest,
                    x,
                    y,
                    0,
                    0,
                    x,
                    y,
                    w,
                    h,
                );
            }
            xrender::XRenderFreePicture(self.dpy, dest);
            xlib::XFlush(self.dpy);
        }
    }

    /// The offscreen picture that `map()` copies into a bar window. The finder
    /// composes it into its frame pixmap to obtain the same background colour
    /// and vertical opacity ramp as dwm's `drw_map_alpha`.
    pub fn picture(&self) -> xrender::Picture {
        self.picture
    }

    /// `XRenderComposite(PictOpOver, src, None, dst)` for an ARGB32 source and
    /// an ARGB32 destination. Used to layer the transparent GL finder overlay
    /// over the already-faded background frame without clearing it.
    pub fn blend_picture(
        &self,
        src: xrender::Picture,
        dst: Drawable,
        visual: *mut Visual,
        x: i32,
        y: i32,
        w: u32,
        h: u32,
    ) {
        unsafe {
            let format = xrender::XRenderFindVisualFormat(self.dpy, visual);
            if format.is_null() || src == 0 || w == 0 || h == 0 {
                return;
            }
            let dest = xrender::XRenderCreatePicture(self.dpy, dst, format, 0, ptr::null());
            if dest == 0 {
                return;
            }
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpOver,
                src,
                0,
                dest,
                0,
                0,
                0,
                0,
                x,
                y,
                w,
                h,
            );
            xrender::XRenderFreePicture(self.dpy, dest);
        }
    }

    fn fade_mask(dpy: *mut Display, fade: u8, h: u32) -> xrender::Picture {
        const ALPHAS: [u16; 12] = [
            0xffff, 0xffff, 0xfd70, 0xf851, 0xed70, 0xdeb8, 0xca3d, 0xb0a3, 0x91ff, 0x6df4, 0x451e,
            0x0000,
        ];
        unsafe {
            let mut stops = [0i32; 12];
            let mut colors = [xrender::XRenderColor {
                red: 0,
                green: 0,
                blue: 0,
                alpha: 0,
            }; 12];
            let count = if fade == 3 { 12 } else { 2 };
            if fade == 3 {
                // dwm's fade=3 override: the first two stops are both at zero,
                // then every tenth of the popup height. XDoubleToFixed truncates.
                const STOPS: [i32; 12] = [
                    0, 0, 6553, 13107, 19660, 26214, 32768, 39321, 45875, 52428, 58982, 65536,
                ];
                stops.copy_from_slice(&STOPS);
                for (i, color) in colors.iter_mut().enumerate() {
                    color.alpha = ALPHAS[i];
                }
            } else {
                stops[0] = 0;
                stops[1] = 65536;
                colors[0].alpha = 0;
                colors[1].alpha = 0xffff;
            }
            let linear = xrender::XLinearGradient {
                p1: xrender::XPointFixed { x: 0, y: 0 },
                p2: xrender::XPointFixed {
                    x: 0,
                    y: (h as i64 * 65536) as i32,
                },
            };
            xrender::XRenderCreateLinearGradient(
                dpy,
                &linear,
                stops.as_ptr(),
                colors.as_ptr(),
                count as i32,
            )
        }
    }

    /// Tags row of dwm's `drawbar()`.
    pub fn tags(&mut self, m: &Metrics, w: i32, occ: u32, selected: u32) {
        let bh = self.h as i32;
        let bh_n = bh - BORDERPX * 2;
        let lrpad = m.lrpad();
        self.rect(0, 0, w, bh, col(CLRBORDER));
        let mut x = BORDERPX;
        for i in 0..TAGS {
            let tw = m.textw(TAG_LABEL);
            let scheme = if occ & 1 << i != 0 {
                scheme_tag(i)
            } else {
                scheme_norm()
            };
            self.text(m, x, BORDERPX, tw, bh_n, lrpad / 2, TAG_LABEL, scheme);
            if selected & 1 << i != 0 {
                self.rect(
                    x + ULINEPAD,
                    bh_n - ULINESTROKE,
                    tw - ULINEPAD * 2,
                    ULINESTROKE,
                    scheme.fg,
                );
            }
            x += tw;
        }
        let lw = m.textw(LAYOUT_SYMBOL);
        self.text(m, x, 0, lw, bh, lrpad / 2, LAYOUT_SYMBOL, scheme_layout());
    }

    /// Title row of dwm's `drawbar()`. The focused window's application icon
    /// takes the place of the Arch launcher; the glyph stays as the fallback
    /// for windows that publish no `_NET_WM_ICON`.
    pub fn title(
        &mut self,
        m: &Metrics,
        w: i32,
        name: Option<&str>,
        focused: bool,
        icon: Option<&crate::icon::ClientIcon>,
    ) {
        let bh = self.h as i32;
        let lrpad = m.lrpad();
        self.rect(0, 0, w, bh, col(CLRBORDER));
        let mut x = BORDERPX;
        // The icon branch already accounts for its own gap; drw_text's lrpad/2
        // would add another ~8px of empty space before the window name.
        let mut title_lpad = lrpad / 2;
        if let Some(icon) = icon
            && let Some(picture) = self.client_icon_picture(icon)
        {
            self.pic(
                x + CLIENT_ICON_LEFT_PAD,
                (bh - icon.height as i32) / 2,
                icon.width,
                icon.height,
                picture,
            );
            x += CLIENT_ICON_LEFT_PAD + icon.width as i32 + CLIENT_ICON_SPACING;
            title_lpad = 0;
        } else {
            for launcher in LAUNCHERS {
                let lw = m.textw(launcher);
                self.text(m, x, 0, lw, bh, lrpad / 2, launcher, scheme_layout());
                x += lw;
            }
        }
        if let Some(name) = name {
            let tw = w - x;
            if tw > 0 {
                let scheme = if focused {
                    scheme_title()
                } else {
                    scheme_norm()
                };
                self.text(m, x, 0, tw, bh, title_lpad, name, scheme);
            }
        }
    }

    /// Keyboard layout section.
    pub fn kb(&mut self, m: &Metrics, w: i32, text: &str, focused: bool) {
        let bh = self.h as i32;
        let bh_n = bh - BORDERPX * 2;
        let scheme = if focused {
            scheme_title()
        } else {
            scheme_norm()
        };
        self.rect(0, 0, w, bh, col(CLRBORDER));
        self.rect(0, BORDERPX, w, bh_n, scheme.bg);
        self.text(
            m,
            0,
            BORDERPX + VERTPADBAR / 2,
            w,
            bh - VERTPADBAR,
            KBLAYOUTPAD,
            text,
            scheme,
        );
    }

    /// Status2d bar for a custom root-window string. The built-in cells use
    /// `status_runs` instead; this path only exists for `xsetroot -name`.
    pub fn status(&mut self, m: &Metrics, w: i32, text: &str, scroll: u32, progress: Option<f32>) {
        let bh = self.h as i32;
        self.rect(0, 0, w, bh, col(CLRBORDER));
        self.status_contents(m, w, bh, bh, text, scroll, progress, false);
    }

    /// Paints typed status runs directly. Every color and position is already
    /// decided by `Status::runs`, so nothing here reads markup characters.
    pub fn status_runs(
        &mut self,
        m: &Metrics,
        w: i32,
        status: &Status,
        scroll: u32,
        progress: Option<f32>,
    ) {
        let bh = self.h as i32;
        let sbh = bh - BORDERPX * 2;
        let norm = scheme_norm();
        self.rect(0, 0, w, bh, col(CLRBORDER));
        self.rect(0, BORDERPX, w, sbh, norm.bg);
        let y = BORDERPX + VERTPADBAR / 2;
        self.paint_runs(
            m,
            &status.runs(),
            y,
            sbh - VERTPADBAR,
            scroll,
            progress,
            false,
        );
    }

    /// Shared run painter. `expanded` leaves the bar's default background
    /// transparent so artwork shows through in the MPRIS panel, matching the
    /// old `status_contents(..., expanded = true)` behaviour.
    #[allow(clippy::too_many_arguments)]
    fn paint_runs(
        &mut self,
        m: &Metrics,
        runs: &[crate::status::StatusRun],
        y: i32,
        h: i32,
        scroll: u32,
        progress: Option<f32>,
        expanded: bool,
    ) {
        let mut x = HORIZPADBAR / 2;
        for run in runs {
            let fg = col(run.fg);
            if run.scroll {
                self.scroll_text(m, x, y, h, &run.text, fg, progress, scroll);
                x += (m.text_width(&run.text) + 2 * MPRIS_SCROLL_PAD).clamp(1, MPRIS_WIDTH);
            } else if !run.text.is_empty() {
                let tw = m.text_width(&run.text);
                let cell_bg = if expanded && run.bg == CLRBORDER {
                    [0.0; 4]
                } else {
                    col(run.bg)
                };
                if cell_bg == [0.0; 4] {
                    self.text_transparent(m, x, y, tw, h, 0, &run.text, fg);
                } else {
                    self.text(m, x, y, tw, h, 0, &run.text, Scheme { fg, bg: cell_bg });
                }
                x += tw;
            }
        }
    }

    /// The center clock, anchored in the middle of the window like dwm.
    pub fn clock(&mut self, m: &Metrics, w: i32, clock: &str, focused: bool) {
        let bh = self.h as i32;
        let bh_n = bh - BORDERPX * 2;
        let tcw = m.text_width(clock) + 2 * CLOCKPAD;
        let x = if w > tcw { (w - tcw) / 2 } else { 0 };
        let scheme = if focused {
            scheme_title()
        } else {
            scheme_norm()
        };
        self.rect(0, 0, w, bh, col(CLRBORDER));
        self.rect(0, BORDERPX, w, bh_n, scheme.bg);
        self.text(
            m,
            x,
            BORDERPX + VERTPADBAR / 2,
            tcw,
            bh - VERTPADBAR,
            CLOCKPAD,
            clock,
            scheme,
        );
    }

    /// The two-row MPRIS panel: cover art, gradient, controls, volume slider,
    /// scrolling title and progress.
    #[allow(clippy::too_many_arguments)]
    pub fn mpris_panel(
        &mut self,
        m: &Metrics,
        w: i32,
        status: &Status,
        player: &crate::mpris::Snapshot,
        scroll: u32,
        marker_hovered: bool,
    ) {
        let bh = (self.h as i32) / 2;
        let panel_h = self.h as i32;
        let norm = scheme_norm();
        self.rect(0, 0, w, panel_h, norm.bg);
        if let Some(art) = player.artwork.as_ref() {
            if let Some(pic) = self.artwork_picture(art, w as u32, panel_h as u32) {
                self.pic(0, 0, w as u32, panel_h as u32, pic);
            }
        }
        self.gradient(0, 0, w as u32, panel_h as u32, norm.bg);

        let (slider_x, slider_w) = mpris_slider_span(w);
        let volume_x = slider_x + slider_w + 6;
        let previous_x = volume_x + 46;
        let next_x = previous_x + MPRIS_CONTROL_W;
        let control_y = bh + 4;
        let control_h = (bh - 8).max(1);
        let fg = scheme_title().fg;
        let playback = if player.playing { "" } else { "" };
        self.text_transparent(m, 10, control_y, 28, control_h, 0, playback, fg);
        self.text_transparent(m, previous_x, control_y, 28, control_h, 0, "", fg);
        self.text_transparent(m, next_x, control_y, 28, control_h, 0, "", fg);

        let track_y = bh + bh / 2 - 2;
        let fill_w =
            (slider_w as f32 * crate::mpris::volume_position(player.volume)).round() as i32;
        let knob_w = crate::bar::mpris_knob(w, bh, player.volume, marker_hovered).2;
        let mut empty = col(0xA6DA95);
        empty[3] = 0.55;
        self.rect_alpha(slider_x, track_y, slider_w, 4, empty);
        self.rect(slider_x, track_y, fill_w, 4, col(0xB8E9B4));
        self.rect(slider_x + fill_w, track_y + 1, knob_w / 2, 2, col(0xB8E9B4));
        self.text_transparent(
            m,
            volume_x,
            control_y,
            38,
            control_h,
            0,
            &format!("{}%", (player.volume * 100.0).round() as u32),
            fg,
        );

        let y = BORDERPX + VERTPADBAR / 2;
        self.paint_runs(
            m,
            &status.runs(),
            y,
            bh - VERTPADBAR,
            scroll,
            player.progress,
            true,
        );
    }

    /// Shared status token painter for the right bar and the MPRIS panel.
    #[allow(clippy::too_many_arguments)]
    fn status_contents(
        &mut self,
        m: &Metrics,
        w: i32,
        bh: i32,
        _canvas_h: i32,
        text: &str,
        scroll: u32,
        progress: Option<f32>,
        expanded: bool,
    ) {
        let sbh = bh - BORDERPX * 2;
        let norm = scheme_norm();
        if !expanded {
            self.rect(0, BORDERPX, w, sbh, norm.bg);
        }
        let mut x = HORIZPADBAR / 2;
        let y = BORDERPX + VERTPADBAR / 2;
        let content_h = sbh - VERTPADBAR;
        let mut fg = norm.fg;
        let mut bg = norm.bg;
        let mut has_bg = false;

        for token in crate::status::parse_status(text) {
            match token {
                StatusToken::Text(s) => {
                    if !s.is_empty() {
                        let tw = m.text_width(&s);
                        let cell_bg = if has_bg {
                            bg
                        } else if expanded {
                            [0.0; 4]
                        } else {
                            norm.bg
                        };
                        if cell_bg == [0.0; 4] {
                            self.text_transparent(m, x, y, tw, content_h, 0, &s, fg);
                        } else {
                            self.text(m, x, y, tw, content_h, 0, &s, Scheme { fg, bg: cell_bg });
                        }
                        x += tw;
                    }
                }
                StatusToken::ScrollText(s) => {
                    self.scroll_text(m, x, y, content_h, &s, fg, progress, scroll);
                    x += (m.text_width(&s) + 2 * MPRIS_SCROLL_PAD).clamp(1, MPRIS_WIDTH);
                }
                StatusToken::Fg(c) => fg = c,
                StatusToken::Bg(c) => {
                    bg = c;
                    has_bg = true;
                }
                StatusToken::Reset => {
                    fg = norm.fg;
                    bg = norm.bg;
                    has_bg = false;
                }
                StatusToken::Forward(f) => x += f,
                StatusToken::Rect(rx, ry, rw, rh) => {
                    self.rect(x + rx, y + ry, rw as i32, rh as i32, fg);
                }
            }
        }
    }

    /// Upload premultiplied `0xAARRGGBB` pixels into a 32-bit pixmap and wrap
    /// it in an XRender picture. Shared by MPRIS artwork and window icons.
    fn argb_picture(&self, pixels: &[u32], w: u32, h: u32) -> Option<(Pixmap, Picture)> {
        if pixels.len() < (w * h) as usize || w == 0 || h == 0 {
            return None;
        }
        unsafe {
            // XPutImage reads the buffer but needs a mutable pointer; keep the
            // copy local so the caller's cached icon data stays immutable.
            let mut data = pixels.to_vec();
            let mut img: XImage = std::mem::zeroed();
            img.width = w as c_int;
            img.height = h as c_int;
            img.format = ZPixmap;
            img.data = data.as_mut_ptr() as *mut c_char;
            img.byte_order = xlib::XImageByteOrder(self.dpy);
            img.bitmap_unit = xlib::XBitmapUnit(self.dpy);
            img.bitmap_bit_order = xlib::XBitmapBitOrder(self.dpy);
            img.bitmap_pad = 32;
            img.depth = 32;
            img.bytes_per_line = (w * 4) as c_int;
            img.bits_per_pixel = 32;
            // XInitImage only derives masks for some depths. Set the ARGB32
            // masks explicitly so the 0xAARRGGBB pixels are never sampled as
            // opaque black by the server.
            img.red_mask = 0x00ff0000;
            img.green_mask = 0x0000ff00;
            img.blue_mask = 0x000000ff;
            if xlib::XInitImage(&mut img) == 0 {
                return None;
            }
            let pixmap = xlib::XCreatePixmap(self.dpy, self.root, w, h, 32);
            let gc = xlib::XCreateGC(self.dpy, pixmap, 0, ptr::null_mut());
            xlib::XPutImage(self.dpy, pixmap, gc, &mut img, 0, 0, 0, 0, w, h);
            xlib::XFreeGC(self.dpy, gc);
            let format = xrender::XRenderFindStandardFormat(self.dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                xlib::XFreePixmap(self.dpy, pixmap);
                return None;
            }
            let picture = xrender::XRenderCreatePicture(self.dpy, pixmap, format, 0, ptr::null());
            if picture == 0 {
                xlib::XFreePixmap(self.dpy, pixmap);
                return None;
            }
            Some((pixmap, picture))
        }
    }

    /// Cover-scale artwork into an ARGB32 pixmap and cache the XRender picture.
    fn artwork_picture(
        &mut self,
        art: &std::sync::Arc<crate::mpris::Artwork>,
        w: u32,
        h: u32,
    ) -> Option<Picture> {
        if let Some(cached) = &self.artwork
            && std::sync::Arc::ptr_eq(&cached.art, art)
            && cached.w == w
            && cached.h == h
        {
            return Some(cached.picture);
        }
        let pixels = cover_pixels(art, w, h)?;
        let (pixmap, picture) = self.argb_picture(&pixels, w, h)?;
        if let Some(old) = self.artwork.take() {
            unsafe {
                if old.picture != 0 {
                    xrender::XRenderFreePicture(self.dpy, old.picture);
                }
                xlib::XFreePixmap(self.dpy, old.pixmap);
            }
        }
        self.artwork = Some(CachedArtwork {
            art: art.clone(),
            w,
            h,
            pixmap,
            picture,
        });
        Some(picture)
    }

    /// The focused client's `_NET_WM_ICON` as an XRender picture. Small icons
    /// are cheap to upload, and `id` changes only when the property changes.
    fn client_icon_picture(&mut self, icon: &crate::icon::ClientIcon) -> Option<Picture> {
        if let Some(cached) = &self.client_icon
            && cached.id == icon.id
            && cached.w == icon.width
            && cached.h == icon.height
        {
            return Some(cached.picture);
        }
        let (pixmap, picture) = self.argb_picture(&icon.argb, icon.width, icon.height)?;
        if let Some(old) = self.client_icon.take() {
            unsafe {
                if old.picture != 0 {
                    xrender::XRenderFreePicture(self.dpy, old.picture);
                }
                xlib::XFreePixmap(self.dpy, old.pixmap);
            }
        }
        self.client_icon = Some(CachedClientIcon {
            id: icon.id,
            w: icon.width,
            h: icon.height,
            pixmap,
            picture,
        });
        Some(picture)
    }
}

/// Cover-fit the artwork into the panel: centre-crop the source to the panel's
/// aspect, then scale once with Lanczos3. The artwork arrives at its native
/// resolution, so this is the only resampling step and a small cover never
/// gets blown up twice.
fn cover_pixels(art: &crate::mpris::Artwork, w: u32, h: u32) -> Option<Vec<u32>> {
    let (sw, sh) = (art.width as u32, art.height as u32);
    if sw == 0 || sh == 0 || w == 0 || h == 0 {
        return None;
    }
    if art.rgba.len() < sw as usize * sh as usize * 4 {
        return None;
    }
    let aspect = w as f64 / h as f64;
    let (cw, ch) = if sw as f64 > sh as f64 * aspect {
        (((sh as f64 * aspect).round() as u32).clamp(1, sw), sh)
    } else {
        (sw, ((sw as f64 / aspect).round() as u32).clamp(1, sh))
    };
    let (x0, y0) = ((sw - cw) / 2, (sh - ch) / 2);
    let cropped = image::RgbaImage::from_fn(cw, ch, |x, y| {
        let i = ((y + y0) * sw + x + x0) as usize * 4;
        image::Rgba([
            art.rgba[i],
            art.rgba[i + 1],
            art.rgba[i + 2],
            art.rgba[i + 3],
        ])
    });
    let scaled = if cw == w && ch == h {
        cropped
    } else {
        resize(&cropped, w, h, FilterType::Lanczos3)
    };
    Some(
        scaled
            .into_raw()
            .as_chunks::<4>()
            .0
            .iter()
            .map(|p| {
                u32::from(p[3]) << 24
                    | u32::from(p[0]) << 16
                    | u32::from(p[1]) << 8
                    | u32::from(p[2])
            })
            .collect(),
    )
}

impl Drop for Drw {
    fn drop(&mut self) {
        unsafe {
            if let Some(art) = self.artwork.take() {
                if art.picture != 0 {
                    xrender::XRenderFreePicture(self.dpy, art.picture);
                }
                xlib::XFreePixmap(self.dpy, art.pixmap);
            }
            if let Some(icon) = self.client_icon.take() {
                if icon.picture != 0 {
                    xrender::XRenderFreePicture(self.dpy, icon.picture);
                }
                xlib::XFreePixmap(self.dpy, icon.pixmap);
            }
            if self.picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.picture);
            }
            if !self.xft_draw.is_null() {
                XftDrawDestroy(self.xft_draw);
            }
            xlib::XFreePixmap(self.dpy, self.drawable);
            xlib::XFreeGC(self.dpy, self.gc);
            for clr in self.colors.values() {
                XftColorFree(
                    self.dpy,
                    self.visual,
                    self.colormap,
                    clr as *const _ as *mut XftColor,
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cover_pixels_scales_native_art_once_to_panel_size() {
        let mut rgba = Vec::with_capacity(336 * 188 * 4);
        for _ in 0..336 * 188 {
            rgba.extend_from_slice(&[40, 80, 120, 255]);
        }
        let art = crate::mpris::Artwork {
            rgba,
            width: 336,
            height: 188,
        };
        let pixels = cover_pixels(&art, 600, 60).expect("cover pixels");
        assert_eq!(pixels.len(), 600 * 60);
        assert!(pixels.iter().all(|&p| p == 0xff28_5078));
    }

    #[test]
    fn cover_pixels_rejects_short_pixel_buffers() {
        let art = crate::mpris::Artwork {
            rgba: vec![0; 4],
            width: 8,
            height: 8,
        };
        assert!(cover_pixels(&art, 60, 60).is_none());
    }
}
