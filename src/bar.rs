use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{CString, c_void};
use std::os::raw::c_int;
use std::ptr;

use glow::HasContext;
use x11::glx::*;
use x11::xcursor::XcursorLibraryLoadCursor;
use x11::xlib;

use crate::text::{Fontset, Op};

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

/// Text measuring for the layout, on the window manager thread. The fontset
/// is owned by this struct, so measuring never touches the render thread.
pub struct Metrics {
    fontset: RefCell<Fontset>,
    /// Font height (ascent + descent), matching dwm's `drw->fonts->h`.
    pub font_h: i32,
}

impl Metrics {
    /// Opens its own X display and font set for measuring.
    pub fn open() -> Result<Metrics> {
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return Err("XOpenDisplay failed".into());
            }
            let screen = xlib::XDefaultScreen(dpy);
            Metrics::new(dpy, screen)
        }
    }

    fn new(dpy: *mut xlib::Display, screen: c_int) -> Result<Metrics> {
        let fontset = Fontset::new(dpy, screen).ok_or("no usable font in fontset")?;
        let font_h = fontset.height();
        Ok(Metrics { fontset: RefCell::new(fontset), font_h })
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
        self.fontset.borrow_mut().getwidth(text) as i32
    }

    /// dwm's `TEXTW`: the text advance plus `lrpad`.
    pub fn textw(&self, text: &str) -> i32 {
        self.text_width(text) + self.lrpad()
    }

    /// The steps of dwm's `drw_text` for the fontset, shared by GL and CPU drawing.
    pub fn text_ops(&self, x: i32, y: i32, w: i32, h: i32, lpad: i32, text: &str) -> Vec<Op> {
        let mut ops = Vec::new();
        self.fontset
            .borrow_mut()
            .text(x, y, w.max(0) as u32, h.max(0) as u32, lpad.max(0) as u32, text, &mut ops);
        ops
    }

    /// Baseline offset of fontset entry `font`, from the top of its glyph run.
    pub fn ascent(&self, font: usize) -> i32 {
        self.fontset.borrow().font(font).ascent
    }

    /// Rasterizes one run of text from fontset entry `font` into a coverage
    /// buffer, with the baseline `ascent` rows from the top.
    pub fn raster(&self, font: usize, text: &str) -> Option<(Vec<u8>, usize, usize)> {
        let set = self.fontset.borrow();
        let f = set.font(font);
        let glyphs = f.glyphs.as_ref()?;
        let mut placed = Vec::new();
        let mut pen = 0i32;
        for ch in text.chars() {
            placed.push((pen, glyphs.rasterize(ch, f.px)));
            pen += set.advance(font, ch);
        }
        let w = (pen.max(1)) as usize;
        let h = f.h as usize;
        let mut buf = vec![0u8; w * h];
        for (gx, (m, bmp)) in placed {
            let base_x = gx + m.xmin;
            let base_y = f.ascent - (m.ymin + m.height as i32);
            for row in 0..m.height {
                for col in 0..m.width {
                    let x = base_x + col as i32;
                    let y = base_y + row as i32;
                    if x < 0 || y < 0 || x >= w as i32 || y >= h as i32 {
                        continue;
                    }
                    let idx = y as usize * w + x as usize;
                    buf[idx] = buf[idx].max(bmp[row * m.width + col]);
                }
            }
        }
        Some((buf, w, h))
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
                    w += (self.text_width(&s) + 2 * MPRIS_SCROLL_PAD).min(MPRIS_WIDTH).max(1);
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
}

/// Glyph runs cached as textures are dropped above this count.
const GLYPH_CACHE_MAX: usize = 512;

pub use crate::config::BORDERPX;
pub const VERTPADBAR: i32 = 12;


const VERT_SRC: &str = r#"#version 330 core
layout(location = 0) in vec2 pos;
layout(location = 1) in vec2 uv;
layout(location = 2) in vec4 color;
uniform vec2 res;
out vec2 vuv;
out vec4 vcol;
void main() {
    vec2 ndc = pos / res * 2.0 - 1.0;
    gl_Position = vec4(ndc.x, -ndc.y, 0.0, 1.0);
    vuv = uv;
    vcol = color;
}
"#;

const FRAG_SRC: &str = r#"#version 330 core
in vec2 vuv;
in vec4 vcol;
uniform sampler2D tex;
uniform int image_mode;
out vec4 frag;
void main() {
    if (image_mode != 0) {
        frag = texture(tex, vuv) * vcol;
    } else {
        float a = texture(tex, vuv).r;
        frag = vec4(vcol.rgb, vcol.a * a);
    }
}
"#;

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
    Scheme { fg: col(0x585767), bg: col(0x1E1D2D) }
}

pub fn scheme_title() -> Scheme {
    Scheme { fg: col(0xf8f8f2), bg: col(0x1E1D2D) }
}

pub fn scheme_layout() -> Scheme {
    Scheme { fg: col(0xABE9B3), bg: col(0x1E1D2D) }
}

pub fn scheme_tag(i: usize) -> Scheme {
    let fg = [0x94E2D5, 0xF28FAD, 0xF8BD96, 0xABE9B3, 0xd5aeea][i];
    Scheme { fg: col(fg), bg: col(0x1E1D2D) }
}

pub struct Gl {
    dpy: *mut xlib::Display,
    ctx: GLXContext,
    gl: glow::Context,
    program: glow::Program,
    vao: glow::VertexArray,
    vbo: glow::Buffer,
    white: glow::Texture,
    artwork: RefCell<Option<(String, glow::Texture)>>,
    /// Coverage textures of rasterized text, keyed by fontset entry and text.
    glyphs: RefCell<HashMap<(usize, String), (glow::Texture, i32, i32)>>,
    metrics: Metrics,
    pub visual_id: u32,
    pub depth: u8,
}

// The GL context is made current only on the thread that owns this value,
// after it has been moved there by `render::spawn`.
unsafe impl Send for Gl {}

impl Gl {
    /// `create_window` gets the GLX visual and depth and returns a window to
    /// draw into. That window becomes current before GL objects are created.
    pub fn new(create_window: impl FnOnce(u32, u8) -> Result<u32>) -> Result<Gl> {
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return Err("XOpenDisplay failed".into());
            }
            let screen = xlib::XDefaultScreen(dpy);

            let attribs: [c_int; 19] = [
                GLX_X_RENDERABLE, 1,
                GLX_DRAWABLE_TYPE, GLX_WINDOW_BIT,
                GLX_RENDER_TYPE, GLX_RGBA_BIT,
                GLX_X_VISUAL_TYPE, GLX_TRUE_COLOR,
                GLX_RED_SIZE, 8,
                GLX_GREEN_SIZE, 8,
                GLX_BLUE_SIZE, 8,
                GLX_ALPHA_SIZE, 8,
                GLX_DOUBLEBUFFER, 1,
                0,
            ];
            let mut count: c_int = 0;
            let configs = glXChooseFBConfig(dpy, screen, attribs.as_ptr(), &mut count);
            if configs.is_null() || count == 0 {
                return Err("no GLX framebuffer config".into());
            }
            let fb = *configs;

            let vi = glXGetVisualFromFBConfig(dpy, fb);
            if vi.is_null() {
                return Err("no visual for GLX config".into());
            }
            let visual_id = (*vi).visualid as u32;
            let depth = (*vi).depth as u8;
            xlib::XFree(vi as *mut c_void);

            let ctx = glXCreateNewContext(dpy, fb, GLX_RGBA_TYPE, ptr::null_mut(), 1);
            if ctx.is_null() {
                return Err("glXCreateNewContext failed".into());
            }
            let win = create_window(visual_id, depth)?;
            if glXMakeCurrent(dpy, win as u64, ctx) == 0 {
                return Err("glXMakeCurrent failed".into());
            }

            let gl = glow::Context::from_loader_function(|name| {
                let c = CString::new(name).unwrap();
                match glXGetProcAddress(c.as_ptr() as *const u8) {
                    Some(f) => f as *const c_void,
                    None => ptr::null(),
                }
            });

            let program = link_program(&gl)?;
            let vao = gl.create_vertex_array()?;
            let vbo = gl.create_buffer()?;
            gl.bind_vertex_array(Some(vao));
            gl.bind_buffer(glow::ARRAY_BUFFER, Some(vbo));
            let stride = 8 * 4;
            gl.vertex_attrib_pointer_f32(0, 2, glow::FLOAT, false, stride, 0);
            gl.vertex_attrib_pointer_f32(1, 2, glow::FLOAT, false, stride, 8);
            gl.vertex_attrib_pointer_f32(2, 4, glow::FLOAT, false, stride, 16);
            gl.enable_vertex_attrib_array(0);
            gl.enable_vertex_attrib_array(1);
            gl.enable_vertex_attrib_array(2);
            gl.enable(glow::BLEND);
            gl.blend_func(glow::SRC_ALPHA, glow::ONE_MINUS_SRC_ALPHA);
            gl.pixel_store_i32(glow::UNPACK_ALIGNMENT, 1);

            let white = gl.create_texture()?;
            gl.bind_texture(glow::TEXTURE_2D, Some(white));
            gl.tex_image_2d(
                glow::TEXTURE_2D, 0, glow::R8 as i32, 1, 1, 0,
                glow::RED, glow::UNSIGNED_BYTE, glow::PixelUnpackData::Slice(Some(&[255u8])),
            );
            set_texture_params(&gl);

            let metrics = Metrics::new(dpy, screen)?;

            Ok(Gl {
                dpy,
                ctx,
                gl,
                program,
                vao,
                vbo,
                white,
                artwork: RefCell::new(None),
                glyphs: RefCell::new(HashMap::new()),
                metrics,
                visual_id,
                depth,
            })
        }
    }

    /// AnDWM's `drw_cur_create`: the cursor called `name` in the user's cursor
    /// theme, or `0` (`None`) when the theme does not have it. The cursor lives
    /// on this connection, so the window manager can use it on its own one.
    pub fn load_cursor(&self, name: &str) -> u32 {
        let Ok(name) = CString::new(name) else {
            return 0;
        };
        unsafe {
            let cursor = XcursorLibraryLoadCursor(self.dpy, name.as_ptr()) as u32;
            xlib::XSync(self.dpy, xlib::False);
            cursor
        }
    }

    /// Makes this GL context current on `win`, which must be a bar window.
    pub fn make_current(&self, win: u32) {
        unsafe {
            glXMakeCurrent(self.dpy, win as u64, self.ctx);
        }
    }

    /// Detaches the context from this thread, so another thread can take it.
    pub fn release_current(&self) {
        unsafe {
            glXMakeCurrent(self.dpy, 0, ptr::null_mut());
        }
    }

    pub fn begin(&self, win_w: i32, win_h: i32, clear: [f32; 4]) {
        unsafe {
            let gl = &self.gl;
            gl.viewport(0, 0, win_w, win_h);
            gl.clear_color(clear[0], clear[1], clear[2], clear[3]);
            gl.clear(glow::COLOR_BUFFER_BIT);
            gl.use_program(Some(self.program));
            let loc = gl.get_uniform_location(self.program, "res");
            gl.uniform_2_f32(loc.as_ref(), win_w as f32, win_h as f32);
            let image_mode = gl.get_uniform_location(self.program, "image_mode");
            gl.uniform_1_i32(image_mode.as_ref(), 0);
            gl.bind_vertex_array(Some(self.vao));
        }
    }

    pub fn finish(&self, win: u32) {
        unsafe {
            glXSwapBuffers(self.dpy, win as u64);
        }
    }

    fn quad(&self, x: f32, y: f32, w: f32, h: f32, uv_w: f32, color: [f32; 4], tex: glow::Texture) {
        let (r, g, b, a) = (color[0], color[1], color[2], color[3]);
        #[rustfmt::skip]
        let v: [f32; 48] = [
            x,     y,     0.0,  0.0,  r, g, b, a,
            x + w, y,     uv_w, 0.0,  r, g, b, a,
            x + w, y + h, uv_w, 1.0,  r, g, b, a,
            x,     y,     0.0,  0.0,  r, g, b, a,
            x + w, y + h, uv_w, 1.0,  r, g, b, a,
            x,     y + h, 0.0,  1.0,  r, g, b, a,
        ];
        unsafe {
            let gl = &self.gl;
            gl.bind_buffer(glow::ARRAY_BUFFER, Some(self.vbo));
            let bytes = std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 4);
            gl.buffer_data_u8_slice(glow::ARRAY_BUFFER, bytes, glow::STREAM_DRAW);
            gl.active_texture(glow::TEXTURE0);
            gl.bind_texture(glow::TEXTURE_2D, Some(tex));
            gl.draw_arrays(glow::TRIANGLES, 0, 6);
        }
    }

    fn image_quad(
        &self,
        x: f32,
        y: f32,
        w: f32,
        h: f32,
        uv: [f32; 4],
        tex: glow::Texture,
    ) {
        let [u0, v0, u1, v1] = uv;
        #[rustfmt::skip]
        let vertices: [f32; 48] = [
            x,     y,     u0, v0,  1.0, 1.0, 1.0, 1.0,
            x + w, y,     u1, v0,  1.0, 1.0, 1.0, 1.0,
            x + w, y + h, u1, v1,  1.0, 1.0, 1.0, 1.0,
            x,     y,     u0, v0,  1.0, 1.0, 1.0, 1.0,
            x + w, y + h, u1, v1,  1.0, 1.0, 1.0, 1.0,
            x,     y + h, u0, v1,  1.0, 1.0, 1.0, 1.0,
        ];
        unsafe {
            let gl = &self.gl;
            let mode = gl.get_uniform_location(self.program, "image_mode");
            gl.uniform_1_i32(mode.as_ref(), 1);
            gl.bind_buffer(glow::ARRAY_BUFFER, Some(self.vbo));
            let bytes = std::slice::from_raw_parts(vertices.as_ptr() as *const u8, vertices.len() * 4);
            gl.buffer_data_u8_slice(glow::ARRAY_BUFFER, bytes, glow::STREAM_DRAW);
            gl.active_texture(glow::TEXTURE0);
            gl.bind_texture(glow::TEXTURE_2D, Some(tex));
            gl.draw_arrays(glow::TRIANGLES, 0, 6);
            gl.uniform_1_i32(mode.as_ref(), 0);
        }
    }

    fn artwork_texture(&self, player: &crate::mpris::Snapshot) -> Option<glow::Texture> {
        if player.art_url.is_empty() {
            return None;
        }
        let mut cached = self.artwork.borrow_mut();
        if let Some((url, texture)) = cached.as_ref()
            && url == &player.art_url
        {
            return Some(*texture);
        }
        if let Some((_, texture)) = cached.take() {
            unsafe { self.gl.delete_texture(texture); }
        }
        let image = player.artwork.as_ref()?;
        let texture = unsafe {
            let texture = self.gl.create_texture().ok()?;
            self.gl.bind_texture(glow::TEXTURE_2D, Some(texture));
            self.gl.tex_image_2d(
                glow::TEXTURE_2D,
                0,
                glow::RGBA8 as i32,
                image.width as i32,
                image.height as i32,
                0,
                glow::RGBA,
                glow::UNSIGNED_BYTE,
                glow::PixelUnpackData::Slice(Some(&image.rgba)),
            );
            set_texture_params(&self.gl);
            texture
        };
        *cached = Some((player.art_url.clone(), texture));
        Some(texture)
    }

    fn draw_cover(&self, x: i32, y: i32, w: i32, h: i32, texture: glow::Texture) {
        let aspect = w as f32 / h.max(1) as f32;
        let (u0, u1, v0, v1) = if aspect >= 1.0 {
            let visible = 1.0 / aspect;
            let top = (1.0 - visible) / 2.0;
            (0.0, 1.0, top, top + visible)
        } else {
            let visible = aspect;
            let left = (1.0 - visible) / 2.0;
            (left, left + visible, 0.0, 1.0)
        };
        self.image_quad(x as f32, y as f32, w as f32, h as f32, [u0, v0, u1, v1], texture);
    }

    /// Fills a rectangle (dwm's `drw_rect` with filled = 1).
    pub fn rect(&self, x: i32, y: i32, w: i32, h: i32, color: [f32; 4]) {
        if w <= 0 || h <= 0 {
            return;
        }
        self.quad(x as f32, y as f32, w as f32, h as f32, 1.0, color, self.white);
    }

    /// dwm's `drw_text`: the steps come from the fontset's walk, and are drawn
    /// in the same order (background fill, then each text run).
    pub fn text(&self, x: i32, y: i32, w: i32, h: i32, lpad: i32, text: &str, s: Scheme) {
        for op in self.metrics.text_ops(x, y, w, h, lpad, text) {
            match op {
                Op::Fill { x, y, w, h } => self.rect(x, y, w as i32, h as i32, s.bg),
                Op::Text { font, x, baseline, text } => {
                    let key = (font, text);
                    let cached = self.glyphs.borrow().get(&key).copied();
                    let (tex, tw, th) = match cached {
                        Some(entry) => entry,
                        None => {
                            let Some((buf, tw, th)) = self.metrics.raster(font, &key.1) else {
                                continue;
                            };
                            let tex = upload_coverage(&self.gl, &buf, tw, th);
                            let mut glyphs = self.glyphs.borrow_mut();
                            if glyphs.len() >= GLYPH_CACHE_MAX {
                                for (_, (old, _, _)) in glyphs.drain() {
                                    unsafe { self.gl.delete_texture(old) };
                                }
                            }
                            glyphs.insert(key, (tex, tw as i32, th as i32));
                            (tex, tw as i32, th as i32)
                        }
                    };
                    let asc = self.metrics.ascent(font);
                    self.quad(x as f32, (baseline - asc) as f32, tw as f32, th as f32, 1.0, s.fg, tex);
                }
            }
        }
    }
}

fn set_texture_params(gl: &glow::Context) {
    unsafe {
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_MIN_FILTER, glow::NEAREST as i32);
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_MAG_FILTER, glow::NEAREST as i32);
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_WRAP_S, glow::CLAMP_TO_EDGE as i32);
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_WRAP_T, glow::CLAMP_TO_EDGE as i32);
    }
}

fn upload_coverage(gl: &glow::Context, buf: &[u8], w: usize, h: usize) -> glow::Texture {
    unsafe {
        let tex = gl.create_texture().expect("create_texture");
        gl.bind_texture(glow::TEXTURE_2D, Some(tex));
        gl.tex_image_2d(
            glow::TEXTURE_2D, 0, glow::R8 as i32, w as i32, h as i32, 0,
            glow::RED, glow::UNSIGNED_BYTE, glow::PixelUnpackData::Slice(Some(buf)),
        );
        set_texture_params(gl);
        tex
    }
}

fn link_program(gl: &glow::Context) -> Result<glow::Program> {
    unsafe {
        let program = gl.create_program()?;
        let mut shaders = Vec::new();
        for (kind, src) in [(glow::VERTEX_SHADER, VERT_SRC), (glow::FRAGMENT_SHADER, FRAG_SRC)] {
            let shader = gl.create_shader(kind)?;
            gl.shader_source(shader, src);
            gl.compile_shader(shader);
            if !gl.get_shader_compile_status(shader) {
                return Err(gl.get_shader_info_log(shader).into());
            }
            gl.attach_shader(program, shader);
            shaders.push(shader);
        }
        gl.link_program(program);
        if !gl.get_program_link_status(program) {
            return Err(gl.get_program_info_log(program).into());
        }
        for shader in shaders {
            gl.delete_shader(shader);
        }
        Ok(program)
    }
}

pub const CLRBORDER: u32 = 0x1E1D2D;
/// Background of the bar windows. Area uncovered by a resize shows this color
/// instead of black until the next frame is drawn.
pub const BAR_BACKGROUND_PIXEL: u32 = 0xFF00_0000 | CLRBORDER;
pub const TAG_LABEL: &str = "\u{f192}";
pub const LAYOUT_SYMBOL: &str = "[]=";
/// config.h `launchers`: the Arch logo, U+F303.
pub const LAUNCHERS: [&str; 1] = ["\u{f303}"];
pub const BARGAP: i32 = 10;
pub const CLOCKPAD: i32 = 24;
pub const KBLAYOUTPAD: i32 = 17;
pub const HORIZPADBAR: i32 = 6;
const MPRIS_WIDTH: i32 = 240;
const MPRIS_CONTROL_W: i32 = 34;

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
const MPRIS_SCROLL_PAD: i32 = 8;
pub const TAGS: usize = 5;
const ULINEPAD: i32 = 5;
const ULINESTROKE: i32 = 2;

impl Gl {
    /// Tags section of dwm's `drawbar()`, drawn into `barwin`.
    pub fn draw_tags(&self, win: u32, w: i32, occ: u32, selected: u32, ltsymbol: &str) {
        let bh = self.metrics.bar_height();
        let bh_n = bh - BORDERPX * 2;
        let lrpad = self.metrics.lrpad();
        self.make_current(win);
        self.begin(w, bh, col(CLRBORDER));
        let mut x = BORDERPX;
        for i in 0..TAGS {
            let tw = self.metrics.textw(TAG_LABEL);
            let scheme = if occ & 1 << i != 0 { scheme_tag(i) } else { scheme_norm() };
            self.text(x, BORDERPX, tw, bh_n, lrpad / 2, TAG_LABEL, scheme);
            if selected & 1 << i != 0 {
                self.rect(x + ULINEPAD, bh_n - ULINESTROKE, tw - ULINEPAD * 2, ULINESTROKE, scheme.fg);
            }
            x += tw;
        }
        let lw = self.metrics.textw(ltsymbol);
        self.text(x, 0, lw, bh, lrpad / 2, ltsymbol, scheme_layout());
        self.finish(win);
    }

    /// Title section of dwm's `drawbar()`, drawn into `bartitlewin`.
    pub fn draw_title(&self, win: u32, w: i32, sel: Option<&str>, focused: bool) {
        let bh = self.metrics.bar_height();
        let lrpad = self.metrics.lrpad();
        self.make_current(win);
        self.begin(w, bh, col(CLRBORDER));
        let mut x = BORDERPX;
        for name in LAUNCHERS {
            let lw = self.metrics.textw(name);
            self.text(x, 0, lw, bh, lrpad / 2, name, scheme_layout());
            x += lw;
        }
        if let Some(name) = sel {
            let tw = w - x;
            if tw > 0 {
                let scheme = if focused { scheme_title() } else { scheme_norm() };
                self.text(x, 0, tw, bh, lrpad / 2, name, scheme);
            }
        }
        self.finish(win);
    }

    /// Keyboard layout section of dwm's `drawbar()`, drawn into `barkbwin`.
    pub fn draw_kb(&self, win: u32, w: i32, kb: &str, focused: bool) {
        let bh = self.metrics.bar_height();
        let bh_n = bh - BORDERPX * 2;
        let scheme = if focused { scheme_title() } else { scheme_norm() };
        self.make_current(win);
        self.begin(w, bh, col(CLRBORDER));
        self.rect(0, BORDERPX, w, bh_n, scheme.bg);
        self.text(0, BORDERPX + VERTPADBAR / 2, w, bh - VERTPADBAR, KBLAYOUTPAD, kb, scheme);
        self.finish(win);
    }

    /// Statusbar drawn into `barrightwin` using OpenGL with status2d markup support (^c, ^b, ^d, ^f, ^r).
    pub fn draw_status(&self, win: u32, w: i32, text: &str, scroll_px: u32, progress: Option<f32>) {
        let bh = self.metrics.bar_height();
        self.make_current(win);
        self.begin(w, bh, col(CLRBORDER));
        self.draw_status_contents(w, bh, bh, text, scroll_px, progress, false);
        self.finish(win);
    }

    pub fn draw_mpris_panel(
        &self,
        win: u32,
        w: i32,
        text: &str,
        player: &crate::mpris::Snapshot,
        scroll_px: u32,
        marker_hovered: bool,
    ) {
        let bh = self.metrics.bar_height();
        let panel_h = bh * 2;
        let norm = scheme_norm();
        self.make_current(win);
        self.begin(w, panel_h, norm.bg);
        if let Some(texture) = self.artwork_texture(player) {
            self.draw_cover(0, 0, w, panel_h, texture);
        } else {
            self.rect(0, 0, w, panel_h, norm.bg);
        }

        for band in 0..16 {
            let t = (band as f32 + 0.5) / 16.0;
            let alpha = if t <= 0.25 { 1.0 } else { (1.0 - (t - 0.25) / 0.75).max(0.0) };
            let y = band * panel_h / 16;
            let end = (band + 1) * panel_h / 16;
            self.rect(0, y, w, end - y, [norm.bg[0], norm.bg[1], norm.bg[2], alpha]);
        }

        let (slider_x, slider_w) = mpris_slider_span(w);
        let control_w = MPRIS_CONTROL_W;
        let volume_x = slider_x + slider_w + 6;
        let previous_x = volume_x + 46;
        let next_x = previous_x + control_w;
        let control_y = bh + 4;
        let control_h = (bh - 8).max(1);
        let transparent = [0.0, 0.0, 0.0, 0.0];
        let control = Scheme { fg: scheme_title().fg, bg: transparent };
        self.text(10, control_y, 28, control_h, 0, if player.playing { "" } else { "" }, control);
        self.text(previous_x, control_y, 28, control_h, 0, "", control);
        self.text(next_x, control_y, 28, control_h, 0, "", control);

        let track_y = bh + bh / 2 - 2;
        let fill_w = (slider_w as f32 * crate::mpris::volume_position(player.volume)).round() as i32;
        let knob_w = mpris_knob(w, bh, player.volume, marker_hovered).2;
        let mut empty = col(0xA6DA95);
        empty[3] = 0.55;
        self.rect(slider_x, track_y, slider_w, 4, empty);
        self.rect(slider_x, track_y, fill_w, 4, col(0xB8E9B4));
        self.rect(slider_x + fill_w, track_y + 1, knob_w / 2, 2, col(0xB8E9B4));
        self.text(
            volume_x,
            control_y,
            38,
            control_h,
            0,
            &format!("{}%", (player.volume * 100.0).round() as u32),
            control,
        );

        self.draw_status_contents(w, bh, panel_h, text, scroll_px, player.progress, true);
        self.finish(win);
    }

    fn draw_status_contents(
        &self,
        w: i32,
        bh: i32,
        canvas_h: i32,
        text: &str,
        scroll_px: u32,
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

        let mut cur_fg = norm.fg;
        let mut cur_bg = norm.bg;
        let mut has_bg = false;

        let tokens = crate::status::parse_status(text);
        for token in tokens {
            match token {
                crate::status::StatusToken::Text(s) => {
                    if !s.is_empty() {
                        let tw = self.metrics.text_width(&s);
                        let bg = if has_bg { cur_bg } else if expanded { [0.0, 0.0, 0.0, 0.0] } else { norm.bg };
                        self.text(x, y, tw, content_h, 0, &s, Scheme { fg: cur_fg, bg });
                        x += tw;
                    }
                }
                crate::status::StatusToken::ScrollText(s) => {
                    let field_w = (self.metrics.text_width(&s) + 2 * MPRIS_SCROLL_PAD)
                        .min(MPRIS_WIDTH)
                        .max(1);
                    let text_w = self.metrics.text_width(&s).max(1);
                    let bg = col(0xA6DA95);
                    self.rect(x, y, field_w, content_h, bg);
                    if let Some(progress) = progress {
                        let progress_w = (field_w as f32 * progress.clamp(0.0, 1.0)).round() as i32;
                        self.rect(x, y, progress_w, content_h, col(0xB8E9B4));
                    }
                    let cycle = text_w + 32;
                    let offset = if text_w + 2 * MPRIS_SCROLL_PAD > MPRIS_WIDTH {
                        scroll_px as i32 % cycle
                    } else {
                        0
                    };
                    let clip_x = x + MPRIS_SCROLL_PAD;
                    let clip_w = (field_w - 2 * MPRIS_SCROLL_PAD).max(0);
                    unsafe {
                        self.gl.enable(glow::SCISSOR_TEST);
                        self.gl.scissor(clip_x, canvas_h - (y + content_h), clip_w, content_h);
                    }
                    for copy in -1..=1 {
                        let text_x = x + MPRIS_SCROLL_PAD - offset + copy * cycle;
                        if text_x < x + field_w && text_x + text_w > clip_x {
                            self.text(
                                text_x,
                                y,
                                text_w,
                                content_h,
                                0,
                                &s,
                                Scheme { fg: cur_fg, bg: [0.0, 0.0, 0.0, 0.0] },
                            );
                        }
                    }
                    unsafe { self.gl.disable(glow::SCISSOR_TEST); }
                    x += field_w;
                }
                crate::status::StatusToken::Fg(c) => cur_fg = c,
                crate::status::StatusToken::Bg(c) => {
                    cur_bg = c;
                    has_bg = true;
                }
                crate::status::StatusToken::Reset => {
                    cur_fg = norm.fg;
                    cur_bg = norm.bg;
                    has_bg = false;
                }
                crate::status::StatusToken::Forward(f) => x += f,
                crate::status::StatusToken::Rect(rx, ry, rw, rh) => {
                    self.rect(x + rx, y + ry, rw as i32, rh as i32, cur_fg);
                }
            }
        }
    }
}
