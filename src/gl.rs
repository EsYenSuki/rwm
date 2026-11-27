//! EGL X11 pixmap surface, OpenGL entry-point loading and Kawase bloom for the
//! finder and notification renderers.
//!
//! Port of AnDWM `dwm.c` 7581-7638 (`notification_gl_init`), 8496-8700
//! (`finder_gl_proc`, `finder_gl_bloom_load_procs`, shader/program/buffers/quad)
//! and 11639-11927 (the five-pass blur/composite used by the finder icons,
//! text and waiting backdrop). The context is a **legacy compatibility** one
//! created with `eglCreateContext` and no profile attributes: the shaders are
//! GLSL v120 and the quads use the fixed-function matrix stack, so a core-only
//! context must never be requested here.
//!
//! Rendering goes straight into an ARGB32 X pixmap via EGL. XRender composes
//! that pixmap into the final frame, so there is no GLX pbuffer and no
//! `glReadPixels`/`XPutImage` copy of the whole popup on every frame. The
//! `gl` 0.14 crate intentionally omits deprecated fixed-function symbols, so
//! `glBegin`/`glVertex2f`/matrix-stack functions are loaded separately via
//! `eglGetProcAddress` and wrapped in [`CompatGl`].

// The context, loader and bloom are consumed by the font/presentation tasks
// that follow; keep a clean build while this module is still standalone.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{CStr, CString, c_char, c_int, c_uint, c_void};
use std::ptr;
use std::sync::OnceLock;

use freetype_sys::{
    FT_Bitmap, FT_Error, FT_Face, FT_GlyphSlot, FT_Load_Glyph, FT_Render_Glyph, FT_Render_Mode,
    FT_UInt, FT_ULong,
};
use gl::types::{GLchar, GLdouble, GLenum, GLfloat, GLint, GLsizei, GLuint};
use x11::xlib;
use x11::xrender;

use crate::egl;

// These two matrix-stack tokens are missing from the `gl` 0.14 constants even
// though the compatibility context uses them.
const GL_MODELVIEW: GLenum = 0x1700;
const GL_PROJECTION: GLenum = 0x1701;

/// dwm.c 8592-8595: `gl_MultiTexCoord0.st` plus `ftransform()` is pure v120
/// fixed-function vertex shading.
const BLOOM_VERTEX_SOURCE: &str = concat!(
    "#version 120\n",
    "varying vec2 uv;\n",
    "void main() { uv = gl_MultiTexCoord0.st; gl_Position = ftransform(); }\n",
);

/// dwm.c 8596-8616: 9-tap Kawase kernel. Mode 0 uses the four diagonal taps at
/// 0.1875; mode 1 adds four axis-aligned taps and reweights the centre/corners.
const BLOOM_FRAGMENT_SOURCE: &str = concat!(
    "#version 120\n",
    "uniform sampler2D source;\n",
    "uniform vec2 texel_size;\n",
    "uniform int mode;\n",
    "varying vec2 uv;\n",
    "void main() {\n",
    "  vec2 d = texel_size;\n",
    "  vec4 c = texture2D(source, uv) * (mode == 0 ? 0.25 : 0.20);\n",
    "  c += texture2D(source, uv + vec2( d.x,  d.y)) * (mode == 0 ? 0.1875 : 0.10);\n",
    "  c += texture2D(source, uv + vec2(-d.x,  d.y)) * (mode == 0 ? 0.1875 : 0.10);\n",
    "  c += texture2D(source, uv + vec2( d.x, -d.y)) * (mode == 0 ? 0.1875 : 0.10);\n",
    "  c += texture2D(source, uv + vec2(-d.x, -d.y)) * (mode == 0 ? 0.1875 : 0.10);\n",
    "  if (mode != 0) {\n",
    "    c += texture2D(source, uv + vec2( d.x, 0.0)) * 0.10;\n",
    "    c += texture2D(source, uv + vec2(-d.x, 0.0)) * 0.10;\n",
    "    c += texture2D(source, uv + vec2(0.0,  d.y)) * 0.10;\n",
    "    c += texture2D(source, uv + vec2(0.0, -d.y)) * 0.10;\n",
    "  }\n",
    "  gl_FragColor = c;\n",
    "}\n",
);

/// dwm.c 11647, 11727, 11840: two downsample-style passes, a wide 1.5 pass,
/// then two upsample-style passes.
const BLOOM_PASS_SCALES: [GLfloat; 5] = [0.5, 1.0, 1.5, 1.0, 0.5];

const SOURCE_TEX: usize = 0;
const PING_TEX: usize = 1;
const PONG_TEX: usize = 2;

pub type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

type FnBegin = unsafe extern "C" fn(GLenum);
type FnEnd = unsafe extern "C" fn();
type FnColor4f = unsafe extern "C" fn(GLfloat, GLfloat, GLfloat, GLfloat);
type FnLoadIdentity = unsafe extern "C" fn();
type FnMatrixMode = unsafe extern "C" fn(GLenum);
type FnOrtho = unsafe extern "C" fn(GLdouble, GLdouble, GLdouble, GLdouble, GLdouble, GLdouble);
type FnPopMatrix = unsafe extern "C" fn();
type FnPushMatrix = unsafe extern "C" fn();
type FnScalef = unsafe extern "C" fn(GLfloat, GLfloat, GLfloat);
type FnTexCoord2f = unsafe extern "C" fn(GLfloat, GLfloat);
type FnTexEnvf = unsafe extern "C" fn(GLenum, GLenum, GLfloat);
type FnTexEnvi = unsafe extern "C" fn(GLenum, GLenum, GLint);
type FnTranslatef = unsafe extern "C" fn(GLfloat, GLfloat, GLfloat);
type FnVertex2f = unsafe extern "C" fn(GLfloat, GLfloat);

/// `gl` 0.14 does not generate the OpenGL 1.x fixed-function entry points that
/// dwm uses directly. They are resolved once, while the EGL context is
/// current, from the same `eglGetProcAddress` table as everything else.
pub struct CompatGl {
    begin_fn: FnBegin,
    end_fn: FnEnd,
    color4f_fn: FnColor4f,
    load_identity_fn: FnLoadIdentity,
    matrix_mode_fn: FnMatrixMode,
    ortho_fn: FnOrtho,
    pop_matrix_fn: FnPopMatrix,
    push_matrix_fn: FnPushMatrix,
    scalef_fn: FnScalef,
    tex_coord2f_fn: FnTexCoord2f,
    tex_envf_fn: FnTexEnvf,
    tex_envi_fn: FnTexEnvi,
    translatef_fn: FnTranslatef,
    vertex2f_fn: FnVertex2f,
}

impl CompatGl {
    fn load() -> Result<CompatGl> {
        Ok(CompatGl {
            begin_fn: load_fn("glBegin")?,
            end_fn: load_fn("glEnd")?,
            color4f_fn: load_fn("glColor4f")?,
            load_identity_fn: load_fn("glLoadIdentity")?,
            matrix_mode_fn: load_fn("glMatrixMode")?,
            ortho_fn: load_fn("glOrtho")?,
            pop_matrix_fn: load_fn("glPopMatrix")?,
            push_matrix_fn: load_fn("glPushMatrix")?,
            scalef_fn: load_fn("glScalef")?,
            tex_coord2f_fn: load_fn("glTexCoord2f")?,
            tex_envf_fn: load_fn("glTexEnvf")?,
            tex_envi_fn: load_fn("glTexEnvi")?,
            translatef_fn: load_fn("glTranslatef")?,
            vertex2f_fn: load_fn("glVertex2f")?,
        })
    }

    pub fn begin(&self, mode: GLenum) {
        unsafe { (self.begin_fn)(mode) }
    }
    pub fn end(&self) {
        unsafe { (self.end_fn)() }
    }
    pub fn color4f(&self, r: GLfloat, g: GLfloat, b: GLfloat, a: GLfloat) {
        unsafe { (self.color4f_fn)(r, g, b, a) }
    }
    pub fn load_identity(&self) {
        unsafe { (self.load_identity_fn)() }
    }
    pub fn matrix_mode(&self, mode: GLenum) {
        unsafe { (self.matrix_mode_fn)(mode) }
    }
    pub fn ortho(
        &self,
        left: GLdouble,
        right: GLdouble,
        bottom: GLdouble,
        top: GLdouble,
        near: GLdouble,
        far: GLdouble,
    ) {
        unsafe { (self.ortho_fn)(left, right, bottom, top, near, far) }
    }
    pub fn pop_matrix(&self) {
        unsafe { (self.pop_matrix_fn)() }
    }
    pub fn push_matrix(&self) {
        unsafe { (self.push_matrix_fn)() }
    }
    pub fn scalef(&self, x: GLfloat, y: GLfloat, z: GLfloat) {
        unsafe { (self.scalef_fn)(x, y, z) }
    }
    pub fn tex_coord2f(&self, s: GLfloat, t: GLfloat) {
        unsafe { (self.tex_coord2f_fn)(s, t) }
    }
    pub fn tex_envf(&self, target: GLenum, pname: GLenum, param: GLfloat) {
        unsafe { (self.tex_envf_fn)(target, pname, param) }
    }
    pub fn tex_envi(&self, target: GLenum, pname: GLenum, param: GLint) {
        unsafe { (self.tex_envi_fn)(target, pname, param) }
    }
    pub fn translatef(&self, x: GLfloat, y: GLfloat, z: GLfloat) {
        unsafe { (self.translatef_fn)(x, y, z) }
    }
    pub fn vertex2f(&self, x: GLfloat, y: GLfloat) {
        unsafe { (self.vertex2f_fn)(x, y) }
    }
}

static COMPAT_GL: OnceLock<CompatGl> = OnceLock::new();

pub fn compat() -> Result<&'static CompatGl> {
    if let Some(loaded) = COMPAT_GL.get() {
        return Ok(loaded);
    }
    let loaded = CompatGl::load()?;
    let _ = COMPAT_GL.set(loaded);
    COMPAT_GL
        .get()
        .ok_or_else(|| "cannot cache compatibility GL entry points".into())
}

fn load_fn<T: Copy>(name: &str) -> Result<T> {
    let proc = proc_address(name);
    if proc.is_null() {
        return Err(format!("EGL is missing compatibility entry point {name}").into());
    }
    // Function pointers and data pointers have the same representation on the
    // supported X11/GL platforms; transmute_copy keeps the raw pointer alive
    // for the copy without pretending it is a reference to a function.
    unsafe { Ok(std::mem::transmute_copy::<*mut c_void, T>(&proc)) }
}

/// dwm.c 8496-8498: resolve one GL entry point through `eglGetProcAddress`.
/// A null pointer is returned for unknown names so the `gl` crate can apply its
/// own EXT fallbacks, exactly like dwm's `...EXT` retry list.
fn proc_address(name: &str) -> *mut c_void {
    egl::proc_address(name)
}

/// Every `gl::...` function used by the bloom and presentation paths must be
/// present after [`load_gl`], either as a core symbol or an EXT fallback.
fn gl_symbols_loaded() -> bool {
    gl::GenFramebuffers::is_loaded()
        && gl::BindFramebuffer::is_loaded()
        && gl::FramebufferTexture2D::is_loaded()
        && gl::CheckFramebufferStatus::is_loaded()
        && gl::DeleteFramebuffers::is_loaded()
        && gl::CreateShader::is_loaded()
        && gl::ShaderSource::is_loaded()
        && gl::CompileShader::is_loaded()
        && gl::GetShaderiv::is_loaded()
        && gl::CreateProgram::is_loaded()
        && gl::AttachShader::is_loaded()
        && gl::LinkProgram::is_loaded()
        && gl::GetProgramiv::is_loaded()
        && gl::UseProgram::is_loaded()
        && gl::GetUniformLocation::is_loaded()
        && gl::Uniform1i::is_loaded()
        && gl::Uniform2f::is_loaded()
        && gl::DeleteShader::is_loaded()
        && gl::DeleteProgram::is_loaded()
        && gl::GenTextures::is_loaded()
        && gl::DeleteTextures::is_loaded()
        && gl::BindTexture::is_loaded()
        && gl::TexImage2D::is_loaded()
        && gl::TexParameteri::is_loaded()
        && gl::Viewport::is_loaded()
        && gl::ClearColor::is_loaded()
        && gl::Clear::is_loaded()
        && gl::Enable::is_loaded()
        && gl::Disable::is_loaded()
        && gl::IsEnabled::is_loaded()
        && gl::ActiveTexture::is_loaded()
        && gl::BlendFunc::is_loaded()
}

/// dwm.c 8500-8567: load all GL symbols through `eglGetProcAddress` while
/// the context is current, then require the bloom/shader subset. The loader
/// retries the `...EXT` spelling for the framebuffer functions, as dwm does at
/// 8543-8558. The `gl` crate already has most of these fallbacks internally but
/// notably lacks one for `glBindFramebuffer`, so the full list is supplied here.
fn load_gl() -> Result {
    gl::load_with(|name| {
        let mut proc = proc_address(name);
        if proc.is_null() {
            let ext = match name {
                "glGenFramebuffers" => "glGenFramebuffersEXT",
                "glBindFramebuffer" => "glBindFramebufferEXT",
                "glDeleteFramebuffers" => "glDeleteFramebuffersEXT",
                "glFramebufferTexture2D" => "glFramebufferTexture2DEXT",
                "glCheckFramebufferStatus" => "glCheckFramebufferStatusEXT",
                _ => return proc,
            };
            proc = proc_address(ext);
        }
        proc
    });

    if !gl_symbols_loaded() {
        return Err("EGL is missing framebuffer or shader entry points".into());
    }
    // Also resolve the fixed-function symbols that `gl` 0.14 does not expose.
    compat()?;
    Ok(())
}

/// dwm.c 7640-7645 (`notification_gl_blend_separate`): use the separate alpha
/// blend equation when available, otherwise fall back to the core 1.0 form.
fn blend_separate() {
    unsafe {
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
    }
}

/// The EGL display, config and compatibility context shared by one surface.
/// Kept separate from [`EglSurface`] so a resize only recreates the X pixmap
/// and EGL surface; glyph textures and bloom buffers stay bound to the context.
struct EglContext {
    dpy: egl::EGLDisplay,
    config: egl::EGLConfig,
    ctx: egl::EGLContext,
}

impl EglContext {
    /// Create a legacy compatibility OpenGL context on the ARGB32 X visual.
    /// No profile/version attributes are passed, so GLSL v120 and the
    /// fixed-function matrix stack remain available.
    fn new(xdpy: *mut xlib::Display, visual: *mut xlib::Visual) -> Result<EglContext> {
        if xdpy.is_null() || visual.is_null() {
            return Err("EGL needs an X display and an ARGB32 visual".into());
        }
        unsafe {
            let visual_id = (*visual).visualid as egl::EGLint;
            let dpy = egl::platform_display(xdpy.cast());
            if dpy.is_null() {
                return Err("cannot open the EGL X11 display".into());
            }
            if egl::initialize(dpy) == 0 {
                let err = egl::error("eglInitialize");
                egl::terminate(dpy);
                return Err(format!("cannot initialize EGL: {err}").into());
            }
            if egl::bind_api(egl::OPENGL_API) == 0 {
                let err = egl::error("eglBindAPI");
                egl::terminate(dpy);
                return Err(format!("cannot select the EGL OpenGL API: {err}").into());
            }

            let attrs: [egl::EGLint; 13] = [
                egl::SURFACE_TYPE,
                egl::PIXMAP_BIT,
                egl::RENDERABLE_TYPE,
                egl::OPENGL_BIT,
                egl::RED_SIZE,
                8,
                egl::GREEN_SIZE,
                8,
                egl::BLUE_SIZE,
                8,
                egl::ALPHA_SIZE,
                8,
                egl::NONE,
            ];
            let mut config: egl::EGLConfig = ptr::null_mut();
            let mut count: egl::EGLint = 0;
            if egl::choose_config(dpy, attrs.as_ptr(), &mut config, &mut count) == 0
                || count == 0
                || config.is_null()
            {
                let err = egl::error("eglChooseConfig");
                egl::terminate(dpy);
                return Err(format!("EGL has no ARGB32 pixmap config: {err}").into());
            }
            // Prefer the exact ARGB32 visual XRender will use. Some drivers do
            // not report native visual IDs for pixmap configs; in that case the
            // RGBA8888 config above is still the right pixel layout.
            let mut matched = config;
            let mut nmatched: egl::EGLint = 0;
            let with_visual: [egl::EGLint; 15] = [
                egl::SURFACE_TYPE,
                egl::PIXMAP_BIT,
                egl::RENDERABLE_TYPE,
                egl::OPENGL_BIT,
                egl::RED_SIZE,
                8,
                egl::GREEN_SIZE,
                8,
                egl::BLUE_SIZE,
                8,
                egl::ALPHA_SIZE,
                8,
                egl::NATIVE_VISUAL_ID,
                visual_id,
                egl::NONE,
            ];
            if egl::choose_config(dpy, with_visual.as_ptr(), &mut matched, &mut nmatched) != 0
                && nmatched > 0
                && !matched.is_null()
            {
                config = matched;
            }

            let ctx = egl::create_context(dpy, config);
            if ctx.is_null() {
                let err = egl::error("eglCreateContext");
                egl::terminate(dpy);
                return Err(format!("cannot create EGL compatibility context: {err}").into());
            }
            Ok(EglContext { dpy, config, ctx })
        }
    }

    fn make_current(&self, surface: egl::EGLSurface) -> Result {
        if egl::make_current(self.dpy, surface, self.ctx) == 0 {
            return Err(format!(
                "cannot bind EGL pixmap surface: {}",
                egl::error("eglMakeCurrent")
            )
            .into());
        }
        Ok(())
    }
}

impl Drop for EglContext {
    fn drop(&mut self) {
        egl::release_current(self.dpy);
        egl::destroy_context(self.dpy, self.ctx);
        egl::terminate(self.dpy);
    }
}

/// dwm.c 8569-8589: compile one v120 shader and include the driver's log on
/// failure. Info logs are optional; compile status and deletion are required.
fn compile_shader(kind: GLenum, source: &str) -> Result<GLuint> {
    let shader = unsafe { gl::CreateShader(kind) };
    if shader == 0 {
        return Err("cannot create finder bloom shader".into());
    }
    let source = CString::new(source).expect("shader source contains no NUL byte");
    let sources = [source.as_ptr()];
    unsafe {
        gl::ShaderSource(shader, 1, sources.as_ptr(), ptr::null());
        gl::CompileShader(shader);

        let mut ok: GLint = 0;
        gl::GetShaderiv(shader, gl::COMPILE_STATUS, &mut ok);
        if ok == 0 {
            let detail = shader_log(true, shader);
            gl::DeleteShader(shader);
            return Err(format!("finder bloom shader compile failed{detail}").into());
        }
    }
    Ok(shader)
}

/// Reads an optional shader/program info log. `is_shader` selects the shader
/// or program entry point; the returned string is empty when the driver does
/// not expose the query.
fn shader_log(is_shader: bool, object: GLuint) -> String {
    unsafe {
        if is_shader {
            if !gl::GetShaderInfoLog::is_loaded() {
                return String::new();
            }
        } else if !gl::GetProgramInfoLog::is_loaded() {
            return String::new();
        }

        let mut log: [GLchar; 512] = [0; 512];
        let mut len: GLsizei = 0;
        if is_shader {
            gl::GetShaderInfoLog(object, 512, &mut len, log.as_mut_ptr());
        } else {
            gl::GetProgramInfoLog(object, 512, &mut len, log.as_mut_ptr());
        }
        let len = (len.max(0) as usize).min(log.len());
        if len == 0 {
            return String::new();
        }
        let bytes: Vec<u8> = log[..len].iter().map(|&b| b as u8).collect();
        format!(": {}", String::from_utf8_lossy(&bytes))
    }
}

fn uniform_location(program: GLuint, name: &str) -> Result<GLint> {
    let cname = CString::new(name).expect("uniform name contains no NUL byte");
    let location = unsafe { gl::GetUniformLocation(program, cname.as_ptr()) };
    if location < 0 {
        Err(format!("finder bloom program is missing uniform {name}").into())
    } else {
        Ok(location)
    }
}

/// The per-row transform dwm applies around the row centre before drawing the
/// source into the bloom FBO. `center_y` is `row_y + text_h / 2` for text and
/// `row_y + bh / 2` for icons; the X centre is always `width / 2`.
#[derive(Clone, Copy, Debug)]
pub struct BloomTransform {
    /// Y centre used for the scale, matching the row/text centre.
    pub center_y: GLfloat,
    /// Translation applied after scaling. Finder's waiting query scales around
    /// `bh / 2` and then shifts down by `6 * query_pose`; using only `center_y`
    /// would scale around the shifted point and leave the glow behind the text.
    pub offset_y: GLfloat,
    pub scale_x: GLfloat,
    pub scale_y: GLfloat,
}

impl BloomTransform {
    /// Final Y coordinate of an untransformed `y` after this transform.
    pub fn map_y(&self, y: GLfloat) -> GLfloat {
        self.offset_y + self.center_y + self.scale_y * (y - self.center_y)
    }
}

/// Owns the v120 Kawase program and its three RGBA textures plus one FBO.
/// Buffers are allocated lazily by [`Bloom::ensure_buffers`] and reused while
/// the requested size is unchanged, exactly like dwm's `finder_bloom_*` state.
pub struct Bloom {
    program: GLuint,
    texture_uniform: GLint,
    texel_uniform: GLint,
    mode_uniform: GLint,
    fbo: GLuint,
    textures: [GLuint; 3],
    width: u32,
    height: u32,
}

impl Bloom {
    /// dwm.c 8591-8651: compile, link and validate the blur program. The
    /// shaders are detached and deleted after linking, as in dwm 8631-8632.
    pub fn new() -> Result<Bloom> {
        let vertex = compile_shader(gl::VERTEX_SHADER, BLOOM_VERTEX_SOURCE)?;
        let fragment = match compile_shader(gl::FRAGMENT_SHADER, BLOOM_FRAGMENT_SOURCE) {
            Ok(shader) => shader,
            Err(e) => {
                unsafe { gl::DeleteShader(vertex) };
                return Err(e);
            }
        };

        unsafe {
            let program = gl::CreateProgram();
            if program == 0 {
                gl::DeleteShader(vertex);
                gl::DeleteShader(fragment);
                return Err("cannot create finder bloom program".into());
            }
            gl::AttachShader(program, vertex);
            gl::AttachShader(program, fragment);
            gl::LinkProgram(program);

            let mut ok: GLint = 0;
            gl::GetProgramiv(program, gl::LINK_STATUS, &mut ok);
            gl::DeleteShader(vertex);
            gl::DeleteShader(fragment);
            if ok == 0 {
                let detail = shader_log(false, program);
                gl::DeleteProgram(program);
                return Err(format!("finder bloom program link failed{detail}").into());
            }

            let uniforms = (|| -> Result<(GLint, GLint, GLint)> {
                Ok((
                    uniform_location(program, "source")?,
                    uniform_location(program, "texel_size")?,
                    uniform_location(program, "mode")?,
                ))
            })();
            let (texture_uniform, texel_uniform, mode_uniform) = match uniforms {
                Ok(uniforms) => uniforms,
                Err(e) => {
                    gl::DeleteProgram(program);
                    return Err(e);
                }
            };

            Ok(Bloom {
                program,
                texture_uniform,
                texel_uniform,
                mode_uniform,
                fbo: 0,
                textures: [0; 3],
                width: 0,
                height: 0,
            })
        }
    }

    /// True while the blur program is valid, the equivalent of dwm's
    /// `finder_bloom_ready`. Buffers may still be unallocated until the first
    /// [`Bloom::ensure_buffers`] or [`Bloom::render`] call.
    pub fn ready(&self) -> bool {
        self.program != 0
    }

    /// Current source/ping/pong buffer dimensions.
    pub fn size(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    /// The fixed finder height (`finder_bloom_h`) used by the per-row calls.
    pub fn height(&self) -> u32 {
        self.height
    }

    /// dwm.c 8665-8689: (re)allocate source, ping and pong textures and the
    /// FBO. A framebuffer completeness check is added on top of dwm's
    /// `fbo != 0` test so an unusable driver fails early instead of rendering
    /// into an incomplete attachment.
    pub fn ensure_buffers(&mut self, width: u32, height: u32) -> Result<()> {
        if width == 0 || height == 0 {
            return Err("bloom buffer dimensions must be non-zero".into());
        }
        if self.fbo != 0 && self.width == width && self.height == height {
            return Ok(());
        }
        self.delete_buffers();

        unsafe {
            let mut textures = [0; 3];
            gl::GenTextures(3, textures.as_mut_ptr());
            if textures.contains(&0) {
                gl::DeleteTextures(3, textures.as_ptr());
                return Err("cannot create bloom textures".into());
            }
            for &texture in &textures {
                gl::BindTexture(gl::TEXTURE_2D, texture);
                gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MIN_FILTER, gl::LINEAR as GLint);
                gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MAG_FILTER, gl::LINEAR as GLint);
                gl::TexParameteri(
                    gl::TEXTURE_2D,
                    gl::TEXTURE_WRAP_S,
                    gl::CLAMP_TO_EDGE as GLint,
                );
                gl::TexParameteri(
                    gl::TEXTURE_2D,
                    gl::TEXTURE_WRAP_T,
                    gl::CLAMP_TO_EDGE as GLint,
                );
                gl::TexImage2D(
                    gl::TEXTURE_2D,
                    0,
                    gl::RGBA as GLint,
                    width as GLsizei,
                    height as GLsizei,
                    0,
                    gl::RGBA,
                    gl::UNSIGNED_BYTE,
                    ptr::null(),
                );
            }
            gl::BindTexture(gl::TEXTURE_2D, 0);

            let mut fbo = 0;
            gl::GenFramebuffers(1, &mut fbo);
            if fbo == 0 {
                gl::DeleteTextures(3, textures.as_ptr());
                return Err("cannot create bloom framebuffer".into());
            }
            gl::BindFramebuffer(gl::FRAMEBUFFER, fbo);
            gl::FramebufferTexture2D(
                gl::FRAMEBUFFER,
                gl::COLOR_ATTACHMENT0,
                gl::TEXTURE_2D,
                textures[SOURCE_TEX],
                0,
            );
            let status = gl::CheckFramebufferStatus(gl::FRAMEBUFFER);
            gl::BindFramebuffer(gl::FRAMEBUFFER, 0);
            if status != gl::FRAMEBUFFER_COMPLETE {
                gl::DeleteFramebuffers(1, &fbo);
                gl::DeleteTextures(3, textures.as_ptr());
                return Err(format!("bloom framebuffer is incomplete: {status:#x}").into());
            }

            self.textures = textures;
            self.fbo = fbo;
            self.width = width;
            self.height = height;
        }
        Ok(())
    }

    /// dwm.c 8653-8663: release the FBO and all three textures and reset the
    /// cached dimensions. Called by [`Bloom::ensure_buffers`] on resize and by
    /// the finder teardown task.
    pub fn delete_buffers(&mut self) {
        unsafe {
            if self.fbo != 0 {
                gl::DeleteFramebuffers(1, &self.fbo);
                self.fbo = 0;
            }
            if self.textures.iter().any(|&texture| texture != 0) {
                gl::DeleteTextures(3, self.textures.as_ptr());
                self.textures = [0; 3];
            }
        }
        self.width = 0;
        self.height = 0;
    }

    /// dwm.c 11639-11721, 11723-11790 and 11835-11927: render `draw_source`
    /// into the source texture, run the five Kawase passes and composite the
    /// result onto the currently bound default framebuffer with `alpha`.
    ///
    /// The closure runs after `glOrtho(0, width, height, 0, -1, 1)` and the
    /// optional row transform are installed, with the FBO bound. It owns its
    /// own texture/blend state; the waiting-backdrop caller must disable
    /// `GL_TEXTURE_2D` before drawing a plain colour quad, as dwm does at
    /// 11868. Returns `false` without drawing when blur or alpha is negligible
    /// (the caller then draws the source unblurred), matching dwm 11815-11832.
    pub fn render<F>(
        &mut self,
        target: GLuint,
        width: u32,
        height: u32,
        blur: GLfloat,
        alpha: GLfloat,
        transform: Option<BloomTransform>,
        draw_source: F,
    ) -> Result<bool>
    where
        F: FnOnce(),
    {
        if !self.ready() || width == 0 || height == 0 || alpha <= 0.001 || blur <= 0.001 {
            return Ok(false);
        }
        self.ensure_buffers(width, height)?;
        let c = compat()?;

        unsafe {
            let state = BloomState::new(c, width, height)?;

            gl::BindFramebuffer(gl::FRAMEBUFFER, self.fbo);
            gl::FramebufferTexture2D(
                gl::FRAMEBUFFER,
                gl::COLOR_ATTACHMENT0,
                gl::TEXTURE_2D,
                self.textures[SOURCE_TEX],
                0,
            );
            gl::Viewport(0, 0, width as GLsizei, height as GLsizei);
            gl::ClearColor(0.0, 0.0, 0.0, 0.0);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            gl::Enable(gl::BLEND);
            blend_separate();

            if let Some(t) = transform {
                c.push_matrix();
                c.translatef(0.0, t.offset_y, 0.0);
                c.translatef(width as GLfloat / 2.0, t.center_y, 0.0);
                c.scalef(t.scale_x, t.scale_y, 1.0);
                c.translatef(-(width as GLfloat / 2.0), -t.center_y, 0.0);
            }
            draw_source();
            if transform.is_some() {
                c.pop_matrix();
            }
            gl::Disable(gl::BLEND);

            gl::UseProgram(self.program);
            gl::Enable(gl::TEXTURE_2D);
            gl::Uniform1i(self.texture_uniform, 0);
            gl::Uniform1i(self.mode_uniform, 0);

            let mut input = self.textures[SOURCE_TEX];
            let mut output = self.textures[PING_TEX];
            let w = width as GLfloat;
            let h = height as GLfloat;
            for (pass, &scale) in BLOOM_PASS_SCALES.iter().enumerate() {
                if pass == 2 {
                    gl::Uniform1i(self.mode_uniform, 1);
                }
                gl::FramebufferTexture2D(
                    gl::FRAMEBUFFER,
                    gl::COLOR_ATTACHMENT0,
                    gl::TEXTURE_2D,
                    output,
                    0,
                );
                gl::Clear(gl::COLOR_BUFFER_BIT);
                gl::ActiveTexture(gl::TEXTURE0);
                gl::BindTexture(gl::TEXTURE_2D, input);
                gl::Uniform2f(self.texel_uniform, blur * scale / w, blur * scale / h);
                self.draw_quad(c);

                let drawn = output;
                input = drawn;
                output = if drawn == self.textures[PING_TEX] {
                    self.textures[PONG_TEX]
                } else {
                    self.textures[PING_TEX]
                };
            }

            gl::UseProgram(0);
            gl::BindFramebuffer(gl::FRAMEBUFFER, target);
            // Offscreen passes deliberately ignore the caller's scissor so the
            // FBO is cleared and blurred across its full extent. Restore it
            // before the final composite so callers can clip bloom output (for
            // example Finder's app list must not paint over the clock row).
            state.restore_scissor();
            gl::Enable(gl::BLEND);
            blend_separate();
            gl::BindTexture(gl::TEXTURE_2D, input);
            c.color4f(1.0, 1.0, 1.0, alpha);
            self.draw_quad(c);
            gl::Disable(gl::BLEND);
            gl::Disable(gl::TEXTURE_2D);
            gl::BindTexture(gl::TEXTURE_2D, 0);
        }
        Ok(true)
    }

    /// dwm.c 8691-8701: FBO textures have a bottom-left origin while the
    /// finder projection is top-left, so the quad's V coordinates are flipped.
    fn draw_quad(&self, c: &CompatGl) {
        let w = self.width as GLfloat;
        let h = self.height as GLfloat;
        c.begin(gl::QUADS);
        c.tex_coord2f(0.0, 1.0);
        c.vertex2f(0.0, 0.0);
        c.tex_coord2f(1.0, 1.0);
        c.vertex2f(w, 0.0);
        c.tex_coord2f(1.0, 0.0);
        c.vertex2f(w, h);
        c.tex_coord2f(0.0, 0.0);
        c.vertex2f(0.0, h);
        c.end();
    }
}

/// Saves the fixed-function state that dwm pushes/disables around a bloom draw
/// and restores it on every exit path. The scissor is disabled for the offscreen
/// passes but re-enabled for the final composite, so a caller's clip still
/// applies to what is actually painted. This mirrors 11654-11655, 11656-11662,
/// 11713-11719 and 11918-11925 without duplicating the restore sequence in
/// each of the three original call sites.
struct BloomState {
    compat: &'static CompatGl,
    scissor: bool,
}

impl BloomState {
    fn new(c: &'static CompatGl, width: u32, height: u32) -> Result<BloomState> {
        let scissor;
        unsafe {
            scissor = gl::IsEnabled(gl::SCISSOR_TEST) != 0;
            if scissor {
                gl::Disable(gl::SCISSOR_TEST);
            }
            c.matrix_mode(GL_PROJECTION);
            c.push_matrix();
            c.load_identity();
            c.ortho(0.0, width as f64, height as f64, 0.0, -1.0, 1.0);
            c.matrix_mode(GL_MODELVIEW);
            c.push_matrix();
            c.load_identity();
        }
        Ok(BloomState { compat: c, scissor })
    }

    /// Re-enable the caller's scissor before the final on-screen composite.
    /// The offscreen passes still run unclipped so blur can sample the whole
    /// source texture; only the output is constrained.
    fn restore_scissor(&self) {
        if self.scissor {
            unsafe {
                gl::Enable(gl::SCISSOR_TEST);
            }
        }
    }
}

impl Drop for BloomState {
    fn drop(&mut self) {
        let c = self.compat;
        unsafe {
            c.matrix_mode(GL_MODELVIEW);
            c.pop_matrix();
            c.matrix_mode(GL_PROJECTION);
            c.pop_matrix();
            c.matrix_mode(GL_MODELVIEW);
            if self.scissor {
                gl::Enable(gl::SCISSOR_TEST);
            }
        }
    }
}

impl Drop for Bloom {
    fn drop(&mut self) {
        self.delete_buffers();
        unsafe {
            if self.program != 0 {
                gl::DeleteProgram(self.program);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// EGL surface -> ARGB32 X pixmap presentation
// ---------------------------------------------------------------------------

/// Where GL actually renders before XRender sees the frame. The fast path is
/// an EGL pixmap surface: GL writes directly into the ARGB32 X pixmap and no
/// pixels cross the GPU/CPU boundary. Some software EGL drivers accept the
/// pixmap surface but never publish its contents to the X server, so detect
/// that once and fall back to an offscreen framebuffer + XImage upload.
enum Presentation {
    Pixmap,
    Readback(ReadbackTarget),
}

/// Offscreen EGL framebuffer used when direct pixmap rendering is unavailable.
/// This is the old `glReadPixels`/`XPutImage` path, but it no longer needs GLX.
struct ReadbackTarget {
    texture: GLuint,
    fbo: GLuint,
    image: *mut xlib::XImage,
}

impl ReadbackTarget {
    fn new(
        dpy: *mut xlib::Display,
        visual: *mut xlib::Visual,
        width: u32,
        height: u32,
    ) -> Result<ReadbackTarget> {
        let width = width.max(1);
        let height = height.max(1);
        let mut texture = 0;
        let mut fbo = 0;
        unsafe {
            gl::GenTextures(1, &mut texture);
            gl::BindTexture(gl::TEXTURE_2D, texture);
            gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MIN_FILTER, gl::NEAREST as GLint);
            gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MAG_FILTER, gl::NEAREST as GLint);
            gl::TexParameteri(
                gl::TEXTURE_2D,
                gl::TEXTURE_WRAP_S,
                gl::CLAMP_TO_EDGE as GLint,
            );
            gl::TexParameteri(
                gl::TEXTURE_2D,
                gl::TEXTURE_WRAP_T,
                gl::CLAMP_TO_EDGE as GLint,
            );
            gl::TexImage2D(
                gl::TEXTURE_2D,
                0,
                gl::RGBA as GLint,
                width as GLsizei,
                height as GLsizei,
                0,
                gl::RGBA,
                gl::UNSIGNED_BYTE,
                ptr::null(),
            );
            if gl::GetError() != gl::NO_ERROR {
                gl::DeleteTextures(1, &texture);
                return Err("cannot allocate EGL readback texture".into());
            }

            gl::GenFramebuffers(1, &mut fbo);
            gl::BindFramebuffer(gl::FRAMEBUFFER, fbo);
            gl::FramebufferTexture2D(
                gl::FRAMEBUFFER,
                gl::COLOR_ATTACHMENT0,
                gl::TEXTURE_2D,
                texture,
                0,
            );
            let status = gl::CheckFramebufferStatus(gl::FRAMEBUFFER);
            gl::BindFramebuffer(gl::FRAMEBUFFER, 0);
            if status != gl::FRAMEBUFFER_COMPLETE {
                gl::DeleteFramebuffers(1, &fbo);
                gl::DeleteTextures(1, &texture);
                return Err(format!("EGL readback framebuffer is incomplete: {status:#x}").into());
            }

            let image = xlib::XCreateImage(
                dpy,
                visual,
                32,
                xlib::ZPixmap,
                0,
                ptr::null_mut(),
                width,
                height,
                32,
                0,
            );
            if image.is_null() {
                gl::DeleteFramebuffers(1, &fbo);
                gl::DeleteTextures(1, &texture);
                return Err("cannot allocate ARGB32 XImage for EGL readback".into());
            }
            // XCreateImage leaves data NULL; calloc matches XDestroyImage's XFree.
            let bytes = (*image).bytes_per_line as usize * height as usize;
            let data = libc::calloc(bytes, 1) as *mut c_char;
            if data.is_null() {
                xlib::XDestroyImage(image);
                gl::DeleteFramebuffers(1, &fbo);
                gl::DeleteTextures(1, &texture);
                return Err("cannot allocate ARGB32 XImage data for EGL readback".into());
            }
            (*image).data = data;
            (*image).byte_order = xlib::XImageByteOrder(dpy);
            (*image).bitmap_unit = xlib::XBitmapUnit(dpy);
            (*image).bitmap_bit_order = xlib::XBitmapBitOrder(dpy);

            Ok(ReadbackTarget {
                texture,
                fbo,
                image,
            })
        }
    }

    /// Copy the bound framebuffer into the presentation pixmap. GL rows start
    /// at the bottom and `GL_BGRA` is byte-for-byte ARGB32 on little-endian
    /// hosts, so only big-endian hosts need a channel swap.
    fn readback(&mut self, dpy: *mut xlib::Display, pixmap: xlib::Pixmap) -> Result<()> {
        if self.image.is_null() {
            return Err("EGL readback surface is not initialized".into());
        }
        unsafe {
            let image = &mut *self.image;
            let w = image.width as GLsizei;
            let h = image.height as GLsizei;
            let mut pixels = vec![0u8; (w * h * 4) as usize];
            gl::ReadPixels(
                0,
                0,
                w,
                h,
                gl::BGRA,
                gl::UNSIGNED_BYTE,
                pixels.as_mut_ptr().cast(),
            );
            let err = gl::GetError();
            if err != gl::NO_ERROR {
                return Err(format!("EGL GL readback failed: {err:#x}").into());
            }

            let bpl = image.bytes_per_line as usize;
            let little_endian = image.byte_order == xlib::LSBFirst;
            let dst = image.data as *mut u8;
            for y in 0..h as usize {
                let src_row = &pixels[(h as usize - 1 - y) * w as usize * 4..];
                let dst_row = std::slice::from_raw_parts_mut(dst.add(y * bpl), (w * 4) as usize);
                if little_endian {
                    dst_row.copy_from_slice(&src_row[..(w * 4) as usize]);
                } else {
                    for (d, s) in dst_row.chunks_exact_mut(4).zip(src_row.chunks_exact(4)) {
                        d[0] = s[3];
                        d[1] = s[2];
                        d[2] = s[1];
                        d[3] = s[0];
                    }
                }
            }

            let gc = xlib::XCreateGC(dpy, pixmap, 0, ptr::null_mut());
            if !gc.is_null() {
                xlib::XPutImage(
                    dpy,
                    pixmap,
                    gc,
                    image,
                    0,
                    0,
                    0,
                    0,
                    image.width as u32,
                    image.height as u32,
                );
                xlib::XFreeGC(dpy, gc);
            }
        }
        Ok(())
    }

    /// Requires the EGL context to be current; GL objects are context-local.
    fn destroy(&mut self) {
        unsafe {
            if self.fbo != 0 {
                gl::DeleteFramebuffers(1, &self.fbo);
            }
            if self.texture != 0 {
                gl::DeleteTextures(1, &self.texture);
            }
            if !self.image.is_null() {
                xlib::XDestroyImage(self.image);
            }
        }
        self.texture = 0;
        self.fbo = 0;
        self.image = ptr::null_mut();
    }
}

/// Owns the EGL context plus the ARGB32 X pixmap that XRender composites. On
/// drivers that publish EGL pixmap writes to X, GL renders straight into that
/// pixmap. The fallback renders into [`ReadbackTarget`] and uploads the result
/// with `XPutImage`, but still uses an EGL context instead of GLX.
pub struct EglSurface {
    dpy: *mut xlib::Display,
    visual: *mut xlib::Visual,
    /// Declared after the pixmap/surface but dropped last: glyph textures and
    /// bloom buffers are deleted while this context is still current.
    egl: EglContext,
    pixmap: xlib::Pixmap,
    picture: xrender::Picture,
    surface: egl::EGLSurface,
    presentation: Option<Presentation>,
    direct: bool,
    width: u32,
    height: u32,
}

impl EglSurface {
    pub fn new(
        dpy: *mut xlib::Display,
        visual: *mut xlib::Visual,
        width: u32,
        height: u32,
        allow_fallback: bool,
    ) -> Result<EglSurface> {
        let width = width.max(1);
        let height = height.max(1);
        let egl_ctx = EglContext::new(dpy, visual)?;
        let mut surface = EglSurface {
            dpy,
            visual,
            egl: egl_ctx,
            pixmap: 0,
            picture: 0,
            surface: ptr::null_mut(),
            presentation: None,
            direct: true,
            width: 0,
            height: 0,
        };
        surface.create_pixmap(width, height)?;
        load_gl()?;
        surface.direct = surface.probe_direct();
        if surface.direct {
            surface.presentation = Some(Presentation::Pixmap);
        } else if allow_fallback {
            let target = ReadbackTarget::new(dpy, visual, width, height)?;
            surface.presentation = Some(Presentation::Readback(target));
        } else {
            return Err(
                "EGL pixmap surface is not visible to XRender and EGL_FALLBACK is disabled".into(),
            );
        }
        surface.make_current()?;
        Ok(surface)
    }

    pub fn picture(&self) -> xrender::Picture {
        self.picture
    }

    pub fn size(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    /// Framebuffer callers must use as their final render target. `0` is the
    /// EGL pixmap on the zero-copy path; the fallback uses its offscreen FBO.
    pub fn framebuffer(&self) -> GLuint {
        match &self.presentation {
            Some(Presentation::Readback(target)) => target.fbo,
            _ => 0,
        }
    }

    /// Rebind this context after another GL context was made current.
    pub fn make_current(&self) -> Result {
        self.egl.make_current(self.surface)?;
        unsafe {
            gl::BindFramebuffer(gl::FRAMEBUFFER, self.framebuffer());
        }
        Ok(())
    }

    /// Complete all pending GL work before XRender reads the pixmap. A plain
    /// `glFlush` is not enough: the X server may composite stale pixmap
    /// contents while the driver still has commands queued. On the fallback
    /// path this also performs the `glReadPixels`/`XPutImage` upload.
    pub fn finish(&mut self) -> Result {
        unsafe {
            if let Some(Presentation::Readback(target)) = self.presentation.as_mut() {
                gl::BindFramebuffer(gl::FRAMEBUFFER, target.fbo);
            }
            gl::Finish();
            let err = gl::GetError();
            if err != gl::NO_ERROR {
                return Err(format!("finder GL rendering failed: {err:#x}").into());
            }
            if let Some(Presentation::Readback(target)) = self.presentation.as_mut() {
                target.readback(self.dpy, self.pixmap)?;
                // Keep the surface bound for the next frame's fixed-function
                // quads and glyph textures.
                gl::BindFramebuffer(gl::FRAMEBUFFER, target.fbo);
            }
        }
        Ok(())
    }

    /// Recreate the drawable when the popup size changes. The EGL context,
    /// shaders, glyph textures and bloom buffers all survive the resize.
    pub fn resize(&mut self, width: u32, height: u32) -> Result<()> {
        let width = width.max(1);
        let height = height.max(1);
        if !self.surface.is_null() && (self.width, self.height) == (width, height) {
            return Ok(());
        }
        if let Some(Presentation::Readback(target)) = self.presentation.as_mut() {
            target.destroy();
        }
        self.presentation = None;
        self.destroy_surface();
        self.create_pixmap(width, height)?;
        if self.direct {
            self.presentation = Some(Presentation::Pixmap);
        } else {
            let target = ReadbackTarget::new(self.dpy, self.visual, width, height)?;
            self.presentation = Some(Presentation::Readback(target));
        }
        self.make_current()
    }

    fn create_pixmap(&mut self, width: u32, height: u32) -> Result<()> {
        unsafe {
            let pixmap = xlib::XCreatePixmap(
                self.dpy,
                xlib::XDefaultRootWindow(self.dpy),
                width,
                height,
                32,
            );
            if pixmap == 0 {
                return Err("cannot create ARGB32 pixmap for EGL rendering".into());
            }
            let format = xrender::XRenderFindStandardFormat(self.dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                xlib::XFreePixmap(self.dpy, pixmap);
                return Err("XRender has no ARGB32 picture format".into());
            }
            let picture = xrender::XRenderCreatePicture(self.dpy, pixmap, format, 0, ptr::null());
            if picture == 0 {
                xlib::XFreePixmap(self.dpy, pixmap);
                return Err("cannot create XRender picture for EGL rendering".into());
            }
            let surface = egl::create_pixmap_surface(self.egl.dpy, self.egl.config, pixmap);
            if surface.is_null() {
                let err = egl::error("eglCreatePixmapSurface");
                xrender::XRenderFreePicture(self.dpy, picture);
                xlib::XFreePixmap(self.dpy, pixmap);
                return Err(format!("cannot create EGL pixmap surface: {err}").into());
            }
            if let Err(e) = self.egl.make_current(surface) {
                egl::destroy_surface(self.egl.dpy, surface);
                xrender::XRenderFreePicture(self.dpy, picture);
                xlib::XFreePixmap(self.dpy, pixmap);
                return Err(e);
            }
            self.pixmap = pixmap;
            self.picture = picture;
            self.surface = surface;
            self.width = width;
            self.height = height;
        }
        Ok(())
    }

    /// Decide once whether this EGL driver makes pixmap-surface writes visible
    /// to XRender. Mesa's software rasterizer on Xvfb accepts the surface but
    /// keeps the pixels private, so a tiny clear/composite/read test is needed.
    fn probe_direct(&self) -> bool {
        unsafe {
            gl::BindFramebuffer(gl::FRAMEBUFFER, 0);
            gl::Viewport(0, 0, self.width as GLsizei, self.height as GLsizei);
            gl::ClearColor(1.0, 0.0, 0.0, 0.5);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            gl::Finish();

            let visible = self.pixmap_has_pixel(0x80ff_0000);
            gl::ClearColor(0.0, 0.0, 0.0, 0.0);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            gl::Finish();
            while gl::GetError() != gl::NO_ERROR {}
            visible
        }
    }

    fn pixmap_has_pixel(&self, expected: u32) -> bool {
        unsafe {
            let format = xrender::XRenderFindStandardFormat(self.dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                return false;
            }
            let out = xlib::XCreatePixmap(
                self.dpy,
                xlib::XDefaultRootWindow(self.dpy),
                self.width,
                self.height,
                32,
            );
            if out == 0 {
                return false;
            }
            let dst = xrender::XRenderCreatePicture(self.dpy, out, format, 0, ptr::null());
            if dst == 0 {
                xlib::XFreePixmap(self.dpy, out);
                return false;
            }
            xrender::XRenderComposite(
                self.dpy,
                xrender::PictOpSrc,
                self.picture,
                0,
                dst,
                0,
                0,
                0,
                0,
                0,
                0,
                self.width,
                self.height,
            );
            xlib::XSync(self.dpy, xlib::False);
            let x = (self.width / 2).min(self.width - 1) as i32;
            let y = (self.height / 2).min(self.height - 1) as i32;
            let image =
                xlib::XGetImage(self.dpy, out, x, y, 1, 1, xlib::XAllPlanes(), xlib::ZPixmap);
            let found = !image.is_null() && xlib::XGetPixel(image, 0, 0) as u32 == expected;
            if !image.is_null() {
                xlib::XDestroyImage(image);
            }
            xrender::XRenderFreePicture(self.dpy, dst);
            xlib::XFreePixmap(self.dpy, out);
            found
        }
    }

    fn destroy_surface(&mut self) {
        egl::release_current(self.egl.dpy);
        egl::destroy_surface(self.egl.dpy, self.surface);
        unsafe {
            if self.picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.picture);
            }
            if self.pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.pixmap);
            }
        }
        self.pixmap = 0;
        self.picture = 0;
        self.surface = ptr::null_mut();
        self.width = 0;
        self.height = 0;
    }
}

impl Drop for EglSurface {
    fn drop(&mut self) {
        if let Some(Presentation::Readback(target)) = self.presentation.as_mut() {
            target.destroy();
        }
        self.destroy_surface();
    }
}

// ---------------------------------------------------------------------------
// GLFont: FreeType glyph textures + HarfBuzz shaping (dwm.c 8703-9206)
// ---------------------------------------------------------------------------

const GL_FONT_MAX_FACES: usize = 32;
const GL_FONT_MAX_GLYPHS: usize = 2048;
const GL_FONT_FALLBACK_FILES: &[&str] = &[
    "/usr/share/fonts/noto/NotoSans-Regular.ttf",
    "/usr/share/fonts/noto/NotoSansSymbols2-Regular.ttf",
    "/usr/share/fonts/noto/NotoSansMath-Regular.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/TTF/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
];

// Texture environment tokens omitted from `gl` 0.14.
const GL_TEXTURE_ENV: GLenum = 0x2300;
const GL_TEXTURE_ENV_MODE: GLenum = 0x2200;
const GL_MODULATE: GLenum = 0x2100;

#[repr(C)]
struct HbGlyphInfo {
    codepoint: u32,
    mask: u32,
    cluster: u32,
    var1: u32,
    var2: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct HbGlyphPosition {
    x_advance: i32,
    y_advance: i32,
    x_offset: i32,
    y_offset: i32,
    var: u32,
}

#[link(name = "harfbuzz")]
unsafe extern "C" {
    fn hb_ft_font_create_referenced(face: FT_Face) -> *mut c_void;
    fn hb_ft_font_set_load_flags(font: *mut c_void, flags: i32);
    fn hb_font_destroy(font: *mut c_void);
    fn hb_buffer_create() -> *mut c_void;
    fn hb_buffer_destroy(buffer: *mut c_void);
    fn hb_buffer_add_utf8(
        buffer: *mut c_void,
        text: *const c_char,
        text_length: c_int,
        item_offset: c_uint,
        item_length: c_int,
    );
    fn hb_buffer_guess_segment_properties(buffer: *mut c_void);
    fn hb_shape(font: *mut c_void, buffer: *mut c_void, features: *const c_void, count: c_uint);
    fn hb_buffer_get_glyph_infos(buffer: *mut c_void, count: *mut c_uint) -> *mut HbGlyphInfo;
    fn hb_buffer_get_glyph_positions(
        buffer: *mut c_void,
        count: *mut c_uint,
    ) -> *mut HbGlyphPosition;
}

type FcCharSet = c_void;
type FcPattern = c_void;
type FcBool = c_int;
type FcResult = c_int;

const FcMatchPattern: c_int = 0;
const FcResultMatch: c_int = 0;

#[link(name = "fontconfig")]
unsafe extern "C" {
    fn FcCharSetCreate() -> *mut FcCharSet;
    fn FcCharSetDestroy(cs: *mut FcCharSet);
    fn FcCharSetAddChar(cs: *mut FcCharSet, cp: u32) -> FcBool;
    fn FcPatternCreate() -> *mut FcPattern;
    fn FcPatternDestroy(p: *mut FcPattern);
    fn FcPatternAddInteger(
        p: *mut FcPattern,
        object: *const c_char,
        value: c_int,
    ) -> FcBool;
    fn FcPatternAddCharSet(p: *mut FcPattern, object: *const c_char, cs: *const FcCharSet) -> FcBool;
    fn FcPatternAddBool(p: *mut FcPattern, object: *const c_char, value: FcBool) -> FcBool;
    fn FcPatternGetString(
        p: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut *mut u8,
    ) -> FcResult;
    fn FcPatternGetInteger(
        p: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut c_int,
    ) -> FcResult;
    fn FcPatternGetBool(
        p: *const FcPattern,
        object: *const c_char,
        n: c_int,
        value: *mut FcBool,
    ) -> FcBool;
    fn FcConfigSubstitute(config: *mut c_void, p: *mut FcPattern, kind: c_int) -> FcBool;
    fn FcDefaultSubstitute(p: *mut FcPattern);
    fn FcFontMatch(config: *mut c_void, p: *mut FcPattern, result: *mut FcResult) -> *mut FcPattern;
}

const FC_TRUE: FcBool = 1;

// Fontconfig property values (fontconfig.h).
const FC_HINT_NONE: c_int = 0;
const FC_HINT_SLIGHT: c_int = 1;
const FC_HINT_MEDIUM: c_int = 2;
const FC_HINT_FULL: c_int = 3;
const FC_RGBA_UNKNOWN: c_int = 0;
const FC_RGBA_RGB: c_int = 1;
const FC_RGBA_BGR: c_int = 2;
const FC_RGBA_VRGB: c_int = 3;
const FC_RGBA_VBGR: c_int = 4;
const FC_RGBA_NONE: c_int = 5;
const FC_LCD_NONE: c_int = 0;
const FC_LCD_DEFAULT: c_int = 1;
const FC_LCD_LIGHT: c_int = 2;
const FC_LCD_LEGACY: c_int = 3;

// The C header values. freetype-sys 0.20 exposes FT_LCD_FILTER_LIGHT as 3,
// which is actually FT_LCD_FILTER_LEGACY1, so use the C values explicitly.
const FT_LCD_LIGHT: freetype_sys::FT_LcdFilter = 2;
const FT_LCD_LEGACY: freetype_sys::FT_LcdFilter = 16;

unsafe fn fc_bool(pattern: *const FcPattern, object: &str) -> Option<bool> {
    let object = CString::new(object).ok()?;
    let mut value: FcBool = 0;
    (unsafe { FcPatternGetBool(pattern, object.as_ptr(), 0, &mut value) } != 0)
        .then(|| value != 0)
}

unsafe fn fc_int(pattern: *const FcPattern, object: &str) -> Option<c_int> {
    let object = CString::new(object).ok()?;
    let mut value = 0;
    (unsafe { FcPatternGetInteger(pattern, object.as_ptr(), 0, &mut value) } == FcResultMatch)
        .then_some(value)
}

/// Hinting settings for every GL text face in the finder and notifications.
///
/// These come from the Xft pattern Xft resolved for the configured font, so
/// X11 resources such as `Xft.hinting`, `Xft.hintstyle`, `Xft.rgba` and
/// `Xft.lcdfilter` are honored the same way as for X11-drawn text. Sizes are
/// deliberately not read from the pattern: callers keep their own pixel sizes.
#[derive(Clone, Copy, Debug)]
pub struct FontHinting {
    load_flags: freetype_sys::FT_Int32,
    /// The hintstyle target without any LCD subpixel target, used if FreeType
    /// cannot support the configured LCD filter.
    grayscale_target: freetype_sys::FT_Int32,
    lcd_order: u8,
    lcd_filter: freetype_sys::FT_LcdFilter,
}

impl Default for FontHinting {
    fn default() -> Self {
        Self {
            // Matches `Xft.hintstyle: hintslight`, the fallback when Xft has no
            // hinting information at all.
            load_flags: freetype_sys::FT_LOAD_DEFAULT | freetype_sys::FT_LOAD_TARGET_LIGHT,
            grayscale_target: freetype_sys::FT_LOAD_TARGET_LIGHT,
            lcd_order: 0,
            lcd_filter: freetype_sys::FT_LCD_FILTER_DEFAULT,
        }
    }
}

impl FontHinting {
    /// Read the hinting properties from a resolved Xft pattern. Xft merges the
    /// X resources into the pattern before returning it from `XftFontOpenName`,
    /// so this is the same configuration the X11 text renderer sees.
    pub fn from_xft_pattern(
        dpy: *mut xlib::Display,
        screen: c_int,
        pattern: *const c_void,
    ) -> Self {
        let mut hinting = Self::default();
        // XRender's subpixel order is the fallback, as it was before Xft
        // properties were consulted. Values match fontconfig's FcRGBA_*.
        if !dpy.is_null() {
            let order = unsafe { xrender::XRenderQuerySubpixelOrder(dpy, screen) };
            hinting.lcd_order = match order {
                1..=4 => order as u8,
                _ => 0,
            };
        }
        if pattern.is_null() {
            return hinting;
        }
        let pattern = pattern as *const FcPattern;
        unsafe {
            let enabled = fc_bool(pattern, "hinting").unwrap_or(true);
            let style = fc_int(pattern, "hintstyle").unwrap_or(FC_HINT_SLIGHT);
            hinting.grayscale_target = match style {
                FC_HINT_MEDIUM | FC_HINT_FULL => freetype_sys::FT_LOAD_TARGET_NORMAL,
                _ => freetype_sys::FT_LOAD_TARGET_LIGHT,
            };
            let target = match fc_int(pattern, "rgba") {
                Some(FC_RGBA_RGB) => {
                    hinting.lcd_order = 1;
                    freetype_sys::FT_LOAD_TARGET_LCD
                }
                Some(FC_RGBA_BGR) => {
                    hinting.lcd_order = 2;
                    freetype_sys::FT_LOAD_TARGET_LCD
                }
                Some(FC_RGBA_VRGB) => {
                    hinting.lcd_order = 3;
                    freetype_sys::FT_LOAD_TARGET_LCD_V
                }
                Some(FC_RGBA_VBGR) => {
                    hinting.lcd_order = 4;
                    freetype_sys::FT_LOAD_TARGET_LCD_V
                }
                Some(FC_RGBA_UNKNOWN) | Some(FC_RGBA_NONE) => {
                    hinting.lcd_order = 0;
                    hinting.grayscale_target
                }
                // No rgba in the pattern: keep XRender's subpixel order and
                // load hints that match it.
                None => match hinting.lcd_order {
                    1 | 2 => freetype_sys::FT_LOAD_TARGET_LCD,
                    3 | 4 => freetype_sys::FT_LOAD_TARGET_LCD_V,
                    _ => hinting.grayscale_target,
                },
                _ => hinting.grayscale_target,
            };
            let mut flags = freetype_sys::FT_LOAD_DEFAULT;
            if !enabled || style == FC_HINT_NONE {
                flags |= freetype_sys::FT_LOAD_NO_HINTING;
            }
            hinting.load_flags = flags | target;
            hinting.lcd_filter = match fc_int(pattern, "lcdfilter") {
                Some(FC_LCD_NONE) => freetype_sys::FT_LCD_FILTER_NONE,
                Some(FC_LCD_LIGHT) => FT_LCD_LIGHT,
                Some(FC_LCD_LEGACY) => FT_LCD_LEGACY,
                _ => freetype_sys::FT_LCD_FILTER_DEFAULT,
            };
        }
        hinting
    }

    /// Used when FreeType has no LCD filter support: fall back to grayscale
    /// rasterization with the configured hint style, not to full LCD without a
    /// filter.
    fn without_lcd(mut self) -> Self {
        self.lcd_order = 0;
        self.load_flags = (self.load_flags & !(0xf << 16)) | self.grayscale_target;
        self
    }
}

static FT_LIB: OnceLock<usize> = OnceLock::new();

fn ft_library() -> Result<FT_Face> {
    // The pointer is stored as usize because raw pointers are not Sync; the
    // library is process-wide and immutable after initialization.
    let addr = if let Some(&addr) = FT_LIB.get() {
        addr
    } else {
        let mut lib: *mut c_void = ptr::null_mut();
        let err: FT_Error = unsafe { freetype_sys::FT_Init_FreeType(&mut lib) };
        if err != 0 || lib.is_null() {
            return Err(format!("cannot initialize FreeType (error {err})").into());
        }
        let _ = FT_LIB.set(lib as usize);
        *FT_LIB.get().expect("FreeType library cached")
    };
    Ok(addr as FT_Face)
}

struct GlFontFace {
    face: FT_Face,
    hb_font: *mut c_void,
    file: String,
    index: i32,
    pixel_size: f64,
}

#[derive(Clone, Copy, Default)]
struct GlGlyph {
    tex_id: GLuint,
    face_index: u32,
    glyph_index: u32,
    w: i32,
    h: i32,
    bearing_x: i32,
    bearing_y: i32,
    advance: i32,
}

/// One resolved Xft face as consumed by dwm's `gl_font_add_face`.
#[derive(Clone, Debug)]
pub struct GlFontSpec {
    pub file: String,
    pub index: i32,
    pub pixel_size: f64,
}

/// One texture per glyph, one FreeType face per file (up to 32), and HarfBuzz
/// shaping per face run. This mirrors dwm's `GLFont` layout, but also loads
/// fontconfig fallbacks for codepoints missing from the configured faces and
/// evicts glyph textures when the cache fills.
pub struct GlFont {
    faces: RefCell<Vec<GlFontFace>>,
    /// Rasterized glyph cache. Text measuring needs glyph shaping but callers
    /// often only hold a shared reference during layout, so the cache uses
    /// interior mutability instead of forcing `&mut self` on every method.
    glyphs: RefCell<Vec<GlGlyph>>,
    glyph_index: RefCell<HashMap<(u32, u32), usize>>,
    pub height: i32,
    pub pixel_size: f64,
    pub lcd_order: u8,
    /// Xft-configured flags shared by HarfBuzz shaping and glyph rasterization.
    load_flags: freetype_sys::FT_Int32,
    dpy: *mut xlib::Display,
    screen: i32,
}

impl GlFont {
    /// dwm.c 8707-8846: load up to 32 Xft-resolved faces at their own pixel
    /// sizes, set a 72 dpi char size so one pixel maps to one font unit, and
    /// create a HarfBuzz font with the hinting Xft was configured to use.
    pub fn new(
        specs: &[GlFontSpec],
        height: i32,
        hinting: FontHinting,
        dpy: *mut xlib::Display,
        screen: i32,
    ) -> Result<GlFont> {
        let library = ft_library()?;
        let mut hinting = hinting;
        if hinting.lcd_order != 0 {
            let err = unsafe {
                freetype_sys::FT_Library_SetLcdFilter(
                    library as freetype_sys::FT_Library,
                    hinting.lcd_filter,
                )
            };
            if err != 0 {
                hinting = hinting.without_lcd();
            }
        }
        let base_size = specs
            .iter()
            .find(|spec| spec.pixel_size > 0.0)
            .map(|spec| spec.pixel_size)
            .unwrap_or(14.0);
        let mut faces = Vec::new();
        for spec in specs.iter().take(GL_FONT_MAX_FACES) {
            let pixel_size = if spec.pixel_size > 0.0 {
                spec.pixel_size
            } else {
                base_size
            };
            if faces.iter().any(|f: &GlFontFace| {
                f.index == spec.index && f.pixel_size == pixel_size && f.file == spec.file
            }) {
                continue;
            }
            if let Ok(face) =
                Self::add_face(library, &spec.file, spec.index, pixel_size, hinting.load_flags)
            {
                faces.push(face);
            }
        }
        if faces.is_empty() {
            for file in GL_FONT_FALLBACK_FILES {
                if let Ok(face) = Self::add_face(library, file, 0, base_size, hinting.load_flags) {
                    faces.push(face);
                    break;
                }
            }
        }
        if faces.is_empty() {
            return Err("no usable FreeType font face for GL text".into());
        }
        let height = if height > 0 {
            height
        } else {
            unsafe {
                let metrics = (*(*faces[0].face).size).metrics.height >> 6;
                if metrics > 0 {
                    metrics as i32
                } else {
                    base_size.ceil() as i32
                }
            }
        };
        Ok(GlFont {
            faces: RefCell::new(faces),
            glyphs: RefCell::new(Vec::new()),
            glyph_index: RefCell::new(HashMap::new()),
            height,
            pixel_size: base_size,
            lcd_order: hinting.lcd_order,
            load_flags: hinting.load_flags,
            dpy,
            screen,
        })
    }

    fn add_face(
        library: FT_Face,
        file: &str,
        index: i32,
        pixel_size: f64,
        load_flags: freetype_sys::FT_Int32,
    ) -> Result<GlFontFace> {
        let cfile = CString::new(file)?;
        let mut face: FT_Face = ptr::null_mut();
        let err: FT_Error = unsafe {
            freetype_sys::FT_New_Face(
                library as *mut c_void,
                cfile.as_ptr(),
                index as freetype_sys::FT_Long,
                &mut face,
            )
        };
        if err != 0 || face.is_null() {
            return Err(format!("cannot load font {file} (error {err})").into());
        }
        let size = (pixel_size * 64.0).round() as freetype_sys::FT_F26Dot6;
        let err: FT_Error = unsafe { freetype_sys::FT_Set_Char_Size(face, 0, size, 72, 72) };
        if err != 0 {
            unsafe { freetype_sys::FT_Done_Face(face) };
            return Err(format!("cannot size font {file} (error {err})").into());
        }
        let hb_font = unsafe { hb_ft_font_create_referenced(face) };
        if hb_font.is_null() {
            unsafe { freetype_sys::FT_Done_Face(face) };
            return Err(format!("cannot create HarfBuzz font for {file}").into());
        }
        unsafe { hb_ft_font_set_load_flags(hb_font, load_flags) };
        Ok(GlFontFace {
            face,
            hb_font,
            file: file.to_string(),
            index,
            pixel_size,
        })
    }

    pub fn ascender(&self) -> i32 {
        let faces = self.faces.borrow();
        let Some(face) = faces.first() else {
            return self.height.max(1);
        };
        unsafe {
            let a = (*(*face.face).size).metrics.ascender >> 6;
            a.max(1) as i32
        }
    }

    /// FreeType's descender in whole pixels. Used by the notification layout,
    /// which sizes its text blocks from the same metrics as dwm's GL font.
    pub fn descender(&self) -> i32 {
        let faces = self.faces.borrow();
        let Some(face) = faces.first() else {
            return 0;
        };
        unsafe {
            let d = -((*(*face.face).size).metrics.descender >> 6);
            d.max(0) as i32
        }
    }

    fn face_for(&self, ch: char) -> usize {
        let cp = ch as u32;
        let faces = self.faces.borrow();
        for (i, f) in faces.iter().enumerate() {
            if unsafe { freetype_sys::FT_Get_Char_Index(f.face, cp as FT_ULong) } != 0 {
                return i;
            }
        }
        drop(faces);
        self.fallback_face(cp).unwrap_or(0)
    }

    fn fallback_face(&self, cp: u32) -> Option<usize> {
        if cp == 0 {
            return None;
        }
        let faces = self.faces.borrow();
        if faces.is_empty() || faces.len() >= GL_FONT_MAX_FACES {
            return None;
        }
        let base = &faces[0];
        let base_file = base.file.clone();
        let base_index = base.index;
        let base_size = if base.pixel_size > 0.0 {
            base.pixel_size
        } else {
            self.pixel_size
        };
        drop(faces);

        let library = ft_library().ok()?;
        if let Some((file, index)) = self.fc_match_file(cp) {
            let file = if file.is_empty() { base_file.clone() } else { file };
            let index = if index < 0 { base_index } else { index };
            if let Some(face_index) = self.try_load_fallback_face(library, &file, index, base_size, cp)
            {
                return Some(face_index);
            }
        }

        for file in GL_FONT_FALLBACK_FILES {
            if let Some(face_index) = self.try_load_fallback_face(library, file, 0, base_size, cp) {
                return Some(face_index);
            }
        }
        None
    }

    fn fc_match_file(&self, cp: u32) -> Option<(String, i32)> {
        if self.dpy.is_null() {
            return None;
        }
        unsafe {
            let charset = FcCharSetCreate();
            if charset.is_null() {
                return None;
            }
            FcCharSetAddChar(charset, cp);
            let pat = FcPatternCreate();
            if pat.is_null() {
                FcCharSetDestroy(charset);
                return None;
            }
            let file_key = CString::new("file").ok()?;
            let idx_key = CString::new("index").ok()?;
            let charset_key = CString::new("charset").ok()?;
            let scalable_key = CString::new("scalable").ok()?;
            FcPatternAddBool(pat, scalable_key.as_ptr(), FC_TRUE);
            FcPatternAddCharSet(pat, charset_key.as_ptr(), charset);
            FcConfigSubstitute(ptr::null_mut(), pat, FcMatchPattern);
            FcDefaultSubstitute(pat);
            let mut result: FcResult = 1;
            let matched = FcFontMatch(ptr::null_mut(), pat, &mut result);
            FcCharSetDestroy(charset);
            FcPatternDestroy(pat);
            if matched.is_null() {
                return None;
            }
            let mut file_ptr: *mut u8 = ptr::null_mut();
            let mut idx = 0;
            let has_file =
                FcPatternGetString(matched, file_key.as_ptr(), 0, &mut file_ptr) == FcResultMatch
                    && !file_ptr.is_null();
            let _ = FcPatternGetInteger(matched, idx_key.as_ptr(), 0, &mut idx);
            let out = has_file.then(|| {
                (
                    CStr::from_ptr(file_ptr as *const c_char)
                        .to_string_lossy()
                        .into_owned(),
                    idx,
                )
            });
            FcPatternDestroy(matched);
            out
        }
    }

    fn try_load_fallback_face(
        &self,
        library: FT_Face,
        file: &str,
        index: i32,
        pixel_size: f64,
        cp: u32,
    ) -> Option<usize> {
        let mut faces = self.faces.borrow_mut();
        if faces.len() >= GL_FONT_MAX_FACES {
            return None;
        }
        if let Some((i, _)) = faces
            .iter()
            .enumerate()
            .find(|(_, f)| f.file == file && f.index == index && f.pixel_size == pixel_size)
        {
            let has = unsafe { freetype_sys::FT_Get_Char_Index(faces[i].face, cp as FT_ULong) } != 0;
            return has.then_some(i);
        }
        let face = Self::add_face(library, file, index, pixel_size, self.load_flags).ok()?;
        let has = unsafe { freetype_sys::FT_Get_Char_Index(face.face, cp as FT_ULong) } != 0;
        if !has {
            unsafe {
                if !face.hb_font.is_null() {
                    hb_font_destroy(face.hb_font);
                }
                if !face.face.is_null() {
                    freetype_sys::FT_Done_Face(face.face);
                }
            }
            return None;
        }
        faces.push(face);
        Some(faces.len() - 1)
    }

    /// Groups consecutive characters by the face that can render them and
    /// shapes each run with HarfBuzz, as dwm's two helper loops do.
    fn shaped_glyphs(&self, text: &str) -> Vec<(usize, u32, HbGlyphPosition)> {
        let chars: Vec<(char, usize)> = text.chars().map(|ch| (ch, self.face_for(ch))).collect();
        let mut out = Vec::new();
        let mut start = 0;
        while start < chars.len() {
            let face = chars[start].1;
            let mut end = start + 1;
            while end < chars.len() && chars[end].1 == face {
                end += 1;
            }
            let run: String = chars[start..end].iter().map(|(ch, _)| *ch).collect();
            if let Some(shaped) = self.shape_run(face, &run) {
                out.extend(shaped);
            }
            start = end;
        }
        out
    }

    fn shape_run(
        &self,
        face_index: usize,
        run: &str,
    ) -> Option<Vec<(usize, u32, HbGlyphPosition)>> {
        let hb_font = {
            let faces = self.faces.borrow();
            faces.get(face_index)?.hb_font
        };
        if hb_font.is_null() {
            return None;
        }
        unsafe {
            let buffer = hb_buffer_create();
            if buffer.is_null() {
                return None;
            }
            hb_buffer_add_utf8(
                buffer,
                run.as_ptr() as *const c_char,
                run.len() as c_int,
                0,
                run.len() as c_int,
            );
            hb_buffer_guess_segment_properties(buffer);
            hb_shape(hb_font, buffer, ptr::null(), 0);
            let mut count: c_uint = 0;
            let infos = hb_buffer_get_glyph_infos(buffer, &mut count);
            let positions = hb_buffer_get_glyph_positions(buffer, &mut count);
            let mut out = Vec::with_capacity(count as usize);
        if !infos.is_null() && !positions.is_null() {
            for i in 0..count as usize {
                let gid = (*infos.add(i)).codepoint;
                let pos = *positions.add(i);
                if gid == 0 {
                    // .notdef: try to render the corresponding character from a
                    // fallback face. HarfBuzz cluster is a byte offset into run.
                    let cluster = (*infos.add(i)).cluster as usize;
                    if let Some(ch) = run[cluster..].chars().next() {
                        let alt_face = self.face_for(ch);
                        if alt_face != face_index {
                            let alt_gid = freetype_sys::FT_Get_Char_Index(
                                self.faces.borrow()[alt_face].face,
                                ch as FT_ULong,
                            );
                            if alt_gid != 0 {
                                out.push((alt_face, alt_gid, pos));
                                continue;
                            }
                        }
                    }
                }
                out.push((face_index, gid, pos));
            }
        }
        hb_buffer_destroy(buffer);
        Some(out)
        }
    }

    /// dwm.c 9040-9077: sum positive 26.6 advances and round up to pixels.
    pub fn text_width(&self, text: &str) -> u32 {
        let mut width: i64 = 0;
        for (_, _, pos) in self.shaped_glyphs(text) {
            width += pos.x_advance.max(0) as i64;
        }
        ((width.max(0) + 63) / 64) as u32
    }

    /// dwm.c 8956-9038: load and rasterize one glyph into its own RGBA texture.
    fn glyph(&self, face_index: u32, glyph_index: u32) -> Option<GlGlyph> {
        let key = (face_index, glyph_index);
        if let Some(&slot) = self.glyph_index.borrow().get(&key) {
            if let Some(glyph) = self.glyphs.borrow().get(slot).copied() {
                return Some(glyph);
            }
        }
        let face = {
            let faces = self.faces.borrow();
            faces.get(face_index as usize)?.face
        };
        let err: FT_Error =
            unsafe { FT_Load_Glyph(face, glyph_index as FT_UInt, self.load_flags) };
        if err != 0 {
            return None;
        }
        let lcd = self.lcd_order != 0;
        let mut mode: FT_Render_Mode = match self.lcd_order {
            1 | 2 => freetype_sys::FT_RENDER_MODE_LCD,
            3 | 4 => freetype_sys::FT_RENDER_MODE_LCD_V,
            _ => freetype_sys::FT_RENDER_MODE_NORMAL,
        };
        let mut err: FT_Error = unsafe { FT_Render_Glyph((*face).glyph, mode) };
        if err != 0 && lcd {
            mode = freetype_sys::FT_RENDER_MODE_NORMAL;
            err = unsafe { FT_Render_Glyph((*face).glyph, mode) };
        }
        if err != 0 {
            return None;
        }
        let slot: FT_GlyphSlot = unsafe { (*face).glyph };
        if slot.is_null() {
            return None;
        }
        let bitmap: &FT_Bitmap = unsafe { &(*slot).bitmap };
        let pixel_mode = bitmap.pixel_mode as u32;
        let is_lcd = pixel_mode == freetype_sys::FT_PIXEL_MODE_LCD;
        let is_lcd_v = pixel_mode == freetype_sys::FT_PIXEL_MODE_LCD_V;
        let (w, h) = if is_lcd {
            (bitmap.width / 3, bitmap.rows)
        } else if is_lcd_v {
            (bitmap.width, bitmap.rows / 3)
        } else {
            (bitmap.width, bitmap.rows)
        };
        let mut glyph = GlGlyph {
            face_index,
            glyph_index,
            w,
            h,
            bearing_x: unsafe { (*slot).bitmap_left },
            bearing_y: unsafe { (*slot).bitmap_top },
            advance: unsafe { ((*slot).advance.x >> 6) as i32 },
            ..GlGlyph::default()
        };
        if w > 0 && h > 0 && !bitmap.buffer.is_null() {
            let mut pixels = vec![0u8; (w * h * 4) as usize];
            let total_rows = bitmap.rows as usize;
            let row_ptr = |row: usize| -> *mut u8 {
                if bitmap.pitch >= 0 {
                    unsafe { bitmap.buffer.add(row * bitmap.pitch as usize) }
                } else {
                    unsafe {
                        bitmap
                            .buffer
                            .add((total_rows - 1 - row) * (-bitmap.pitch) as usize)
                    }
                }
            };
            for y in 0..h {
                for x in 0..w {
                    let (r, g, b, a) = if is_lcd || is_lcd_v {
                        let (p0, p1, p2) = unsafe {
                            if is_lcd {
                                let row = row_ptr(y as usize);
                                (
                                    row.add(x as usize * 3),
                                    row.add(x as usize * 3 + 1),
                                    row.add(x as usize * 3 + 2),
                                )
                            } else {
                                (
                                    row_ptr(y as usize * 3).add(x as usize),
                                    row_ptr(y as usize * 3 + 1).add(x as usize),
                                    row_ptr(y as usize * 3 + 2).add(x as usize),
                                )
                            }
                        };
                        let (mut r, g, mut b) = unsafe { (*p0, *p1, *p2) };
                        // fontconfig uses RGB=1, BGR=2, VRGB=3, VBGR=4.
                        if self.lcd_order == 2 || self.lcd_order == 4 {
                            std::mem::swap(&mut r, &mut b);
                        }
                        let a = r.max(g).max(b);
                        // Premultiply for the renderer's ONE,ONE_MINUS_SRC_ALPHA blend.
                        let pm = |c: u8| ((c as u16 * a as u16 + 127) / 255) as u8;
                        (pm(r), pm(g), pm(b), a)
                    } else if pixel_mode == freetype_sys::FT_PIXEL_MODE_MONO {
                        let byte = unsafe { *row_ptr(y as usize).add(x as usize / 8) };
                        let bit = if byte & (0x80 >> (x as usize % 8)) != 0 { 255 } else { 0 };
                        (bit, bit, bit, bit)
                    } else {
                        let coverage = unsafe { *row_ptr(y as usize).add(x as usize) };
                        (coverage, coverage, coverage, coverage)
                    };
                    let p = ((y * w + x) * 4) as usize;
                    pixels[p] = r;
                    pixels[p + 1] = g;
                    pixels[p + 2] = b;
                    pixels[p + 3] = a;
                }
            }
            unsafe {
                gl::GenTextures(1, &mut glyph.tex_id);
                if glyph.tex_id != 0 {
                    gl::BindTexture(gl::TEXTURE_2D, glyph.tex_id);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MIN_FILTER, gl::NEAREST as GLint);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_MAG_FILTER, gl::NEAREST as GLint);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_WRAP_S, gl::CLAMP_TO_EDGE as GLint);
                    gl::TexParameteri(gl::TEXTURE_2D, gl::TEXTURE_WRAP_T, gl::CLAMP_TO_EDGE as GLint);
                    gl::PixelStorei(gl::UNPACK_ALIGNMENT, 1);
                    gl::TexImage2D(
                        gl::TEXTURE_2D,
                        0,
                        gl::RGBA as GLint,
                        w as GLsizei,
                        h as GLsizei,
                        0,
                        gl::RGBA,
                        gl::UNSIGNED_BYTE,
                        pixels.as_ptr() as *const c_void,
                    );
                    gl::BindTexture(gl::TEXTURE_2D, 0);
                }
            }
        }
        let mut glyphs = self.glyphs.borrow_mut();
        if glyphs.len() >= GL_FONT_MAX_GLYPHS {
            // Evict half the cache to avoid unbounded texture leaks.
            let keep_from = glyphs.len() / 2;
            let removed: Vec<GlGlyph> = glyphs.drain(..keep_from).collect();
            unsafe {
                for g in &removed {
                    if g.tex_id != 0 {
                        gl::DeleteTextures(1, &g.tex_id);
                    }
                }
            }
            let mut index = self.glyph_index.borrow_mut();
            index.clear();
            for (slot, g) in glyphs.iter().enumerate() {
                index.insert((g.face_index, g.glyph_index), slot);
            }
        }
        let slot = glyphs.len();
        glyphs.push(glyph);
        self.glyph_index.borrow_mut().insert(key, slot);
        Some(glyph)
    }

    /// dwm.c 9083-9177. `x` is the pen start, `baseline` the glyph baseline,
    /// `max_width` the clip width. Colour components are 0..1. This matches
    /// dwm's `gl_font_draw_text_alpha_for` with `grayscale == 0`: the glyph
    /// texture's coverage is already premultiplied into its RGB channels, so
    /// `GL_MODULATE` plus premultiplied blending keeps the text crisp.
    pub fn draw_text(
        &self,
        text: &str,
        x: i32,
        baseline: i32,
        max_width: u32,
        color: (f32, f32, f32),
        alpha: f32,
    ) -> Result<()> {
        let c = compat()?;
        let shaped = self.shaped_glyphs(text);
        unsafe {
            gl::Enable(gl::TEXTURE_2D);
            gl::Enable(gl::BLEND);
            premultiplied_blend();
            c.color4f(color.0 * alpha, color.1 * alpha, color.2 * alpha, alpha);
            c.tex_envf(GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, GL_MODULATE as GLfloat);
        }
        let mut pen_x: i64 = x as i64 * 64;
        let limit = max_width as i64 * 64;
        for (face_index, gid, pos) in shaped {
            if (pen_x + pos.x_advance as i64 - x as i64 * 64).max(0) > limit {
                break;
            }
            let glyph = self.glyph(face_index as u32, gid);
            let pen = (pen_x + pos.x_offset as i64) as f32 / 64.0;
            if let Some(g) = glyph {
                if g.tex_id != 0 && g.w > 0 && g.h > 0 {
                    let x1 = pen + g.bearing_x as f32;
                    let y1 = baseline as f32 - g.bearing_y as f32 - pos.y_offset as f32 / 64.0;
                    let x2 = x1 + g.w as f32;
                    let y2 = y1 + g.h as f32;
                    unsafe {
                        gl::BindTexture(gl::TEXTURE_2D, g.tex_id);
                        c.begin(gl::QUADS);
                        c.tex_coord2f(0.0, 0.0);
                        c.vertex2f(x1, y1);
                        c.tex_coord2f(1.0, 0.0);
                        c.vertex2f(x2, y1);
                        c.tex_coord2f(1.0, 1.0);
                        c.vertex2f(x2, y2);
                        c.tex_coord2f(0.0, 1.0);
                        c.vertex2f(x1, y2);
                        c.end();
                    }
                }
            }
            pen_x += pos.x_advance as i64;
            if pen_x - x as i64 * 64 > limit {
                break;
            }
        }
        unsafe {
            c.tex_envf(GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, GL_MODULATE as GLfloat);
            gl::Disable(gl::BLEND);
            gl::Disable(gl::TEXTURE_2D);
            gl::BindTexture(gl::TEXTURE_2D, 0);
        }
        Ok(())
    }
}

/// dwm.c 7648-7654: premultiplied alpha blending for glyph textures.
fn premultiplied_blend() {
    unsafe {
        if gl::BlendFuncSeparate::is_loaded() {
            gl::BlendFuncSeparate(
                gl::ONE,
                gl::ONE_MINUS_SRC_ALPHA,
                gl::ONE,
                gl::ONE_MINUS_SRC_ALPHA,
            );
        } else {
            gl::BlendFunc(gl::ONE, gl::ONE_MINUS_SRC_ALPHA);
        }
    }
}

impl Drop for GlFont {
    fn drop(&mut self) {
        unsafe {
            for g in self.glyphs.borrow().iter() {
                if g.tex_id != 0 {
                    gl::DeleteTextures(1, &g.tex_id);
                }
            }
            for face in self.faces.borrow().iter() {
                if !face.hb_font.is_null() {
                    hb_font_destroy(face.hb_font);
                }
                if !face.face.is_null() {
                    freetype_sys::FT_Done_Face(face.face);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;

    // All tests share the global `gl` loader and a single X display.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn font_hinting_uses_xft_properties() {
        unsafe {
            let pattern = FcPatternCreate();
            assert!(!pattern.is_null());
            FcPatternAddBool(pattern, c"hinting".as_ptr(), FC_TRUE);
            FcPatternAddInteger(pattern, c"hintstyle".as_ptr(), FC_HINT_MEDIUM);
            FcPatternAddInteger(pattern, c"rgba".as_ptr(), FC_RGBA_BGR);
            FcPatternAddInteger(pattern, c"lcdfilter".as_ptr(), FC_LCD_LIGHT);
            let hinting = FontHinting::from_xft_pattern(ptr::null_mut(), 0, pattern);
            assert_eq!(hinting.lcd_order, 2);
            assert_eq!(
                hinting.load_flags & (0xf << 16),
                freetype_sys::FT_LOAD_TARGET_LCD
            );
            assert_eq!(
                hinting.load_flags & freetype_sys::FT_LOAD_NO_HINTING,
                0
            );
            assert_eq!(hinting.lcd_filter, FT_LCD_LIGHT);
            FcPatternDestroy(pattern);

            let pattern = FcPatternCreate();
            assert!(!pattern.is_null());
            FcPatternAddBool(pattern, c"hinting".as_ptr(), 0);
            FcPatternAddInteger(pattern, c"hintstyle".as_ptr(), FC_HINT_NONE);
            FcPatternAddInteger(pattern, c"rgba".as_ptr(), 5);
            FcPatternAddInteger(pattern, c"lcdfilter".as_ptr(), FC_LCD_NONE);
            let hinting = FontHinting::from_xft_pattern(ptr::null_mut(), 0, pattern);
            assert_eq!(hinting.lcd_order, 0);
            assert_ne!(
                hinting.load_flags & freetype_sys::FT_LOAD_NO_HINTING,
                0
            );
            assert_eq!(hinting.lcd_filter, freetype_sys::FT_LCD_FILTER_NONE);
            FcPatternDestroy(pattern);
        }
    }

    /// 32-bit TrueColor visual, i.e. the same kind of ARGB visual the window
    /// manager picks for the finder and notification windows.
    unsafe fn argb_visual(dpy: *mut xlib::Display) -> *mut xlib::Visual {
        unsafe {
            let screen = xlib::XDefaultScreen(dpy);
            let mut template: xlib::XVisualInfo = std::mem::zeroed();
            template.screen = screen;
            template.depth = 32;
            template.class = xlib::TrueColor;
            let mut count = 0;
            let visuals = xlib::XGetVisualInfo(
                dpy,
                xlib::VisualScreenMask | xlib::VisualDepthMask | xlib::VisualClassMask,
                &mut template,
                &mut count,
            );
            if visuals.is_null() || count == 0 {
                return ptr::null_mut();
            }
            let visual = (*visuals).visual;
            xlib::XFree(visuals.cast());
            visual
        }
    }

    unsafe fn open_surface(width: u32, height: u32) -> Option<(*mut xlib::Display, EglSurface)> {
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return None;
            }
            let visual = argb_visual(dpy);
            if visual.is_null() {
                xlib::XCloseDisplay(dpy);
                return None;
            }
            // Tests exercise both paths, so allow the fallback explicitly
            // regardless of the production EGL_FALLBACK setting.
            match EglSurface::new(dpy, visual, width, height, true) {
                Ok(surface) => Some((dpy, surface)),
                Err(e) => {
                    eprintln!("skipping EGL test: {e}");
                    xlib::XCloseDisplay(dpy);
                    None
                }
            }
        }
    }

    /// With the fallback disabled, initialization must either use the direct
    /// pixmap path or fail loudly. It must never silently select the XImage
    /// readback target.
    #[test]
    fn fallback_can_be_disabled() {
        let _guard = TEST_LOCK.lock().unwrap();
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return;
            }
            let visual = argb_visual(dpy);
            if visual.is_null() {
                xlib::XCloseDisplay(dpy);
                return;
            }
            match EglSurface::new(dpy, visual, 16, 16, false) {
                Ok(gl) => assert_eq!(gl.framebuffer(), 0),
                Err(e) => assert!(
                    e.to_string().contains("EGL_FALLBACK is disabled"),
                    "unexpected EGL error: {e}"
                ),
            }
            xlib::XCloseDisplay(dpy);
        }
    }

    /// Exercises the real EGL path when a display and an ARGB32 visual exist.
    #[test]
    fn creates_binds_and_resizes_egl_surface() {
        let _guard = TEST_LOCK.lock().unwrap();
        unsafe {
            let Some((dpy, mut gl)) = open_surface(300, 40) else {
                return;
            };
            assert_eq!(gl.size(), (300, 40));
            assert_ne!(gl.picture(), 0);
            gl.make_current().expect("rebind EGL surface");

            gl.resize(320, 48).expect("resize EGL surface");
            assert_eq!(gl.size(), (320, 48));
            gl.make_current().expect("rebind resized EGL surface");
            gl.finish().expect("finish GL work");

            drop(gl);
            xlib::XCloseDisplay(dpy);
        }
    }

    /// Core invariant of both presentation paths: after `finish()`, XRender
    /// composites ARGB32 pixels from the surface picture.
    #[test]
    fn egl_surface_is_visible_to_xrender() {
        let _guard = TEST_LOCK.lock().unwrap();
        unsafe {
            let Some((dpy, mut gl)) = open_surface(64, 64) else {
                return;
            };
            gl.make_current().expect("EGL surface is current");
            gl::Viewport(0, 0, 64, 64);
            gl::ClearColor(1.0, 0.0, 0.0, 0.5);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            gl.finish().expect("flush GL into the pixmap");

            let format = xrender::XRenderFindStandardFormat(dpy, xrender::PictStandardARGB32);
            assert!(!format.is_null());
            let out = xlib::XCreatePixmap(dpy, xlib::XDefaultRootWindow(dpy), 64, 64, 32);
            let dst = xrender::XRenderCreatePicture(dpy, out, format, 0, ptr::null());
            xrender::XRenderComposite(
                dpy,
                xrender::PictOpSrc,
                gl.picture(),
                0,
                dst,
                0,
                0,
                0,
                0,
                0,
                0,
                64,
                64,
            );
            xlib::XSync(dpy, xlib::False);
            let image = xlib::XGetImage(dpy, out, 32, 32, 1, 1, xlib::XAllPlanes(), xlib::ZPixmap);
            assert!(!image.is_null());
            let pixel = xlib::XGetPixel(image, 0, 0);
            assert_eq!(
                pixel & 0xffff_ffff,
                0x80ff_0000,
                "EGL surface did not render as ARGB32"
            );
            xlib::XDestroyImage(image);
            xrender::XRenderFreePicture(dpy, dst);
            xlib::XFreePixmap(dpy, out);
            drop(gl);
            xlib::XCloseDisplay(dpy);
        }
    }

    /// FreeType + HarfBuzz text measurement and glyph texture upload through
    /// the same compatibility context used by the finder.
    #[test]
    fn glfont_measures_and_draws_text() {
        let _guard = TEST_LOCK.lock().unwrap();
        unsafe {
            let Some((dpy, gl)) = open_surface(320, 40) else {
                return;
            };
            let matched = std::process::Command::new("fc-match")
                .args(["-f", "%{file}", "sans-serif"])
                .output()
                .ok()
                .and_then(|o| String::from_utf8(o.stdout).ok())
                .unwrap_or_default();
            let specs = vec![GlFontSpec {
                file: matched,
                index: 0,
                pixel_size: 12.0,
            }];
            let hinting = FontHinting::from_xft_pattern(dpy, xlib::XDefaultScreen(dpy), ptr::null());
            let font = GlFont::new(&specs, 20, hinting, dpy, xlib::XDefaultScreen(dpy))
                .unwrap_or_else(|e| panic!("GLFont init failed: {e}"));
            assert!(font.height > 0);
            assert!(font.text_width("Finder") > 0);
            assert_eq!(font.text_width(""), 0);

            gl::Viewport(0, 0, 320, 40);
            gl::ClearColor(0.0, 0.0, 0.0, 0.0);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            let c = compat().expect("fixed-function GL entry points");
            c.matrix_mode(GL_PROJECTION);
            c.load_identity();
            c.ortho(0.0, 320.0, 40.0, 0.0, -1.0, 1.0);
            c.matrix_mode(GL_MODELVIEW);
            c.load_identity();
            font.draw_text("Finder", 8, 20, 300, (1.0, 1.0, 1.0), 1.0)
                .expect("draw GL text");
            assert_eq!(gl::GetError(), gl::NO_ERROR);
            let mut pixels = [0u8; 320 * 40 * 4];
            gl::ReadPixels(
                0,
                0,
                320,
                40,
                gl::RGBA,
                gl::UNSIGNED_BYTE,
                pixels.as_mut_ptr().cast(),
            );
            assert!(
                pixels.chunks_exact(4).any(|p| p[3] > 0),
                "expected visible glyph pixels"
            );
            drop(font);
            drop(gl);
            xlib::XCloseDisplay(dpy);
        }
    }

    /// Compiles the v120 shaders, validates the FBO, runs all five blur passes
    /// and reads back a visible pixel from the default EGL pixmap framebuffer.
    #[test]
    fn bloom_compiles_blurs_and_composites() {
        let _guard = TEST_LOCK.lock().unwrap();
        unsafe {
            let Some((dpy, gl)) = open_surface(300, 40) else {
                return;
            };
            let mut bloom = Bloom::new().unwrap_or_else(|e| panic!("bloom init failed: {e}"));
            assert!(bloom.ready());
            bloom.ensure_buffers(300, 40).expect("bloom buffers");
            assert_eq!(bloom.size(), (300, 40));

            bloom.ensure_buffers(320, 48).expect("bloom resize");
            assert_eq!(bloom.size(), (320, 48));
            bloom.delete_buffers();
            assert_eq!(bloom.size(), (0, 0));
            bloom.ensure_buffers(300, 40).expect("bloom recreate");

            gl::Viewport(0, 0, 300, 40);
            gl::ClearColor(0.0, 0.0, 0.0, 0.0);
            gl::Clear(gl::COLOR_BUFFER_BIT);
            while gl::GetError() != gl::NO_ERROR {}

            let c = compat().expect("fixed-function GL entry points");
            let drew = bloom
                .render(gl.framebuffer(), 300, 40, 2.0, 1.0, None, || {
                    gl::Disable(gl::TEXTURE_2D);
                    c.color4f(1.0, 1.0, 1.0, 1.0);
                    c.begin(gl::QUADS);
                    c.vertex2f(120.0, 10.0);
                    c.vertex2f(180.0, 10.0);
                    c.vertex2f(180.0, 30.0);
                    c.vertex2f(120.0, 30.0);
                    c.end();
                })
                .expect("bloom render");
            assert!(drew);
            assert_eq!(gl::GetError(), gl::NO_ERROR);

            let mut pixel = [0u8; 4];
            gl::ReadPixels(
                150,
                20,
                1,
                1,
                gl::RGBA,
                gl::UNSIGNED_BYTE,
                pixel.as_mut_ptr().cast(),
            );
            assert_eq!(gl::GetError(), gl::NO_ERROR);
            assert!(pixel[3] > 0, "expected visible bloom pixel, got {pixel:?}");

            // Bloom's final composite must respect the caller's scissor. Clip
            // to the left third and confirm the centre pixel stays cleared,
            // even though the offscreen blur was rendered across full width.
            unsafe {
                gl::Disable(gl::SCISSOR_TEST);
                gl::Clear(gl::COLOR_BUFFER_BIT);
                gl::Enable(gl::SCISSOR_TEST);
                gl::Scissor(0, 0, 100, 40);
            }
            let clipped = bloom
                .render(gl.framebuffer(), 300, 40, 2.0, 1.0, None, || {
                    gl::Disable(gl::TEXTURE_2D);
                    c.color4f(1.0, 1.0, 1.0, 1.0);
                    c.begin(gl::QUADS);
                    c.vertex2f(120.0, 10.0);
                    c.vertex2f(180.0, 10.0);
                    c.vertex2f(180.0, 30.0);
                    c.vertex2f(120.0, 30.0);
                    c.end();
                })
                .expect("clipped bloom render");
            assert!(clipped);
            unsafe {
                gl::Disable(gl::SCISSOR_TEST);
            }
            assert_eq!(gl::GetError(), gl::NO_ERROR);
            let mut clipped_pixel = [0u8; 4];
            gl::ReadPixels(
                150,
                20,
                1,
                1,
                gl::RGBA,
                gl::UNSIGNED_BYTE,
                clipped_pixel.as_mut_ptr().cast(),
            );
            assert_eq!(gl::GetError(), gl::NO_ERROR);
            assert_eq!(
                clipped_pixel[3], 0,
                "scissored bloom leaked outside the clip: {clipped_pixel:?}"
            );

            drop(bloom);
            drop(gl);
            xlib::XCloseDisplay(dpy);
        }
    }
}
