//! GLX pbuffer context, OpenGL entry-point loading and Kawase bloom for the
//! finder port.
//!
//! Port of AnDWM `dwm.c` 7581-7638 (`notification_gl_init`), 8496-8700
//! (`finder_gl_proc`, `finder_gl_bloom_load_procs`, shader/program/buffers/quad)
//! and 11639-11927 (the five-pass blur/composite used by the finder icons,
//! text and waiting backdrop). The context is a **legacy compatibility** one
//! created with `glXCreateNewContext(..., GLX_RGBA_TYPE, ...)`: the shaders are
//! GLSL v120 and the quads use the fixed-function matrix stack, so a core-only
//! context must never be requested here.
//!
//! The `gl` 0.14 crate intentionally omits deprecated fixed-function symbols,
//! so `glBegin`/`glVertex2f`/matrix-stack functions are loaded separately via
//! `glXGetProcAddressARB` and wrapped in [`CompatGl`].

// The context, loader and bloom are consumed by the font/presentation tasks
// that follow; keep a clean build while this module is still standalone.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{CString, c_char, c_int, c_uint, c_void};
use std::ptr;
use std::sync::OnceLock;

use freetype_sys::{
    FT_Bitmap, FT_Error, FT_Face, FT_GlyphSlot, FT_Load_Glyph, FT_Render_Glyph, FT_Render_Mode,
    FT_UInt, FT_ULong,
};
use gl::types::{GLchar, GLdouble, GLenum, GLfloat, GLint, GLsizei, GLuint};
use x11::glx::{self, GLXContext, GLXFBConfig};
use x11::xlib;
use x11::xrender;

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
/// dwm uses directly. They are resolved once, while the pbuffer context is
/// current, from the same `glXGetProcAddressARB` table as everything else.
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
        return Err(format!("GLX is missing compatibility entry point {name}").into());
    }
    // Function pointers and data pointers have the same representation on the
    // supported X11/GL platforms; transmute_copy keeps the raw pointer alive
    // for the copy without pretending it is a reference to a function.
    unsafe { Ok(std::mem::transmute_copy::<*const c_void, T>(&proc)) }
}

/// The offscreen GLX pbuffer that backs finder rendering. Created once and
/// reused; a size change recreates only the pbuffer, not the context. Dropping
/// it releases the current binding, pbuffer and context in that order.
pub struct GlPbuffer {
    dpy: *mut xlib::Display,
    fbconfig: GLXFBConfig,
    ctx: GLXContext,
    pbuffer: u64,
    width: u32,
    height: u32,
}

/// dwm.c 8496-8498: resolve one GL entry point through `glXGetProcAddressARB`.
/// `None` (a null pointer) is returned for unknown names so the `gl` crate can
/// apply its own EXT fallbacks, exactly like dwm's `...EXT` retry list.
fn proc_address(name: &str) -> *const c_void {
    let Ok(name) = CString::new(name) else {
        return ptr::null();
    };
    unsafe {
        glx::glXGetProcAddressARB(name.as_ptr() as *const u8)
            .map_or(ptr::null(), |f| f as *const c_void)
    }
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

/// dwm.c 8500-8567: load all GL symbols through `glXGetProcAddressARB` while
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
        return Err("GLX is missing framebuffer or shader entry points".into());
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

impl GlPbuffer {
    /// dwm.c 7581-7638: choose a pbuffer-capable FBConfig with an 8-bit alpha
    /// channel, create the legacy compatibility context and bind a pbuffer of
    /// `width` x `height`. Any failure returns an error and leaves no GL state
    /// behind, so the finder can stay inactive without touching the clock bar.
    pub fn new(dpy: *mut xlib::Display, screen: i32, width: u32, height: u32) -> Result<GlPbuffer> {
        let width = width.max(1);
        let height = height.max(1);
        unsafe {
            // The terminator is `None`, i.e. 0, as in dwm's attrs[].
            let attrs: [i32; 15] = [
                glx::GLX_X_RENDERABLE,
                xlib::True,
                glx::GLX_DRAWABLE_TYPE,
                glx::GLX_PBUFFER_BIT,
                glx::GLX_RENDER_TYPE,
                glx::GLX_RGBA_BIT,
                glx::GLX_RED_SIZE,
                8,
                glx::GLX_GREEN_SIZE,
                8,
                glx::GLX_BLUE_SIZE,
                8,
                glx::GLX_ALPHA_SIZE,
                8,
                0,
            ];
            let mut nconfigs = 0;
            let configs = glx::glXChooseFBConfig(dpy, screen, attrs.as_ptr(), &mut nconfigs);
            if configs.is_null() || nconfigs == 0 {
                if !configs.is_null() {
                    xlib::XFree(configs.cast());
                }
                return Err("GLX has no RGBA pbuffer configuration with 8-bit alpha".into());
            }
            let fbconfig: GLXFBConfig = *configs;
            xlib::XFree(configs.cast());

            // GLX_RGBA_TYPE, not glXCreateContextAttribsARB: GLSL v120 and the
            // fixed-function quads used by the bloom pipeline need compatibility GL.
            let ctx = glx::glXCreateNewContext(
                dpy,
                fbconfig,
                glx::GLX_RGBA_TYPE,
                ptr::null_mut(),
                xlib::True,
            );
            if ctx.is_null() {
                return Err("cannot create GLX context".into());
            }

            let pbuffer = match create_pbuffer(dpy, fbconfig, width, height) {
                Ok(p) => p,
                Err(e) => {
                    glx::glXDestroyContext(dpy, ctx);
                    return Err(e);
                }
            };

            if glx::glXMakeCurrent(dpy, pbuffer, ctx) == 0 {
                glx::glXDestroyPbuffer(dpy, pbuffer);
                glx::glXDestroyContext(dpy, ctx);
                return Err("cannot bind GLX pbuffer".into());
            }
            if let Err(e) = load_gl() {
                glx::glXMakeCurrent(dpy, 0, ptr::null_mut());
                glx::glXDestroyPbuffer(dpy, pbuffer);
                glx::glXDestroyContext(dpy, ctx);
                return Err(e);
            }

            Ok(GlPbuffer {
                dpy,
                fbconfig,
                ctx,
                pbuffer,
                width,
                height,
            })
        }
    }

    /// The bound pbuffer, for `glXMakeCurrent` after another drawable takes the
    /// context. Zero when the context has already been released.
    pub fn drawable(&self) -> u64 {
        self.pbuffer
    }

    /// Current pbuffer dimensions.
    pub fn size(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    /// dwm.c 7610-7629: recreate the pbuffer when the requested size changes.
    /// The context itself survives, so shader and texture state stay intact.
    pub fn resize(&mut self, width: u32, height: u32) -> Result {
        let width = width.max(1);
        let height = height.max(1);
        if (width, height) == (self.width, self.height) {
            return Ok(());
        }
        unsafe {
            glx::glXMakeCurrent(self.dpy, 0, ptr::null_mut());
            glx::glXDestroyPbuffer(self.dpy, self.pbuffer);
            self.pbuffer = 0;
            self.width = 0;
            self.height = 0;

            let pbuffer = create_pbuffer(self.dpy, self.fbconfig, width, height)?;
            if glx::glXMakeCurrent(self.dpy, pbuffer, self.ctx) == 0 {
                glx::glXDestroyPbuffer(self.dpy, pbuffer);
                return Err("cannot bind resized GLX pbuffer".into());
            }
            self.pbuffer = pbuffer;
            self.width = width;
            self.height = height;
        }
        Ok(())
    }

    /// Rebind this context after another drawable was made current.
    pub fn make_current(&self) -> Result {
        unsafe {
            if glx::glXMakeCurrent(self.dpy, self.pbuffer, self.ctx) == 0 {
                return Err("cannot bind GLX pbuffer".into());
            }
        }
        Ok(())
    }
}

/// dwm.c 7616-7626: build the `GLX_PBUFFER_WIDTH`/`HEIGHT` attribute list and
/// create the offscreen drawable.
unsafe fn create_pbuffer(
    dpy: *mut xlib::Display,
    fbconfig: GLXFBConfig,
    w: u32,
    h: u32,
) -> Result<u64> {
    let attrs: [i32; 5] = [
        glx::GLX_PBUFFER_WIDTH,
        w as i32,
        glx::GLX_PBUFFER_HEIGHT,
        h as i32,
        0,
    ];
    unsafe {
        let pbuffer = glx::glXCreatePbuffer(dpy, fbconfig, attrs.as_ptr());
        if pbuffer == 0 {
            return Err("cannot create GLX pbuffer".into());
        }
        Ok(pbuffer)
    }
}

impl Drop for GlPbuffer {
    fn drop(&mut self) {
        // Mesa's software renderer raises BadMatch from X_ShmPutImage when a
        // resized GLX pbuffer is unbound and destroyed. Finder keeps one
        // pbuffer for the process lifetime, so leave the context and drawable
        // for the X server to reclaim when the display connection closes.
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
            let _state = BloomState::new(c, width, height)?;

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
            gl::BindFramebuffer(gl::FRAMEBUFFER, 0);
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
/// and restores it on every exit path. This mirrors 11654-11655, 11656-11662,
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
// GL -> ARGB32 XImage presentation (dwm.c 9255-9430, 11392-11428)
// ---------------------------------------------------------------------------

/// Owns the 32-bit ARGB pixmap/picture that receives the GL framebuffer.
/// `glReadPixels` is done with `GL_BGRA`, which is byte-for-byte `ARGB32` on
/// little-endian hosts, then the rows are flipped because GL rows start at the
/// bottom while XImage rows start at the top. The resulting picture is handed
/// to `Drw::map_picture`, which composites it onto the ARGB clock/finder
/// window with XRender (XCopyArea would raise `BadMatch`).
pub struct GlSurface {
    dpy: *mut xlib::Display,
    visual: *mut xlib::Visual,
    pixmap: xlib::Pixmap,
    picture: xrender::Picture,
    image: *mut xlib::XImage,
    width: u32,
    height: u32,
}

impl GlSurface {
    pub fn new(
        dpy: *mut xlib::Display,
        visual: *mut xlib::Visual,
        width: u32,
        height: u32,
    ) -> Result<GlSurface> {
        let mut surface = GlSurface {
            dpy,
            visual,
            pixmap: 0,
            picture: 0,
            image: ptr::null_mut(),
            width: 0,
            height: 0,
        };
        surface.resize(width, height)?;
        Ok(surface)
    }

    pub fn picture(&self) -> xrender::Picture {
        self.picture
    }

    pub fn size(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    /// Overwrites the alpha byte of one readback pixel before it is copied into
    /// the presentation pixmap. The notification popup uses this to apply
    /// dwm's vertical opacity ramp directly to its transparent foreground.
    pub fn set_alpha(&mut self, x: u32, y: u32, alpha: u8) {
        if x >= self.width || y >= self.height || self.image.is_null() {
            return;
        }
        unsafe {
            let image = &*self.image;
            let bpl = image.bytes_per_line as usize;
            let data = image.data as *mut u8;
            let offset = y as usize * bpl + x as usize * 4;
            let alpha_index = if image.byte_order == xlib::LSBFirst {
                3
            } else {
                0
            };
            *data.add(offset + alpha_index) = alpha;
        }
    }

    pub fn resize(&mut self, width: u32, height: u32) -> Result<()> {
        let width = width.max(1);
        let height = height.max(1);
        if self.picture != 0 && (self.width, self.height) == (width, height) {
            return Ok(());
        }
        self.destroy();
        unsafe {
            let image = xlib::XCreateImage(
                self.dpy,
                self.visual,
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
                return Err("cannot allocate ARGB32 XImage for finder GL readback".into());
            }
            // XCreateImage does not allocate the pixel buffer when passed a
            // NULL data pointer; it leaves image->data NULL. dwm assigns an
            // ecalloc'd buffer here. Use calloc so XDestroyImage's XFree can
            // release it later without an incompatible allocator.
            let bytes = (*image).bytes_per_line as usize * height as usize;
            let data = libc::calloc(bytes, 1) as *mut c_char;
            if data.is_null() {
                xlib::XDestroyImage(image);
                return Err("cannot allocate ARGB32 XImage data for finder GL readback".into());
            }
            (*image).data = data;
            (*image).byte_order = xlib::XImageByteOrder(self.dpy);
            (*image).bitmap_unit = xlib::XBitmapUnit(self.dpy);
            (*image).bitmap_bit_order = xlib::XBitmapBitOrder(self.dpy);
            let pixmap = xlib::XCreatePixmap(
                self.dpy,
                xlib::XDefaultRootWindow(self.dpy),
                width,
                height,
                32,
            );
            if pixmap == 0 {
                xlib::XDestroyImage(image);
                return Err("cannot create ARGB32 pixmap for finder GL readback".into());
            }
            let format = xrender::XRenderFindStandardFormat(self.dpy, xrender::PictStandardARGB32);
            if format.is_null() {
                xlib::XFreePixmap(self.dpy, pixmap);
                xlib::XDestroyImage(image);
                return Err("XRender has no ARGB32 picture format".into());
            }
            let picture = xrender::XRenderCreatePicture(self.dpy, pixmap, format, 0, ptr::null());
            if picture == 0 {
                xlib::XFreePixmap(self.dpy, pixmap);
                xlib::XDestroyImage(image);
                return Err("cannot create XRender picture for finder GL readback".into());
            }
            self.image = image;
            self.pixmap = pixmap;
            self.picture = picture;
            self.width = width;
            self.height = height;
        }
        Ok(())
    }

    /// Reads the currently bound GL drawable into the ARGB32 pixmap. The
    /// caller must make the pbuffer current first.
    pub fn readback(&mut self) -> Result<()> {
        self.readback_with_alpha(|_, _| None)
    }

    /// Same as [`Self::readback`], but lets the caller replace each pixel's
    /// alpha before the XImage is committed to the pixmap. dwm applies the
    /// notification's vertical opacity ramp at this point; applying it after
    /// `XPutImage` would leave the present pixmap unchanged.
    pub fn readback_with_alpha<F>(&mut self, mut alpha: F) -> Result<()>
    where
        F: FnMut(u32, u32) -> Option<u8>,
    {
        if self.image.is_null() {
            return Err("finder GL surface is not initialized".into());
        }
        unsafe {
            let image = &mut *self.image;
            let w = self.width as GLsizei;
            let h = self.height as GLsizei;
            let mut pixels = vec![0u8; (w * h * 4) as usize];
            gl::ReadPixels(
                0,
                0,
                w,
                h,
                gl::BGRA,
                gl::UNSIGNED_BYTE,
                pixels.as_mut_ptr() as *mut c_void,
            );
            let err = gl::GetError();
            if err != gl::NO_ERROR {
                return Err(format!("finder GL readback failed: {err:#x}").into());
            }
            let bpl = image.bytes_per_line as usize;
            let little_endian = image.byte_order == xlib::LSBFirst;
            let alpha_index = if little_endian { 3 } else { 0 };
            let dst = image.data as *mut u8;
            for y in 0..self.height as usize {
                let src_row = &pixels[(h as usize - 1 - y) * w as usize * 4..];
                let dst_row = std::slice::from_raw_parts_mut(dst.add(y * bpl), (w * 4) as usize);
                if little_endian {
                    // BGRA in memory is 0xAARRGGBB on little-endian hosts.
                    dst_row.copy_from_slice(&src_row[..(w * 4) as usize]);
                } else {
                    for (d, s) in dst_row.chunks_exact_mut(4).zip(src_row.chunks_exact(4)) {
                        d[0] = s[3];
                        d[1] = s[2];
                        d[2] = s[1];
                        d[3] = s[0];
                    }
                }
                for x in 0..self.width {
                    if let Some(value) = alpha(x, y as u32) {
                        dst_row[x as usize * 4 + alpha_index] = value;
                    }
                }
            }
            let gc = xlib::XCreateGC(self.dpy, self.pixmap, 0, ptr::null_mut());
            if !gc.is_null() {
                xlib::XPutImage(
                    self.dpy,
                    self.pixmap,
                    gc,
                    image,
                    0,
                    0,
                    0,
                    0,
                    self.width,
                    self.height,
                );
                xlib::XFreeGC(self.dpy, gc);
            }
        }
        Ok(())
    }

    fn destroy(&mut self) {
        unsafe {
            if self.picture != 0 {
                xrender::XRenderFreePicture(self.dpy, self.picture);
            }
            if self.pixmap != 0 {
                xlib::XFreePixmap(self.dpy, self.pixmap);
            }
            if !self.image.is_null() {
                xlib::XDestroyImage(self.image);
            }
        }
        self.picture = 0;
        self.pixmap = 0;
        self.image = ptr::null_mut();
        self.width = 0;
        self.height = 0;
    }
}

impl Drop for GlSurface {
    fn drop(&mut self) {
        self.destroy();
    }
}

// ---------------------------------------------------------------------------
// GLFont: FreeType glyph textures + HarfBuzz shaping (dwm.c 8703-9206)
// ---------------------------------------------------------------------------

const GL_FONT_MAX_FACES: usize = 32;
const GL_FONT_MAX_GLYPHS: usize = 2048;

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
/// shaping per face run. This mirrors dwm's `GLFont` exactly: no glyph atlas,
/// `GL_RGBA`/`GL_UNSIGNED_BYTE` upload and `GL_NEAREST` filtering.
pub struct GlFont {
    faces: Vec<GlFontFace>,
    /// Rasterized glyph cache. Text measuring needs glyph shaping but callers
    /// often only hold a shared reference during layout, so the cache uses
    /// interior mutability instead of forcing `&mut self` on every method.
    glyphs: RefCell<Vec<GlGlyph>>,
    glyph_index: RefCell<HashMap<(u32, u32), usize>>,
    pub height: i32,
    pub pixel_size: f64,
    pub lcd_order: u8,
}

impl GlFont {
    /// dwm.c 8707-8846: load up to 32 Xft-resolved faces at their own pixel
    /// sizes, set a 72 dpi char size so one pixel maps to one font unit, and
    /// create a HarfBuzz font with light hinting for each one.
    pub fn new(specs: &[GlFontSpec], height: i32, lcd_order: u8) -> Result<GlFont> {
        let library = ft_library()?;
        let mut lcd_order = lcd_order;
        if lcd_order != 0 {
            let err = unsafe {
                freetype_sys::FT_Library_SetLcdFilter(
                    library as freetype_sys::FT_Library,
                    freetype_sys::FT_LCD_FILTER_DEFAULT,
                )
            };
            if err != 0 {
                lcd_order = 0;
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
            if let Ok(face) = Self::add_face(library, &spec.file, spec.index, pixel_size) {
                faces.push(face);
            }
        }
        if faces.is_empty() {
            for file in [
                "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
                "/usr/share/fonts/TTF/DejaVuSans.ttf",
                "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
            ] {
                if let Ok(face) = Self::add_face(library, file, 0, base_size) {
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
            faces,
            glyphs: RefCell::new(Vec::new()),
            glyph_index: RefCell::new(HashMap::new()),
            height,
            pixel_size: base_size,
            lcd_order,
        })
    }

    fn add_face(library: FT_Face, file: &str, index: i32, pixel_size: f64) -> Result<GlFontFace> {
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
        unsafe {
            hb_ft_font_set_load_flags(
                hb_font,
                freetype_sys::FT_LOAD_DEFAULT | freetype_sys::FT_LOAD_TARGET_LIGHT,
            );
        }
        Ok(GlFontFace {
            face,
            hb_font,
            file: file.to_string(),
            index,
            pixel_size,
        })
    }

    pub fn ascender(&self) -> i32 {
        unsafe {
            let a = (*(*self.faces[0].face).size).metrics.ascender >> 6;
            a.max(1) as i32
        }
    }

    /// FreeType's descender in whole pixels. Used by the notification layout,
    /// which sizes its text blocks from the same metrics as dwm's GL font.
    pub fn descender(&self) -> i32 {
        unsafe {
            let d = -((*(*self.faces[0].face).size).metrics.descender >> 6);
            d.max(0) as i32
        }
    }

    fn face_for(&self, ch: char) -> usize {
        let cp = ch as FT_ULong;
        for (i, f) in self.faces.iter().enumerate() {
            if unsafe { freetype_sys::FT_Get_Char_Index(f.face, cp) } != 0 {
                return i;
            }
        }
        0
    }

    /// Groups consecutive characters by the face that can render them and
    /// shapes each run with HarfBuzz, as dwm's two helper loops do.
    fn shaped_glyphs(&self, text: &str) -> Vec<(usize, u32, HbGlyphPosition)> {
        let chars: Vec<(char, usize)> = text
            .chars()
            .map(|ch| {
                let face = self.face_for(ch);
                (ch, face)
            })
            .collect();
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
        if face_index >= self.faces.len() {
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
            hb_shape(self.faces[face_index].hb_font, buffer, ptr::null(), 0);
            let mut count: c_uint = 0;
            let infos = hb_buffer_get_glyph_infos(buffer, &mut count);
            let positions = hb_buffer_get_glyph_positions(buffer, &mut count);
            let mut out = Vec::with_capacity(count as usize);
            if !infos.is_null() && !positions.is_null() {
                for i in 0..count as usize {
                    out.push((face_index, (*infos.add(i)).codepoint, *positions.add(i)));
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
        let font = self.faces.get(face_index as usize)?;
        let face = font.face;
        let load_flags = freetype_sys::FT_LOAD_DEFAULT | freetype_sys::FT_LOAD_TARGET_LIGHT;
        let err: FT_Error = unsafe { FT_Load_Glyph(face, glyph_index as FT_UInt, load_flags) };
        if err != 0 {
            return None;
        }
        let lcd = self.lcd_order != 0;
        let mut mode: FT_Render_Mode = if lcd {
            freetype_sys::FT_RENDER_MODE_LCD
        } else {
            freetype_sys::FT_RENDER_MODE_NORMAL
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
        let is_lcd = bitmap.pixel_mode as u32 == freetype_sys::FT_PIXEL_MODE_LCD;
        let w = if is_lcd {
            bitmap.width / 3
        } else {
            bitmap.width
        };
        let h = bitmap.rows;
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
            for y in 0..h {
                let row = if bitmap.pitch >= 0 {
                    unsafe { bitmap.buffer.add(y as usize * bitmap.pitch as usize) }
                } else {
                    // Negative pitch: row 0 is stored last in memory.
                    unsafe {
                        bitmap
                            .buffer
                            .add((h - 1 - y) as usize * (-bitmap.pitch) as usize)
                    }
                };
                for x in 0..w {
                    let (r, g, b, a) = if is_lcd {
                        let rgb = unsafe { std::slice::from_raw_parts(row.add(x as usize * 3), 3) };
                        let (r, g, b) = if self.lcd_order == 2 {
                            (rgb[2], rgb[1], rgb[0])
                        } else {
                            (rgb[0], rgb[1], rgb[2])
                        };
                        (r, g, b, r.max(g).max(b))
                    } else if bitmap.pixel_mode as u32 == freetype_sys::FT_PIXEL_MODE_MONO {
                        let byte = unsafe { *row.add(x as usize / 8) };
                        let bit = if byte & (0x80 >> (x as usize % 8)) != 0 {
                            255
                        } else {
                            0
                        };
                        (bit, bit, bit, bit)
                    } else {
                        let coverage = unsafe { *row.add(x as usize) };
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
        if glyphs.len() < GL_FONT_MAX_GLYPHS {
            let slot = glyphs.len();
            glyphs.push(glyph);
            self.glyph_index.borrow_mut().insert(key, slot);
            Some(glyph)
        } else {
            Some(glyph)
        }
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
            for face in &self.faces {
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
    use super::*;

    /// Exercises the real GLX path when a display is available. Headless builds
    /// skip it: Xvfb is not installed in the development environment, but the
    /// live `:0` display is used for this one focused check.
    #[test]
    fn creates_binds_resizes_and_releases_legacy_pbuffer() {
        if std::env::var_os("DISPLAY").is_none() {
            return;
        }
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return;
            }
            let screen = xlib::XDefaultScreen(dpy);
            let mut gl = GlPbuffer::new(dpy, screen, 300, 40)
                .unwrap_or_else(|e| panic!("GLX pbuffer init failed: {e}"));
            assert_eq!(gl.size(), (300, 40));
            assert_ne!(gl.drawable(), 0);
            assert!(!gl.ctx.is_null());
            assert_eq!(glx::glXGetCurrentContext(), gl.ctx);

            gl.resize(320, 48).expect("resize pbuffer");
            assert_eq!(gl.size(), (320, 48));
            assert_eq!(glx::glXGetCurrentContext(), gl.ctx);
            gl.make_current().expect("rebind pbuffer");

            // Finder deliberately leaves its single GLX pbuffer alive until
            // the display closes, because Mesa's software renderer raises
            // BadMatch when a resized pbuffer is unbound. The test releases it
            // explicitly after checking that Drop honors that policy.
            let ctx = gl.ctx;
            let pbuffer = gl.drawable();
            drop(gl);
            assert_eq!(glx::glXGetCurrentContext(), ctx);
            glx::glXMakeCurrent(dpy, 0, ptr::null_mut());
            glx::glXDestroyPbuffer(dpy, pbuffer);
            glx::glXDestroyContext(dpy, ctx);
            xlib::XCloseDisplay(dpy);
        }
    }

    /// FreeType + HarfBuzz text measurement and glyph texture upload through
    /// the same legacy pbuffer context used by the finder.
    #[test]
    fn glfont_measures_and_draws_text() {
        if std::env::var_os("DISPLAY").is_none() {
            return;
        }
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return;
            }
            let screen = xlib::XDefaultScreen(dpy);
            let gl = GlPbuffer::new(dpy, screen, 320, 40)
                .unwrap_or_else(|e| panic!("GLX pbuffer init failed: {e}"));
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
            let mut font =
                GlFont::new(&specs, 20, 0).unwrap_or_else(|e| panic!("GLFont init failed: {e}"));
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
    /// and reads back a visible pixel from the default pbuffer framebuffer.
    #[test]
    fn bloom_compiles_blurs_and_composites() {
        if std::env::var_os("DISPLAY").is_none() {
            return;
        }
        unsafe {
            let dpy = xlib::XOpenDisplay(ptr::null());
            if dpy.is_null() {
                return;
            }
            let screen = xlib::XDefaultScreen(dpy);
            let gl = GlPbuffer::new(dpy, screen, 300, 40)
                .unwrap_or_else(|e| panic!("GLX pbuffer init failed: {e}"));
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
                .render(300, 40, 2.0, 1.0, None, || {
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

            drop(bloom);
            drop(gl);
            xlib::XCloseDisplay(dpy);
        }
    }
}
