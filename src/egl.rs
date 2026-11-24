//! Minimal EGL 1.5 bindings for the X11 pixmap presentation path.
//!
//! Only the entry points rwm needs are declared here. In particular the X11
//! platform is selected explicitly so EGL uses the same `Display` as Xlib and
//! XRender; `eglGetDisplay` would pick one from the environment instead.
//!
//! The X11 pixmap surface is matched to the 32-bit ARGB visual chosen by the
//! window manager. Mesa and the proprietary drivers then render GL straight
//! into that pixmap in ARGB32 layout, which is exactly what XRender consumes:
//! no GLX pbuffer, no GPU-to-CPU readback and no `XPutImage` upload.

#![allow(non_camel_case_types, dead_code)]

use std::ffi::{c_char, c_int, c_uint, c_void};

pub type EGLBoolean = c_uint;
pub type EGLDisplay = *mut c_void;
pub type EGLConfig = *mut c_void;
pub type EGLContext = *mut c_void;
pub type EGLSurface = *mut c_void;
pub type EGLNativePixmapType = u64;
pub type EGLNativeDisplayType = *mut c_void;
pub type EGLenum = c_uint;
pub type EGLint = c_int;
pub type EGLAttrib = isize;

/// EGL_PLATFORM_X11_KHR (also EGL_PLATFORM_X11 in EGL 1.5).
pub const PLATFORM_X11: EGLenum = 0x31d5;
pub const OPENGL_API: EGLenum = 0x30a2;
pub const SURFACE_TYPE: EGLint = 0x3033;
pub const PIXMAP_BIT: EGLint = 0x0002;
pub const RENDERABLE_TYPE: EGLint = 0x3040;
pub const OPENGL_BIT: EGLint = 0x0008;
pub const RED_SIZE: EGLint = 0x3024;
pub const GREEN_SIZE: EGLint = 0x3023;
pub const BLUE_SIZE: EGLint = 0x3022;
pub const ALPHA_SIZE: EGLint = 0x3021;
pub const NATIVE_VISUAL_ID: EGLint = 0x302e;
pub const NONE: EGLint = 0x3038;

#[link(name = "EGL")]
unsafe extern "C" {
    fn eglGetPlatformDisplay(
        platform: EGLenum,
        native_display: EGLNativeDisplayType,
        attrib_list: *const EGLAttrib,
    ) -> EGLDisplay;
    fn eglGetDisplay(display_id: EGLNativeDisplayType) -> EGLDisplay;
    fn eglInitialize(dpy: EGLDisplay, major: *mut EGLint, minor: *mut EGLint) -> EGLBoolean;
    fn eglTerminate(dpy: EGLDisplay) -> EGLBoolean;
    fn eglBindAPI(api: EGLenum) -> EGLBoolean;
    fn eglChooseConfig(
        dpy: EGLDisplay,
        attrib_list: *const EGLint,
        configs: *mut EGLConfig,
        config_size: EGLint,
        num_config: *mut EGLint,
    ) -> EGLBoolean;
    fn eglCreatePixmapSurface(
        dpy: EGLDisplay,
        config: EGLConfig,
        pixmap: EGLNativePixmapType,
        attrib_list: *const EGLint,
    ) -> EGLSurface;
    fn eglCreateContext(
        dpy: EGLDisplay,
        config: EGLConfig,
        share_context: EGLContext,
        attrib_list: *const EGLint,
    ) -> EGLContext;
    fn eglMakeCurrent(
        dpy: EGLDisplay,
        draw: EGLSurface,
        read: EGLSurface,
        ctx: EGLContext,
    ) -> EGLBoolean;
    fn eglDestroySurface(dpy: EGLDisplay, surface: EGLSurface) -> EGLBoolean;
    fn eglDestroyContext(dpy: EGLDisplay, ctx: EGLContext) -> EGLBoolean;
    fn eglGetProcAddress(name: *const c_char) -> Option<unsafe extern "C" fn()>;
    fn eglGetError() -> EGLint;
}

pub fn platform_display(native: EGLNativeDisplayType) -> EGLDisplay {
    unsafe {
        // EGL 1.5 core entry point. Older runtime libraries can be missing it
        // even though the headers are new enough, so fall back to eglGetDisplay.
        let dpy = eglGetPlatformDisplay(PLATFORM_X11, native, std::ptr::null());
        if dpy.is_null() {
            eglGetDisplay(native)
        } else {
            dpy
        }
    }
}

pub fn initialize(dpy: EGLDisplay) -> EGLBoolean {
    let mut major = 0;
    let mut minor = 0;
    unsafe { eglInitialize(dpy, &mut major, &mut minor) }
}

pub fn terminate(dpy: EGLDisplay) {
    unsafe {
        eglTerminate(dpy);
    }
}

pub fn bind_api(api: EGLenum) -> EGLBoolean {
    unsafe { eglBindAPI(api) }
}

pub fn choose_config(
    dpy: EGLDisplay,
    attrs: *const EGLint,
    config: *mut EGLConfig,
    count: *mut EGLint,
) -> EGLBoolean {
    unsafe { eglChooseConfig(dpy, attrs, config, 1, count) }
}

pub fn create_pixmap_surface(
    dpy: EGLDisplay,
    config: EGLConfig,
    pixmap: EGLNativePixmapType,
) -> EGLSurface {
    unsafe { eglCreatePixmapSurface(dpy, config, pixmap, std::ptr::null()) }
}

pub fn create_context(dpy: EGLDisplay, config: EGLConfig) -> EGLContext {
    // No context attributes: keep the compatibility profile so the v120
    // bloom shaders and fixed-function quads keep working unchanged.
    unsafe { eglCreateContext(dpy, config, std::ptr::null_mut(), std::ptr::null()) }
}

pub fn make_current(dpy: EGLDisplay, surface: EGLSurface, ctx: EGLContext) -> EGLBoolean {
    unsafe { eglMakeCurrent(dpy, surface, surface, ctx) }
}

pub fn release_current(dpy: EGLDisplay) {
    unsafe {
        eglMakeCurrent(
            dpy,
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            std::ptr::null_mut(),
        );
    }
}

pub fn destroy_surface(dpy: EGLDisplay, surface: EGLSurface) {
    if !surface.is_null() {
        unsafe {
            eglDestroySurface(dpy, surface);
        }
    }
}

pub fn destroy_context(dpy: EGLDisplay, ctx: EGLContext) {
    if !ctx.is_null() {
        unsafe {
            eglDestroyContext(dpy, ctx);
        }
    }
}

pub fn proc_address(name: &str) -> *mut c_void {
    let Ok(name) = std::ffi::CString::new(name) else {
        return std::ptr::null_mut();
    };
    unsafe { eglGetProcAddress(name.as_ptr()).map_or(std::ptr::null_mut(), |f| f as *mut c_void) }
}

/// Human-readable suffix for an EGL failure, e.g. ` (error 0x3008)`.
pub fn error(op: &str) -> String {
    unsafe { format!("{op} failed (EGL error {:#x})", eglGetError()) }
}
