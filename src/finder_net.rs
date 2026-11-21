//! Finder network helpers: asynchronous Google translation through `curl` and
//! interactive OCR region capture piped to `tesseract`.
//!
//! Both operations hand their result back through [`FinderNet::poll`] so the
//! WM event loop never waits on a subprocess. Only the OCR pointer grab is
//! synchronous, because it has to follow the user's drag in real time.

use std::collections::HashMap;
use std::ffi::{c_int, c_uint, c_ulong};
use std::io::{Read, Write};
use std::mem;
use std::process::{Child, ChildStdout, Command, ExitStatus, Stdio};
use std::ptr;
use std::sync::{Arc, Mutex, mpsc};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use image::codecs::png::PngEncoder;
use image::{ColorType, ImageEncoder, Rgba, RgbaImage};
use x11::xlib;

const TRANSLATION_ERROR: &str = "Translation unavailable (curl required)";
const TRANSLATION_PARSE_ERROR: &str = "Translation unavailable";
const OCR_ERROR: &str = "OCR unavailable";
const OCR_TESSERACT_ERROR: &str = "OCR unavailable (tesseract required)";

/// dwm's `FINDER_TRANSLATE_MAX`.
const RESPONSE_LIMIT: usize = 8192;
/// dwm's `FINDER_TRANSLATE_RESULT`.
const RESULT_LIMIT: usize = 2048;
const SELECT_TIMEOUT: Duration = Duration::from_secs(30);
const WORKER_POLL: Duration = Duration::from_millis(10);
const MAX_CAPTURE_BYTES: usize = 64 * 1024 * 1024;
const JSON_DEPTH_LIMIT: u8 = 32;

/// `XC_crosshair` from X11/cursorfont.h. The x11 crate does not export it.
const XC_CROSSHAIR: c_uint = 2;

/// dwm asks tesseract for English, Thai and Japanese. Installations that only
/// ship English would otherwise fail before reading the captured image, so use
/// the subset that is actually available.
fn ocr_languages() -> String {
    let Ok(output) = Command::new("tesseract").arg("--list-langs").output() else {
        return "eng".to_string();
    };
    let listed = String::from_utf8_lossy(&output.stdout);
    let available: Vec<&str> = ["eng", "tha", "jpn"]
        .into_iter()
        .filter(|lang| listed.lines().any(|line| line.trim() == *lang))
        .collect();
    if available.is_empty() {
        "eng".to_string()
    } else {
        available.join("+")
    }
}

/// A completed asynchronous Finder network operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NetResult {
    Translate(String),
    Ocr(String),
    Error(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum JobKind {
    Translate,
    Ocr,
}

struct Job {
    kind: JobKind,
    child: Arc<Mutex<Option<Child>>>,
    rx: mpsc::Receiver<NetResult>,
    thread: Option<JoinHandle<()>>,
}

/// Owner of at most one in-flight translation or OCR subprocess.
pub struct FinderNet {
    job: Option<Job>,
}

impl FinderNet {
    pub fn new() -> Self {
        Self { job: None }
    }

    /// Returns true while a translation or OCR subprocess is in flight.
    pub fn is_busy(&self) -> bool {
        self.job.is_some()
    }

    /// Starts a background `curl` translation.
    ///
    /// `target_en` matches dwm's `finder_translate_target_en`: when true the
    /// target language is English, otherwise it is Thai. A synchronous spawn
    /// failure returns `"Translation unavailable (curl required)"`; runtime
    /// failures arrive through [`FinderNet::poll`] as [`NetResult::Error`].
    pub fn translate(&mut self, text: &str, target_en: bool) -> Result<(), String> {
        self.cancel();

        let target = if target_en { "tl=en" } else { "tl=th" };
        let query = format!("q={text}");
        let mut child = Command::new("curl")
            .args([
                "--silent",
                "--fail",
                "--max-time",
                "8",
                "--user-agent",
                "Mozilla/5.0",
                "--get",
                "--data-urlencode",
                "client=dict-chrome-ex",
                "--data-urlencode",
                "sl=auto",
                "--data-urlencode",
            ])
            .arg(target)
            .arg("--data-urlencode")
            .arg(&query)
            .arg("https://clients5.google.com/translate_a/t")
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|_| TRANSLATION_ERROR.to_string())?;

        let Some(stdout) = child.stdout.take() else {
            let _ = child.kill();
            let _ = child.wait();
            return Err(TRANSLATION_ERROR.to_string());
        };

        let shared = Arc::new(Mutex::new(Some(child)));
        let worker_child = Arc::clone(&shared);
        let (tx, rx) = mpsc::channel();
        let thread = thread::spawn(move || {
            let (response, read_ok) = read_bounded(stdout);
            let status_ok = reap_child(&worker_child).is_some_and(|status| status.success());
            let result = if !read_ok || !status_ok {
                NetResult::Error(TRANSLATION_ERROR.to_string())
            } else {
                match parse_translation_response(&response) {
                    Some(text) => NetResult::Translate(text),
                    None => NetResult::Error(TRANSLATION_PARSE_ERROR.to_string()),
                }
            };
            let _ = tx.send(result);
        });

        self.job = Some(Job {
            kind: JobKind::Translate,
            child: shared,
            rx,
            thread: Some(thread),
        });
        Ok(())
    }

    /// Selects a screen region with an Xlib pointer grab, captures it, and
    /// starts background OCR. The grab lasts only until mouse release (or a
    /// 30 second safety timeout); OCR itself runs in a worker thread.
    pub fn ocr_region(&mut self, dpy: *mut xlib::Display) -> Result<(), String> {
        self.cancel();
        if dpy.is_null() {
            return Err(OCR_ERROR.to_string());
        }

        let rect = unsafe { select_region(dpy)? };
        let png = unsafe { capture_region(dpy, rect)? };

        let mut child = Command::new("tesseract")
            .args([
                "stdin",
                "stdout",
                "--oem",
                "1",
                "--psm",
                "6",
                "-c",
                "preserve_interword_spaces=1",
                "-l",
                &ocr_languages(),
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|_| OCR_TESSERACT_ERROR.to_string())?;

        let stdin = child.stdin.take();
        let Some(stdout) = child.stdout.take() else {
            let _ = child.kill();
            let _ = child.wait();
            return Err(OCR_TESSERACT_ERROR.to_string());
        };

        let shared = Arc::new(Mutex::new(Some(child)));
        let worker_child = Arc::clone(&shared);
        let (tx, rx) = mpsc::channel();
        let thread = thread::spawn(move || {
            if let Some(mut stdin) = stdin {
                let _ = stdin.write_all(&png);
            }
            let (response, read_ok) = read_bounded(stdout);
            let status_ok = reap_child(&worker_child).is_some_and(|status| status.success());
            let result = if !read_ok || !status_ok {
                NetResult::Error(OCR_ERROR.to_string())
            } else {
                let text = String::from_utf8_lossy(&response);
                let text = bound_utf8(text.trim(), RESULT_LIMIT);
                if text.is_empty() {
                    NetResult::Error(OCR_ERROR.to_string())
                } else {
                    NetResult::Ocr(text)
                }
            };
            let _ = tx.send(result);
        });

        self.job = Some(Job {
            kind: JobKind::Ocr,
            child: shared,
            rx,
            thread: Some(thread),
        });
        Ok(())
    }

    /// Takes a completed result if one is available. Never blocks.
    pub fn poll(&mut self) -> Option<NetResult> {
        let kind = self.job.as_ref()?.kind;
        let result = match self.job.as_ref()?.rx.try_recv() {
            Ok(result) => result,
            Err(mpsc::TryRecvError::Empty) => return None,
            Err(mpsc::TryRecvError::Disconnected) => NetResult::Error(match kind {
                JobKind::Translate => TRANSLATION_ERROR.to_string(),
                JobKind::Ocr => OCR_ERROR.to_string(),
            }),
        };

        if let Some(job) = self.job.take() {
            if let Some(thread) = job.thread {
                let _ = thread.join();
            }
            kill_child(&job.child);
        }
        Some(result)
    }

    /// Kills the in-flight subprocess (if any), joins its worker and drops any
    /// pending result.
    pub fn cancel(&mut self) {
        let Some(job) = self.job.take() else {
            return;
        };
        kill_child(&job.child);
        if let Some(thread) = job.thread {
            let _ = thread.join();
        }
    }
}

impl Default for FinderNet {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for FinderNet {
    fn drop(&mut self) {
        self.cancel();
    }
}

fn lock_child(child: &Arc<Mutex<Option<Child>>>) -> std::sync::MutexGuard<'_, Option<Child>> {
    child
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn kill_child(child: &Arc<Mutex<Option<Child>>>) {
    let taken = { lock_child(child).take() };
    if let Some(mut child) = taken {
        let _ = child.kill();
        let _ = child.wait();
    }
}

/// Waits for the child without holding its mutex while blocked. `cancel` must
/// be able to take and kill the child even when a worker is waiting on it.
fn reap_child(child: &Arc<Mutex<Option<Child>>>) -> Option<ExitStatus> {
    loop {
        let state = {
            let mut guard = lock_child(child);
            match guard.as_mut() {
                Some(process) => process.try_wait(),
                None => return None,
            }
        };
        match state {
            Ok(Some(_)) => {
                let taken = { lock_child(child).take() };
                return taken.and_then(|mut process| process.wait().ok());
            }
            Ok(None) => thread::sleep(WORKER_POLL),
            Err(_) => {
                let _ = { lock_child(child).take() };
                return None;
            }
        }
    }
}

fn read_bounded<R: Read>(mut reader: R) -> (Vec<u8>, bool) {
    let mut bytes = Vec::new();
    let ok = reader
        .take(RESPONSE_LIMIT as u64 + 1)
        .read_to_end(&mut bytes)
        .is_ok();
    bytes.truncate(RESPONSE_LIMIT);
    (bytes, ok)
}

fn bound_utf8(text: &str, limit: usize) -> String {
    if text.len() <= limit {
        return text.to_string();
    }
    let mut end = limit;
    while end > 0 && !text.is_char_boundary(end) {
        end -= 1;
    }
    text[..end].to_string()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rect {
    x: i32,
    y: i32,
    w: u32,
    h: u32,
}

fn rect_from_points(x0: i32, y0: i32, x1: i32, y1: i32, max_w: i32, max_h: i32) -> Rect {
    let left = x0.min(x1).max(0).min(max_w);
    let right = x0.max(x1).max(0).min(max_w);
    let top = y0.min(y1).max(0).min(max_h);
    let bottom = y0.max(y1).max(0).min(max_h);
    Rect {
        x: left,
        y: top,
        w: (right - left) as u32,
        h: (bottom - top) as u32,
    }
}

struct SelectionGuard {
    dpy: *mut xlib::Display,
    cursor: xlib::Cursor,
    gc: xlib::GC,
}

impl Drop for SelectionGuard {
    fn drop(&mut self) {
        unsafe {
            xlib::XUngrabPointer(self.dpy, xlib::CurrentTime);
            if !self.gc.is_null() {
                xlib::XFreeGC(self.dpy, self.gc);
            }
            if self.cursor != 0 {
                xlib::XFreeCursor(self.dpy, self.cursor);
            }
            xlib::XFlush(self.dpy);
        }
    }
}

fn next_event(dpy: *mut xlib::Display, deadline: Instant) -> Result<xlib::XEvent, String> {
    loop {
        unsafe {
            if xlib::XPending(dpy) > 0 {
                let mut event: xlib::XEvent = mem::zeroed();
                xlib::XNextEvent(dpy, &mut event);
                return Ok(event);
            }

            let remaining = deadline
                .saturating_duration_since(Instant::now())
                .as_millis();
            if remaining == 0 {
                return Err("OCR selection timed out".to_string());
            }
            let timeout = remaining.min(i32::MAX as u128) as i32;
            let mut pollfd = libc::pollfd {
                fd: xlib::XConnectionNumber(dpy),
                events: libc::POLLIN,
                revents: 0,
            };
            let ready = libc::poll(&mut pollfd, 1, timeout);
            if ready < 0 {
                let err = std::io::Error::last_os_error();
                if err.raw_os_error() == Some(libc::EINTR) {
                    continue;
                }
                return Err(format!("OCR selection failed: {err}"));
            }
        }
    }
}

unsafe fn draw_selection_rect(
    dpy: *mut xlib::Display,
    root: xlib::Window,
    gc: xlib::GC,
    rect: Option<Rect>,
) {
    unsafe {
        if let Some(rect) = rect {
            if rect.w != 0 && rect.h != 0 {
                xlib::XDrawRectangle(dpy, root, gc, rect.x, rect.y, rect.w, rect.h);
            }
        }
    }
}

unsafe fn select_region(dpy: *mut xlib::Display) -> Result<Rect, String> {
    unsafe {
        let root = xlib::XDefaultRootWindow(dpy);
        if root == 0 {
            return Err(OCR_ERROR.to_string());
        }

        let mut root_return: xlib::Window = 0;
        let mut x_return: c_int = 0;
        let mut y_return: c_int = 0;
        let mut width_return: c_uint = 0;
        let mut height_return: c_uint = 0;
        let mut border_return: c_uint = 0;
        let mut depth_return: c_uint = 0;
        if xlib::XGetGeometry(
            dpy,
            root,
            &mut root_return,
            &mut x_return,
            &mut y_return,
            &mut width_return,
            &mut height_return,
            &mut border_return,
            &mut depth_return,
        ) == 0
        {
            return Err(OCR_ERROR.to_string());
        }

        let cursor = xlib::XCreateFontCursor(dpy, XC_CROSSHAIR);
        if cursor == 0 {
            return Err("OCR unavailable (cursor creation failed)".to_string());
        }

        let mask = (xlib::ButtonPressMask
            | xlib::ButtonReleaseMask
            | xlib::PointerMotionMask
            | xlib::ButtonMotionMask) as c_uint;
        let grab = xlib::XGrabPointer(
            dpy,
            root,
            xlib::False,
            mask,
            xlib::GrabModeAsync,
            xlib::GrabModeAsync,
            0,
            cursor,
            xlib::CurrentTime,
        );
        if grab != xlib::GrabSuccess {
            unsafe {
                xlib::XFreeCursor(dpy, cursor);
                xlib::XFlush(dpy);
            }
            return Err("OCR unavailable (pointer grab failed)".to_string());
        }

        let gc = xlib::XCreateGC(dpy, root, 0, ptr::null_mut());
        if gc.is_null() {
            unsafe {
                xlib::XUngrabPointer(dpy, xlib::CurrentTime);
                xlib::XFreeCursor(dpy, cursor);
                xlib::XFlush(dpy);
            }
            return Err(OCR_ERROR.to_string());
        }

        unsafe {
            xlib::XSetFunction(dpy, gc, xlib::GXxor);
            xlib::XSetLineAttributes(dpy, gc, 1, xlib::LineSolid, xlib::CapButt, xlib::JoinMiter);
            xlib::XSetSubwindowMode(dpy, gc, xlib::IncludeInferiors);
            xlib::XSetGraphicsExposures(dpy, gc, xlib::False);
            xlib::XSetForeground(dpy, gc, xlib::XWhitePixel(dpy, xlib::XDefaultScreen(dpy)));
            xlib::XFlush(dpy);
        }

        let _guard = SelectionGuard { dpy, cursor, gc };
        let deadline = Instant::now() + SELECT_TIMEOUT;
        let mut origin: Option<(i32, i32)> = None;
        let mut drawn: Option<Rect> = None;

        loop {
            let event = next_event(dpy, deadline)?;
            match event.get_type() {
                xlib::ButtonPress => {
                    let (button, x, y) =
                        unsafe { (event.button.button, event.button.x, event.button.y) };
                    if button == xlib::Button1 && origin.is_none() {
                        origin = Some((x, y));
                    } else if button == xlib::Button3 {
                        return Err("OCR selection cancelled".to_string());
                    }
                }
                xlib::MotionNotify => {
                    if let Some((x0, y0)) = origin {
                        let (x, y) = unsafe { (event.motion.x, event.motion.y) };
                        let next = rect_from_points(
                            x0,
                            y0,
                            x,
                            y,
                            width_return as i32,
                            height_return as i32,
                        );
                        unsafe {
                            draw_selection_rect(dpy, root, gc, drawn);
                            draw_selection_rect(dpy, root, gc, Some(next));
                            xlib::XFlush(dpy);
                        }
                        drawn = Some(next);
                    }
                }
                xlib::ButtonRelease => {
                    let (button, x, y) =
                        unsafe { (event.button.button, event.button.x, event.button.y) };
                    if button == xlib::Button1 {
                        if let Some((x0, y0)) = origin.take() {
                            let rect = rect_from_points(
                                x0,
                                y0,
                                x,
                                y,
                                width_return as i32,
                                height_return as i32,
                            );
                            unsafe {
                                draw_selection_rect(dpy, root, gc, drawn);
                                xlib::XFlush(dpy);
                            }
                            drawn = None;
                            drop(_guard);
                            if rect.w < 2 || rect.h < 2 {
                                return Err("OCR selection cancelled".to_string());
                            }
                            return Ok(rect);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

fn masked_component(pixel: u64, mask: u64) -> u8 {
    if mask == 0 {
        return 0;
    }
    let shift = mask.trailing_zeros();
    let max = mask >> shift;
    if max == 0 {
        return 0;
    }
    let value = (pixel & mask) >> shift;
    let scaled = (value as u128 * 255 + (max as u128) / 2) / max as u128;
    scaled as u8
}

unsafe fn capture_region(dpy: *mut xlib::Display, rect: Rect) -> Result<Vec<u8>, String> {
    unsafe {
        if rect.w == 0 || rect.h == 0 {
            return Err(OCR_ERROR.to_string());
        }
        let needed = (rect.w as usize)
            .checked_mul(rect.h as usize)
            .and_then(|pixels| pixels.checked_mul(4))
            .ok_or_else(|| OCR_ERROR.to_string())?;
        if needed > MAX_CAPTURE_BYTES {
            return Err(OCR_ERROR.to_string());
        }

        let image = xlib::XGetImage(
            dpy,
            xlib::XDefaultRootWindow(dpy),
            rect.x,
            rect.y,
            rect.w,
            rect.h,
            xlib::XAllPlanes(),
            xlib::ZPixmap,
        );
        if image.is_null() || (*image).data.is_null() {
            if !image.is_null() {
                xlib::XDestroyImage(image);
            }
            return Err(OCR_ERROR.to_string());
        }

        let red_mask = (*image).red_mask as u64;
        let green_mask = (*image).green_mask as u64;
        let blue_mask = (*image).blue_mask as u64;
        let use_colormap = red_mask == 0 && green_mask == 0 && blue_mask == 0;
        let colormap = xlib::XDefaultColormap(dpy, xlib::XDefaultScreen(dpy));
        let mut palette: HashMap<u64, [u8; 3]> = HashMap::new();
        let mut out = RgbaImage::new(rect.w, rect.h);

        for y in 0..rect.h {
            for x in 0..rect.w {
                let pixel = xlib::XGetPixel(image, x as i32, y as i32) as u64;
                let rgb = if use_colormap {
                    if let Some(cached) = palette.get(&pixel) {
                        *cached
                    } else {
                        let mut color: xlib::XColor = mem::zeroed();
                        color.pixel = pixel as c_ulong;
                        let rgb = if xlib::XQueryColor(dpy, colormap, &mut color) == 0 {
                            [0, 0, 0]
                        } else {
                            [
                                (color.red >> 8) as u8,
                                (color.green >> 8) as u8,
                                (color.blue >> 8) as u8,
                            ]
                        };
                        palette.insert(pixel, rgb);
                        rgb
                    }
                } else {
                    [
                        masked_component(pixel, red_mask),
                        masked_component(pixel, green_mask),
                        masked_component(pixel, blue_mask),
                    ]
                };
                out.put_pixel(x, y, Rgba([rgb[0], rgb[1], rgb[2], 255]));
            }
        }
        xlib::XDestroyImage(image);

        let mut png = Vec::new();
        PngEncoder::new(&mut png)
            .write_image(
                out.as_raw(),
                out.width(),
                out.height(),
                ColorType::Rgba8.into(),
            )
            .map_err(|_| OCR_ERROR.to_string())?;
        Ok(png)
    }
}

fn skip_ws(input: &[u8], pos: &mut usize) {
    while *pos < input.len() && input[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn skip_ws_commas(input: &[u8], pos: &mut usize) {
    while *pos < input.len() && (input[*pos].is_ascii_whitespace() || input[*pos] == b',') {
        *pos += 1;
    }
}

fn push_bounded(out: &mut String, ch: char) {
    if out.len() + ch.len_utf8() <= RESULT_LIMIT {
        out.push(ch);
    }
}

fn append_bounded(out: &mut String, part: &str) {
    for ch in part.chars() {
        if out.len() + ch.len_utf8() > RESULT_LIMIT {
            break;
        }
        out.push(ch);
    }
}

fn utf8_len(first: u8) -> Option<usize> {
    match first {
        0x00..=0x7f => Some(1),
        0xc2..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf4 => Some(4),
        _ => None,
    }
}

fn parse_hex4(input: &[u8], pos: &mut usize) -> Option<u32> {
    let mut value = 0u32;
    for _ in 0..4 {
        let byte = *input.get(*pos)?;
        *pos += 1;
        value = value * 16 + (byte as char).to_digit(16)?;
    }
    Some(value)
}

fn parse_json_string(input: &[u8], start: usize) -> Option<(String, usize)> {
    if input.get(start) != Some(&b'"') {
        return None;
    }
    let mut pos = start + 1;
    let mut out = String::new();

    while pos < input.len() {
        let byte = input[pos];
        pos += 1;
        if byte == b'"' {
            return Some((out, pos));
        }
        if byte == b'\\' {
            let escape = *input.get(pos)?;
            pos += 1;
            match escape {
                b'"' | b'\\' | b'/' => push_bounded(&mut out, escape as char),
                b'b' => push_bounded(&mut out, '\u{0008}'),
                b'f' => push_bounded(&mut out, '\u{000c}'),
                b'n' => push_bounded(&mut out, '\n'),
                b'r' => push_bounded(&mut out, '\r'),
                b't' => push_bounded(&mut out, '\t'),
                b'u' => {
                    let mut cp = parse_hex4(input, &mut pos)?;
                    if (0xd800..=0xdbff).contains(&cp)
                        && input.get(pos) == Some(&b'\\')
                        && input.get(pos + 1) == Some(&b'u')
                    {
                        let saved = pos;
                        pos += 2;
                        let low = parse_hex4(input, &mut pos)?;
                        if (0xdc00..=0xdfff).contains(&low) {
                            cp = 0x10000 + ((cp - 0xd800) << 10) + (low - 0xdc00);
                        } else {
                            pos = saved;
                        }
                    }
                    push_bounded(&mut out, char::from_u32(cp)?);
                }
                _ => return None,
            }
        } else if byte < 0x80 {
            push_bounded(&mut out, byte as char);
        } else {
            let begin = pos - 1;
            let end = begin.checked_add(utf8_len(byte)?)?;
            let text = std::str::from_utf8(input.get(begin..end)?).ok()?;
            for ch in text.chars() {
                push_bounded(&mut out, ch);
            }
            pos = end;
        }
    }
    None
}

fn skip_json_value(input: &[u8], pos: &mut usize, depth: u8) -> Option<()> {
    if depth > JSON_DEPTH_LIMIT {
        return None;
    }
    skip_ws(input, pos);
    match *input.get(*pos)? {
        b'"' => {
            let (_, next) = parse_json_string(input, *pos)?;
            *pos = next;
            Some(())
        }
        b'[' | b'{' => {
            let close = if input[*pos] == b'[' { b']' } else { b'}' };
            *pos += 1;
            loop {
                skip_ws_commas(input, pos);
                while *pos < input.len() && input[*pos] == b':' {
                    *pos += 1;
                }
                skip_ws(input, pos);
                if *pos >= input.len() {
                    return None;
                }
                if input[*pos] == close {
                    *pos += 1;
                    return Some(());
                }
                skip_json_value(input, pos, depth + 1)?;
            }
        }
        _ => {
            let begin = *pos;
            while *pos < input.len()
                && !input[*pos].is_ascii_whitespace()
                && !matches!(input[*pos], b',' | b']' | b'}')
            {
                *pos += 1;
            }
            if *pos == begin { None } else { Some(()) }
        }
    }
}

/// Parses one JSON value and returns the first non-empty string found among
/// its *values* (never object keys), leaving `pos` just past the value. Used
/// to pull the translated text out of each part of a translation response
/// while ignoring the language-code, confidence and numeric fields.
fn first_string_value(input: &[u8], pos: &mut usize, depth: u8) -> Option<String> {
    if depth > JSON_DEPTH_LIMIT {
        return None;
    }
    skip_ws(input, pos);
    match *input.get(*pos)? {
        b'"' => {
            let (text, next) = parse_json_string(input, *pos)?;
            *pos = next;
            Some(text)
        }
        b'[' | b'{' => {
            let object = input[*pos] == b'{';
            let close = if object { b'}' } else { b']' };
            *pos += 1;
            let mut first: Option<String> = None;
            loop {
                skip_ws_commas(input, pos);
                if *pos >= input.len() {
                    return None;
                }
                if input[*pos] == close {
                    *pos += 1;
                    return Some(first.unwrap_or_default());
                }
                if object {
                    // Object keys are not translation text.
                    if input[*pos] != b'"' {
                        return None;
                    }
                    let (_, next) = parse_json_string(input, *pos)?;
                    *pos = next;
                    skip_ws(input, pos);
                    if input.get(*pos) != Some(&b':') {
                        return None;
                    }
                    *pos += 1;
                }
                let before = *pos;
                let value = first_string_value(input, pos, depth + 1).unwrap_or_default();
                if *pos == before {
                    return None;
                }
                if first.is_none() && !value.is_empty() {
                    first = Some(value);
                }
            }
        }
        _ => {
            let begin = *pos;
            while *pos < input.len()
                && !input[*pos].is_ascii_whitespace()
                && !matches!(input[*pos], b',' | b']' | b'}')
            {
                *pos += 1;
            }
            if *pos == begin {
                None
            } else {
                Some(String::new())
            }
        }
    }
}

/// Extracts the translated text from the Chrome endpoint's `[[text, source]]`
/// response, and also accepts dwm's older nested per-part arrays. The outer
/// array must contain arrays; each one contributes its first string value,
/// which is the translation, while language codes and other fields are
/// ignored.
fn parse_translation_response(input: &[u8]) -> Option<String> {
    let mut pos = 0;
    skip_ws(input, &mut pos);
    if input.get(pos) != Some(&b'[') {
        return None;
    }
    pos += 1;
    skip_ws(input, &mut pos);

    let mut out = String::new();
    loop {
        skip_ws_commas(input, &mut pos);
        if pos >= input.len() {
            return None;
        }
        if input[pos] == b']' {
            pos += 1;
            break;
        }
        if input[pos] != b'[' {
            return None;
        }
        let part = first_string_value(input, &mut pos, 0)?;
        append_bounded(&mut out, &part);
    }

    if out.is_empty() {
        None
    } else {
        Some(bound_utf8(&out, RESULT_LIMIT))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(text: &str) -> Option<String> {
        parse_translation_response(text.as_bytes())
    }

    #[test]
    fn parses_chrome_style_response() {
        assert_eq!(parse(r#"[["สวัสดี","hello"]]"#).as_deref(), Some("สวัสดี"));
        assert_eq!(parse("[[\"hello\",\"thai\"]]").as_deref(), Some("hello"));
    }

    #[test]
    fn parses_legacy_multi_part_response() {
        assert_eq!(
            parse(r#"[ [["Hel"],"en"], [["lo"],"en"] ]"#).as_deref(),
            Some("Hello")
        );
    }

    #[test]
    fn decodes_escapes_and_surrogate_pairs() {
        assert_eq!(
            parse(r#"[["A\n\u0E01\uD83D\uDE00\"B\""]]"#).as_deref(),
            Some("A\nก😀\"B\"")
        );
    }

    #[test]
    fn skips_non_string_values_in_legacy_parts() {
        let response = r#"[ [["Hi"],null,{"n":[1,2]},[2,3]] ]"#;
        assert_eq!(parse(response).as_deref(), Some("Hi"));
    }

    #[test]
    fn rejects_malformed_responses() {
        for response in [
            "",
            "{}",
            "[",
            r#"["only"]"#,
            r#"[[""]]"#,
            r#"[["bad\uZZZZ"]]"#,
            r#"[["unterminated]]"#,
        ] {
            assert!(
                parse(response).is_none(),
                "unexpectedly parsed {response:?}"
            );
        }
    }

    #[test]
    fn truncates_long_results_on_char_boundaries() {
        let text = "ก".repeat(1500);
        let response = format!("[[\"{text}\",\"th\"]]");
        let result = parse(&response).expect("long response should parse");
        assert!(result.len() <= RESULT_LIMIT);
        assert!(result.chars().all(|ch| ch == 'ก'));
    }

    #[test]
    fn rectangle_helper_clamps_to_screen() {
        assert_eq!(
            rect_from_points(-10, -5, 50, 30, 40, 20),
            Rect {
                x: 0,
                y: 0,
                w: 40,
                h: 20
            }
        );
        assert_eq!(
            rect_from_points(30, 25, 5, 10, 100, 100),
            Rect {
                x: 5,
                y: 10,
                w: 25,
                h: 15
            }
        );
    }

    #[test]
    fn masks_rgb_components() {
        assert_eq!(masked_component(0x00ff_0000, 0x00ff_0000), 255);
        assert_eq!(masked_component(0x0000_007f, 0x0000_00ff), 127);
        assert_eq!(masked_component(42, 0), 0);
    }
}
