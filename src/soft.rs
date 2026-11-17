//! CPU drawing for the clock bar. It produces the same steps as the GL text
//! path, into a pixel buffer that is sent to the window with `PutImage`.

use crate::bar::{BORDERPX, CLOCKPAD, CLRBORDER, Metrics, Scheme, VERTPADBAR, col, scheme_norm, scheme_title};
use crate::text::Op;

/// Pixels of one 32-bit ZPixmap, 0xAARRGGBB each.
pub struct Canvas {
    pub w: usize,
    pub h: usize,
    px: Vec<u32>,
}

/// The 0xAARRGGBB pixel for an opaque color.
fn pixel(c: [f32; 4]) -> u32 {
    let ch = |v: f32| (v * 255.0).round() as u32;
    0xFF00_0000 | ch(c[0]) << 16 | ch(c[1]) << 8 | ch(c[2])
}

impl Canvas {
    pub fn new(w: usize, h: usize, clear: u32) -> Canvas {
        Canvas { w, h, px: vec![clear; w * h] }
    }

    /// The area of a rectangle that lies inside the canvas, as `(x0, y0, x1, y1)`.
    fn clip(&self, x: i32, y: i32, w: i32, h: i32) -> Option<(usize, usize, usize, usize)> {
        let x0 = x.clamp(0, self.w as i32) as usize;
        let y0 = y.clamp(0, self.h as i32) as usize;
        let x1 = (x + w).clamp(0, self.w as i32) as usize;
        let y1 = (y + h).clamp(0, self.h as i32) as usize;
        (x0 < x1 && y0 < y1).then_some((x0, y0, x1, y1))
    }

    /// dwm's `drw_rect` with filled = 1.
    pub fn fill(&mut self, x: i32, y: i32, w: i32, h: i32, color: u32) {
        let Some((x0, y0, x1, y1)) = self.clip(x, y, w, h) else {
            return;
        };
        for row in y0..y1 {
            self.px[row * self.w + x0..row * self.w + x1].fill(color);
        }
    }

    /// Blends `color` over the canvas by the coverage bytes of a `tw` x `th` run.
    fn blend(&mut self, x: i32, y: i32, tw: usize, th: usize, cov: &[u8], color: u32) {
        let Some((x0, y0, x1, y1)) = self.clip(x, y, tw as i32, th as i32) else {
            return;
        };
        let fg = [(color >> 16) & 0xff, (color >> 8) & 0xff, color & 0xff];
        for py in y0..y1 {
            for px in x0..x1 {
                let a = cov[(py as i32 - y) as usize * tw + (px as i32 - x) as usize] as u32;
                if a == 0 {
                    continue;
                }
                let dst = &mut self.px[py * self.w + px];
                let d = [(*dst >> 16) & 0xff, (*dst >> 8) & 0xff, *dst & 0xff];
                let mix = |i: usize| (fg[i] * a + d[i] * (255 - a)) / 255;
                *dst = 0xFF00_0000 | mix(0) << 16 | mix(1) << 8 | mix(2);
            }
        }
    }

    /// dwm's `drw_text`, drawn the same way as `Gl::text`.
    pub fn text(&mut self, m: &Metrics, x: i32, y: i32, w: i32, h: i32, lpad: i32, text: &str, s: Scheme) {
        for op in m.text_ops(x, y, w, h, lpad, text) {
            match op {
                Op::Fill { x, y, w, h } => self.fill(x, y, w as i32, h as i32, pixel(s.bg)),
                Op::Text { font, x, baseline, text } => {
                    let Some((cov, tw, th)) = m.raster(font, &text) else {
                        continue;
                    };
                    let top = baseline - m.ascent(font);
                    self.blend(x, top, tw, th, &cov, pixel(s.fg));
                }
            }
        }
    }

    /// The pixels in the byte order of a little-endian 32-bit ZPixmap.
    pub fn into_bytes(self) -> Vec<u8> {
        self.px.iter().flat_map(|p| p.to_le_bytes()).collect()
    }
}

/// Clock section of dwm's `drawbar()`, the same drawing as the GL version.
pub fn clock(m: &Metrics, w: i32, clock: &str, focused: bool) -> Canvas {
    let bh = m.bar_height();
    let bh_n = bh - BORDERPX * 2;
    let tcw = m.text_width(clock) + 2 * CLOCKPAD;
    let x = if w > tcw { (w - tcw) / 2 } else { 0 };
    let scheme = if focused { scheme_title() } else { scheme_norm() };
    let mut canvas = Canvas::new(w.max(1) as usize, bh.max(1) as usize, pixel(col(CLRBORDER)));
    canvas.fill(0, BORDERPX, w, bh_n, pixel(scheme.bg));
    canvas.text(m, x, BORDERPX + VERTPADBAR / 2, tcw, bh - VERTPADBAR, CLOCKPAD, clock, scheme);
    canvas
}
