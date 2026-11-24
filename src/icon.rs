//! Port of AnDWM's `geticonprop()`: read the focused window's `_NET_WM_ICON`
//! property, pick the best-sized frame and scale it into the bar's icon cell.
//!
//! The result is premultiplied ARGB32, the layout XRender expects for a
//! `PictStandardARGB32` picture. `drw` uploads it once per icon version and
//! composites it where the Arch logo used to be.

use image::imageops::FilterType;

/// One decoded icon, ready for `XPutImage`. `id` changes whenever the property
/// is reloaded so bar draw keys and cached XRender pictures become stale.
#[derive(Clone)]
pub struct ClientIcon {
    pub id: u64,
    pub width: u32,
    pub height: u32,
    /// Premultiplied `0xAARRGGBB` pixels, row-major.
    pub argb: Vec<u32>,
}

/// Decode a raw `_NET_WM_ICON` property (width, height, ARGB pixels, repeated)
/// into an icon that fits a `target`-pixel square, preserving aspect ratio.
///
/// AnDWM first looks for the smallest frame at least as large as `ICONSIZE`
/// and only falls back to the largest smaller one. Keeping that order avoids
/// blowing up a 16x16 icon to 21x21 when a 32x32 one is also available.
pub fn client_icon(data: &[u32], target: u32, id: u64) -> Option<ClientIcon> {
    let target = target.max(1) as usize;
    let mut frames: Vec<(usize, usize, usize, usize)> = Vec::new();
    let mut i = 0;
    while i + 2 <= data.len() {
        let w = data[i] as usize;
        let h = data[i + 1] as usize;
        if w == 0 || h == 0 || w >= 16384 || h >= 16384 {
            break;
        }
        let pixels = w.checked_mul(h)?;
        if i + 2 + pixels > data.len() {
            break;
        }
        frames.push((i + 2, w, h, w.max(h)));
        i += 2 + pixels;
    }

    let (start, w, h, _) = frames
        .iter()
        .copied()
        .filter(|&(_, _, _, max)| max >= target)
        .min_by_key(|&(_, _, _, max)| max - target)
        .or_else(|| {
            frames
                .iter()
                .copied()
                .min_by_key(|&(_, _, _, max)| target.saturating_sub(max))
        })?;

    let (dw, dh) = if w <= h {
        ((w * target / h).max(1), target)
    } else {
        (target, (h * target / w).max(1))
    };

    // X11 sends ARGB. Convert to RGBA for `image`'s scaler, then premultiply
    // after scaling so transparent edges do not bleed dark fringes.
    let rgba: Vec<u8> = data[start..start + w * h]
        .iter()
        .flat_map(|&px| {
            [
                (px >> 16) as u8,
                (px >> 8) as u8,
                px as u8,
                (px >> 24) as u8,
            ]
        })
        .collect();
    let source = image::RgbaImage::from_raw(w as u32, h as u32, rgba)?;
    let scaled = if w == dw && h == dh {
        source
    } else {
        image::imageops::resize(&source, dw as u32, dh as u32, FilterType::Lanczos3)
    };
    let argb = scaled
        .pixels()
        .map(|p| {
            let a = p.0[3] as u32;
            let r = p.0[0] as u32 * a / 255;
            let g = p.0[1] as u32 * a / 255;
            let b = p.0[2] as u32 * a / 255;
            a << 24 | r << 16 | g << 8 | b
        })
        .collect();

    Some(ClientIcon {
        id,
        width: dw as u32,
        height: dh as u32,
        argb,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefers_the_closest_icon_at_least_the_target_size() {
        // A 16x16 and a 64x64 frame for a 19px cell: 64 is closer than
        // falling back to the smaller one, just like AnDWM's first pass.
        let mut data = vec![16, 16];
        data.extend(std::iter::repeat(0xff00ff00u32).take(16 * 16));
        data.extend([64, 64]);
        data.extend(std::iter::repeat(0xffff0000u32).take(64 * 64));
        let icon = client_icon(&data, 19, 7).unwrap();
        assert_eq!((icon.width, icon.height), (19, 19));
        assert_eq!(icon.id, 7);
        assert_eq!(icon.argb.len(), 19 * 19);
        assert_eq!(icon.argb[0] & 0x00ff_ffff, 0x00ff_0000);
    }

    #[test]
    fn keeps_aspect_ratio_and_premultiplies_alpha() {
        // 40x20 scales to 19x9 in a 19px cell.
        let mut data = vec![40, 20];
        data.extend(std::iter::repeat(0x80112233u32).take(40 * 20));
        let icon = client_icon(&data, 19, 1).unwrap();
        assert_eq!((icon.width, icon.height), (19, 9));
        let p = icon.argb[0];
        assert_eq!(p >> 24, 0x80);
        // 0x11/0x22/0x33 at 50% alpha round down in premultiplication.
        assert_eq!(p & 0x00ff_ffff, 0x0008_1119);
    }
}
