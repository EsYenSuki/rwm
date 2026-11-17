use std::collections::HashSet;

use x11rb::protocol::xproto::Window;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rect {
    pub x: i32,
    pub y: i32,
    pub w: u32,
    pub h: u32,
}

impl Rect {
    pub fn contains(&self, px: i32, py: i32) -> bool {
        px >= self.x
            && py >= self.y
            && px < self.x + self.w as i32
            && py < self.y + self.h as i32
    }

    /// Splits the rect with `gap` pixels between the halves. The first half
    /// gets `ratio` of the space.
    pub fn split(self, side_by_side: bool, gap: i32, ratio: f64) -> (Rect, Rect) {
        let gap = gap.max(0);
        if side_by_side {
            let total = (self.w as i32 - gap).max(0);
            let w1 = first_len(total, ratio);
            (
                Rect { w: w1 as u32, ..self },
                Rect { x: self.x + w1 + gap, w: (total - w1) as u32, ..self },
            )
        } else {
            let total = (self.h as i32 - gap).max(0);
            let h1 = first_len(total, ratio);
            (
                Rect { h: h1 as u32, ..self },
                Rect { y: self.y + h1 + gap, h: (total - h1) as u32, ..self },
            )
        }
    }
}

/// The first half's length out of `total` pixels at `ratio`, rounded down.
fn first_len(total: i32, ratio: f64) -> i32 {
    ((total as f64 * ratio) + 1e-6).floor().clamp(0.0, total as f64) as i32
}

/// dwm's `gappoh`, `gappov`, `gappih` and `gappiv` after the enable switch.
/// `oh` and `ov` are the outer margins, `ih` the gap between stacked windows
/// and `iv` the gap between side-by-side windows.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gaps {
    pub oh: i32,
    pub ov: i32,
    pub ih: i32,
    pub iv: i32,
}

/// The edges a resize drag from `(px, py)` moves, as `(left, right, top, bottom)`.
/// The press picks a side per axis when it is in that side's outer third, so
/// an edge's middle moves one edge and a corner moves two. A press in the
/// middle of both axes moves only the nearest edge.
pub fn resize_edges(rect: Rect, (px, py): (i32, i32)) -> (bool, bool, bool, bool) {
    let third_w = rect.w as i32 / 3;
    let third_h = rect.h as i32 / 3;
    let left = px < rect.x + third_w;
    let right = px >= rect.x + rect.w as i32 - third_w;
    let top = py < rect.y + third_h;
    let bottom = py >= rect.y + rect.h as i32 - third_h;
    if !(left || right || top || bottom) {
        let dists = [
            (px - rect.x, 0),
            (rect.x + rect.w as i32 - px, 1),
            (py - rect.y, 2),
            (rect.y + rect.h as i32 - py, 3),
        ];
        let nearest = dists.iter().min_by_key(|(d, _)| *d).map_or(0, |(_, i)| *i);
        return (nearest == 0, nearest == 1, nearest == 2, nearest == 3);
    }
    (left, right, top, bottom)
}

/// The edges each hover zone of `edge_zones` stands for, as
/// `(left, right, top, bottom)`, in the same order.
pub const ZONE_EDGES: [(bool, bool, bool, bool); 8] = [
    (true, false, false, false),
    (false, true, false, false),
    (false, false, true, false),
    (false, false, false, true),
    (true, false, true, false),
    (false, true, true, false),
    (true, false, false, true),
    (false, true, false, true),
];

/// The hover zones along the edges of `rect`, `band` pixels deep: left, right,
/// top and bottom, then the four corner squares. Corners do not overlap the
/// side zones.
pub fn edge_zones(rect: Rect, band: i32) -> [Rect; 8] {
    let (x, y) = (rect.x, rect.y);
    let (w, h) = (rect.w as i32, rect.h as i32);
    let b = band.clamp(1, (w.min(h) / 2).max(1));
    let side_h = (h - 2 * b).max(0) as u32;
    let mid_w = (w - 2 * b).max(0) as u32;
    let (rx, by) = (x + w - b, y + h - b);
    let (b, bu) = (b, b as u32);
    [
        Rect { x, y: y + b, w: bu, h: side_h },
        Rect { x: rx, y: y + b, w: bu, h: side_h },
        Rect { x: x + b, y, w: mid_w, h: bu },
        Rect { x: x + b, y: by, w: mid_w, h: bu },
        Rect { x, y, w: bu, h: bu },
        Rect { x: rx, y, w: bu, h: bu },
        Rect { x, y: by, w: bu, h: bu },
        Rect { x: rx, y: by, w: bu, h: bu },
    ]
}

/// Moves the chosen edges of `rect` by the drag offset `(dx, dy)`. The opposite
/// edges stay put, and a size never drops below one pixel.
pub fn resize_rect(
    rect: Rect,
    (left, right, top, bottom): (bool, bool, bool, bool),
    (dx, dy): (i32, i32),
) -> Rect {
    let mut r = rect;
    if left {
        let w = (rect.w as i32 - dx).max(1);
        r.x = rect.x + rect.w as i32 - w;
        r.w = w as u32;
    }
    if right {
        r.w = (rect.w as i32 + dx).max(1) as u32;
    }
    if top {
        let h = (rect.h as i32 - dy).max(1);
        r.y = rect.y + rect.h as i32 - h;
        r.h = h as u32;
    }
    if bottom {
        r.h = (rect.h as i32 + dy).max(1) as u32;
    }
    r
}

/// The area inside the outer margins of `rect`.
pub fn inset(rect: Rect, gaps: &Gaps) -> Rect {
    Rect {
        x: rect.x + gaps.ov,
        y: rect.y + gaps.oh,
        w: (rect.w as i32 - 2 * gaps.ov).max(0) as u32,
        h: (rect.h as i32 - 2 * gaps.oh).max(0) as u32,
    }
}

/// Binary split tree. Leaves that are not in `vis` take no space, so a hidden
/// window's sibling gets the whole parent area.
pub enum Node {
    Leaf(Window),
    Split {
        side_by_side: bool,
        ratio: f64,
        first: Box<Node>,
        second: Box<Node>,
    },
}

impl Node {
    pub fn any_visible(&self, vis: &HashSet<Window>) -> bool {
        match self {
            Node::Leaf(w) => vis.contains(w),
            Node::Split { first, second, .. } => {
                first.any_visible(vis) || second.any_visible(vis)
            }
        }
    }

    pub fn has_leaf(&self, win: Window) -> bool {
        match self {
            Node::Leaf(w) => *w == win,
            Node::Split { first, second, .. } => first.has_leaf(win) || second.has_leaf(win),
        }
    }

    /// Moves the split boundaries next to `win` on the chosen sides by the
    /// drag `(dx, dy)`. `want` is `(left, right, top, bottom)`. A boundary is
    /// only moved when the window touches it, and the deepest split wins, so
    /// the boundary nearest each chosen side is the one that moves.
    fn resize_boundaries(
        &mut self,
        rect: Rect,
        vis: &HashSet<Window>,
        gaps: &Gaps,
        win: Window,
        want: &mut (bool, bool, bool, bool),
        (dx, dy): (i32, i32),
    ) {
        match self {
            Node::Leaf(_) => {}
            Node::Split { side_by_side, ratio, first, second } => {
                let (fv, sv) = (first.any_visible(vis), second.any_visible(vis));
                if !(fv && sv) {
                    if fv {
                        first.resize_boundaries(rect, vis, gaps, win, want, (dx, dy));
                    } else if sv {
                        second.resize_boundaries(rect, vis, gaps, win, want, (dx, dy));
                    }
                    return;
                }
                let gap = if *side_by_side { gaps.iv } else { gaps.ih };
                let (a, b) = rect.split(*side_by_side, gap, *ratio);
                let in_first = first.has_leaf(win);
                if in_first {
                    first.resize_boundaries(a, vis, gaps, win, want, (dx, dy));
                } else {
                    second.resize_boundaries(b, vis, gaps, win, want, (dx, dy));
                }
                let side = match (*side_by_side, in_first) {
                    (true, true) => &mut want.1,
                    (true, false) => &mut want.0,
                    (false, true) => &mut want.3,
                    (false, false) => &mut want.2,
                };
                if !*side {
                    return;
                }
                *side = false;
                let total = if *side_by_side { rect.w as i32 - gap } else { rect.h as i32 - gap }.max(0);
                if total < 2 {
                    return;
                }
                let step = if *side_by_side { dx } else { dy };
                let len = first_len(total, *ratio) + step;
                *ratio = len.clamp(1, total - 1) as f64 / total as f64;
            }
        }
    }

    pub fn layout(
        &self,
        rect: Rect,
        vis: &HashSet<Window>,
        gaps: &Gaps,
        out: &mut Vec<(Window, Rect)>,
    ) {
        match self {
            Node::Leaf(win) => {
                if vis.contains(win) {
                    out.push((*win, rect));
                }
            }
            Node::Split { side_by_side, ratio, first, second } => {
                match (first.any_visible(vis), second.any_visible(vis)) {
                    (true, true) => {
                        let gap = if *side_by_side { gaps.iv } else { gaps.ih };
                        let (a, b) = rect.split(*side_by_side, gap, *ratio);
                        first.layout(a, vis, gaps, out);
                        second.layout(b, vis, gaps, out);
                    }
                    (true, false) => first.layout(rect, vis, gaps, out),
                    (false, true) => second.layout(rect, vis, gaps, out),
                    (false, false) => {}
                }
            }
        }
    }

    /// Swaps the positions of two leaves.
    pub fn swap(&mut self, a: Window, b: Window) {
        match self {
            Node::Leaf(w) if *w == a => *w = b,
            Node::Leaf(w) if *w == b => *w = a,
            Node::Leaf(_) => {}
            Node::Split { first, second, .. } => {
                first.swap(a, b);
                second.swap(a, b);
            }
        }
    }

    /// Replaces the leaf `target` with a split holding `target` and `new`.
    pub fn insert(&mut self, target: Window, new: Window, new_first: bool, side_by_side: bool) -> bool {
        if let Node::Split { first, second, .. } = self {
            return first.insert(target, new, new_first, side_by_side)
                || second.insert(target, new, new_first, side_by_side);
        }
        let Node::Leaf(w) = *self else { return false };
        if w != target {
            return false;
        }
        let (first, second) = if new_first {
            (Node::Leaf(new), Node::Leaf(w))
        } else {
            (Node::Leaf(w), Node::Leaf(new))
        };
        *self = Node::Split {
            side_by_side,
            ratio: 0.5,
            first: Box::new(first),
            second: Box::new(second),
        };
        true
    }

    /// Removes the leaf `target`; its sibling takes over the parent area.
    pub fn remove(self, target: Window) -> Option<Node> {
        match self {
            Node::Leaf(w) => (w != target).then_some(Node::Leaf(w)),
            Node::Split { side_by_side, ratio, first, second } => {
                match ((*first).remove(target), (*second).remove(target)) {
                    (Some(a), Some(b)) => Some(Node::Split {
                        side_by_side,
                        ratio,
                        first: Box::new(a),
                        second: Box::new(b),
                    }),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                }
            }
        }
    }
}

/// Resizes tiled `win` by moving the boundaries on its chosen `edges` by the
/// drag `(dx, dy)`. `rect` is the area of the whole tree.
pub fn resize_tiled(
    node: &mut Node,
    rect: Rect,
    vis: &HashSet<Window>,
    gaps: &Gaps,
    win: Window,
    edges: (bool, bool, bool, bool),
    delta: (i32, i32),
) {
    let mut want = edges;
    node.resize_boundaries(rect, vis, gaps, win, &mut want, delta);
}

/// Adds `new` beside the whole tree, splitting along the long side of `area`.
pub fn append(tree: Option<Node>, new: Window, area: Rect) -> Node {
    match tree {
        None => Node::Leaf(new),
        Some(old) => Node::Split {
            side_by_side: area.w > area.h,
            ratio: 0.5,
            first: Box::new(old),
            second: Box::new(Node::Leaf(new)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn layout_all(node: &Node, rect: Rect) -> Vec<(Window, Rect)> {
        let mut vis = HashSet::new();
        collect_leaves(node, &mut vis);
        let mut out = Vec::new();
        node.layout(rect, &vis, &Gaps::default(), &mut out);
        out
    }

    fn collect_leaves(node: &Node, vis: &mut HashSet<Window>) {
        match node {
            Node::Leaf(w) => {
                vis.insert(*w);
            }
            Node::Split { first, second, .. } => {
                collect_leaves(first, vis);
                collect_leaves(second, vis);
            }
        }
    }

    #[test]
    fn test_hyprland_cursor_spawn_scenario() {
        let screen = Rect { x: 0, y: 0, w: 1920, h: 1080 };

        // 1. First window: fills entire workspace
        let mut tree: Option<Node> = None;
        let w1: Window = 101;
        tree = Some(append(tree, w1, screen));

        let l1 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l1.len(), 1);
        assert_eq!(l1[0], (w1, Rect { x: 0, y: 0, w: 1920, h: 1080 }));

        // 2. Second window: mouse in left side of w1 (e.g. mx=200, my=500)
        let w2: Window = 102;
        let mx = 200;
        let my = 500;
        let leaves = layout_all(tree.as_ref().unwrap(), screen);
        let (target, rect) = leaves.into_iter().find(|(_, r)| r.contains(mx, my)).unwrap();
        assert_eq!(target, w1);

        let side_by_side = rect.w > rect.h; // 1920 > 1080 -> true
        assert!(side_by_side);
        let new_first = mx < rect.x + (rect.w / 2) as i32; // 200 < 960 -> true (left side)
        assert!(new_first);

        tree.as_mut().unwrap().insert(target, w2, new_first, side_by_side);

        let l2 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l2.len(), 2);
        // w2 takes the left half, w1 takes the right half
        assert_eq!(l2[0], (w2, Rect { x: 0, y: 0, w: 960, h: 1080 }));
        assert_eq!(l2[1], (w1, Rect { x: 960, y: 0, w: 960, h: 1080 }));

        // 3. Third window: mouse in top half of w2 (e.g. mx=200, my=200)
        let w3: Window = 103;
        let mx = 200;
        let my = 200;
        let leaves = layout_all(tree.as_ref().unwrap(), screen);
        let (target, rect) = leaves.into_iter().find(|(_, r)| r.contains(mx, my)).unwrap();
        assert_eq!(target, w2);
        assert_eq!(rect, Rect { x: 0, y: 0, w: 960, h: 1080 });

        let side_by_side = rect.w > rect.h; // 960 > 1080 -> false (height more than width)
        assert!(!side_by_side);
        let new_first = my < rect.y + (rect.h / 2) as i32; // 200 < 540 -> true (top half)
        assert!(new_first);

        tree.as_mut().unwrap().insert(target, w3, new_first, side_by_side);

        let l3 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l3.len(), 3);
        // w3 takes top-left, w2 takes bottom-left, w1 takes right half
        assert_eq!(l3[0], (w3, Rect { x: 0, y: 0, w: 960, h: 540 }));
        assert_eq!(l3[1], (w2, Rect { x: 0, y: 540, w: 960, h: 540 }));
        assert_eq!(l3[2], (w1, Rect { x: 960, y: 0, w: 960, h: 1080 }));

        // 4. Fourth window: mouse in bottom half of w1 (e.g. mx=1400, my=800)
        let w4: Window = 104;
        let mx = 1400;
        let my = 800;
        let leaves = layout_all(tree.as_ref().unwrap(), screen);
        let (target, rect) = leaves.into_iter().find(|(_, r)| r.contains(mx, my)).unwrap();
        assert_eq!(target, w1);
        assert_eq!(rect, Rect { x: 960, y: 0, w: 960, h: 1080 });

        let side_by_side = rect.w > rect.h; // 960 > 1080 -> false
        assert!(!side_by_side);
        let new_first = my < rect.y + (rect.h / 2) as i32; // 800 < 540 -> false (bottom half)
        assert!(!new_first);

        tree.as_mut().unwrap().insert(target, w4, new_first, side_by_side);

        let l4 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l4.len(), 4);
        assert_eq!(l4[0], (w3, Rect { x: 0, y: 0, w: 960, h: 540 }));
        assert_eq!(l4[1], (w2, Rect { x: 0, y: 540, w: 960, h: 540 }));
        assert_eq!(l4[2], (w1, Rect { x: 960, y: 0, w: 960, h: 540 }));
        assert_eq!(l4[3], (w4, Rect { x: 960, y: 540, w: 960, h: 540 }));

        // 5. Test removal: remove w3 -> w2 expands to fill left half
        tree = tree.unwrap().remove(w3);
        let l5 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l5.len(), 3);
        assert_eq!(l5[0], (w2, Rect { x: 0, y: 0, w: 960, h: 1080 }));
        assert_eq!(l5[1], (w1, Rect { x: 960, y: 0, w: 960, h: 540 }));
        assert_eq!(l5[2], (w4, Rect { x: 960, y: 540, w: 960, h: 540 }));

        // Remove w4 -> w1 expands to fill right half
        tree = tree.unwrap().remove(w4);
        let l6 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l6.len(), 2);
        assert_eq!(l6[0], (w2, Rect { x: 0, y: 0, w: 960, h: 1080 }));
        assert_eq!(l6[1], (w1, Rect { x: 960, y: 0, w: 960, h: 1080 }));

        // Remove w2 -> w1 fills entire workspace
        tree = tree.unwrap().remove(w2);
        let l7 = layout_all(tree.as_ref().unwrap(), screen);
        assert_eq!(l7.len(), 1);
        assert_eq!(l7[0], (w1, Rect { x: 0, y: 0, w: 1920, h: 1080 }));

        // Remove w1 -> tree is empty
        tree = tree.unwrap().remove(w1);
        assert!(tree.is_none());
    }

    #[test]
    fn test_visibility_filtering() {
        let screen = Rect { x: 0, y: 0, w: 1920, h: 1080 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);

        // Both visible
        let mut vis = HashSet::new();
        vis.insert(1);
        vis.insert(2);
        let none = Gaps::default();
        let mut out = Vec::new();
        tree.layout(screen, &vis, &none, &mut out);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].1, Rect { x: 0, y: 0, w: 960, h: 1080 });
        assert_eq!(out[1].1, Rect { x: 960, y: 0, w: 960, h: 1080 });

        // Only 1 visible -> gets whole screen
        let mut vis1 = HashSet::new();
        vis1.insert(1);
        let mut out1 = Vec::new();
        tree.layout(screen, &vis1, &none, &mut out1);
        assert_eq!(out1.len(), 1);
        assert_eq!(out1[0], (1, screen));

        // Only 2 visible -> gets whole screen
        let mut vis2 = HashSet::new();
        vis2.insert(2);
        let mut out2 = Vec::new();
        tree.layout(screen, &vis2, &none, &mut out2);
        assert_eq!(out2.len(), 1);
        assert_eq!(out2[0], (2, screen));
    }

    #[test]
    fn test_inner_gaps_between_split_windows() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);
        tree.insert(2, 3, false, false);

        let gaps = Gaps { oh: 0, ov: 0, ih: 20, iv: 10 };
        let vis: HashSet<Window> = [1, 2, 3].into_iter().collect();
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);

        // Left column takes the left half; the 10px iv gap sits between columns.
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 495, h: 500 }));
        // Right column is split top and bottom with the 20px ih gap between.
        assert_eq!(out[1], (2, Rect { x: 505, y: 0, w: 495, h: 240 }));
        assert_eq!(out[2], (3, Rect { x: 505, y: 260, w: 495, h: 240 }));
    }

    #[test]
    fn test_inset_outer_gaps() {
        let screen = Rect { x: 100, y: 50, w: 1000, h: 500 };
        let gaps = Gaps { oh: 14, ov: 20, ih: 0, iv: 0 };
        assert_eq!(inset(screen, &gaps), Rect { x: 120, y: 64, w: 960, h: 472 });
    }

    #[test]
    fn test_resize_edges_follow_press_zone() {
        let r = Rect { x: 0, y: 0, w: 300, h: 300 };
        assert_eq!(resize_edges(r, (290, 10)), (false, true, true, false));
        assert_eq!(resize_edges(r, (5, 150)), (true, false, false, false));
        assert_eq!(resize_edges(r, (150, 295)), (false, false, false, true));
        assert_eq!(resize_edges(r, (10, 290)), (true, false, false, true));
        assert_eq!(resize_edges(r, (150, 150)), (true, false, false, false));
        assert_eq!(resize_edges(r, (150, 110)), (false, false, true, false));
        assert_eq!(resize_edges(r, (200, 150)), (false, true, false, false));
    }

    #[test]
    fn test_edge_zones_cover_border_without_overlap() {
        let r = Rect { x: 10, y: 20, w: 300, h: 200 };
        let z = edge_zones(r, 6);
        assert_eq!(z[0], Rect { x: 10, y: 26, w: 6, h: 188 });
        assert_eq!(z[1], Rect { x: 304, y: 26, w: 6, h: 188 });
        assert_eq!(z[2], Rect { x: 16, y: 20, w: 288, h: 6 });
        assert_eq!(z[3], Rect { x: 16, y: 214, w: 288, h: 6 });
        assert_eq!(z[4], Rect { x: 10, y: 20, w: 6, h: 6 });
        assert_eq!(z[7], Rect { x: 304, y: 214, w: 6, h: 6 });
        assert!(z[0].contains(10, 100) && !z[0].contains(16, 100));
    }

    #[test]
    fn test_resize_rect_moves_only_chosen_edges() {
        let r = Rect { x: 0, y: 0, w: 300, h: 300 };
        let top_right = resize_edges(r, (290, 10));
        assert_eq!(
            resize_rect(r, top_right, (20, 30)),
            Rect { x: 0, y: 30, w: 320, h: 270 }
        );
        let left = resize_edges(r, (5, 150));
        assert_eq!(
            resize_rect(r, left, (-10, 40)),
            Rect { x: -10, y: 0, w: 310, h: 300 }
        );
        let bottom = resize_edges(r, (150, 295));
        assert_eq!(
            resize_rect(r, bottom, (50, 20)),
            Rect { x: 0, y: 0, w: 300, h: 320 }
        );
    }

    #[test]
    fn test_resize_tiled_two_windows_share_one_edge() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);
        let vis: HashSet<Window> = [1, 2].into_iter().collect();
        let gaps = Gaps::default();

        let right_of_left = (false, true, false, false);
        resize_tiled(&mut tree, screen, &vis, &gaps, 1, right_of_left, (50, 0));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 550, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 550, y: 0, w: 450, h: 500 }));

        let left_of_right = (true, false, false, false);
        resize_tiled(&mut tree, screen, &vis, &gaps, 2, left_of_right, (-100, 0));
        out.clear();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 450, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 450, y: 0, w: 550, h: 500 }));
    }

    #[test]
    fn test_resize_tiled_three_windows_moves_nearest_boundary() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);
        tree.insert(2, 3, false, false);
        let vis: HashSet<Window> = [1, 2, 3].into_iter().collect();
        let gaps = Gaps::default();

        let bottom_of_top_right = (false, false, false, true);
        resize_tiled(&mut tree, screen, &vis, &gaps, 2, bottom_of_top_right, (0, 60));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 500, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 500, y: 0, w: 500, h: 310 }));
        assert_eq!(out[2], (3, Rect { x: 500, y: 310, w: 500, h: 190 }));

        let right_of_left = (false, true, false, false);
        resize_tiled(&mut tree, screen, &vis, &gaps, 1, right_of_left, (-200, 0));
        out.clear();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 300, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 300, y: 0, w: 700, h: 310 }));
        assert_eq!(out[2], (3, Rect { x: 300, y: 310, w: 700, h: 190 }));
    }

    #[test]
    fn test_resize_tiled_screen_edge_is_a_no_op() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);
        let vis: HashSet<Window> = [1, 2].into_iter().collect();
        let gaps = Gaps::default();
        resize_tiled(&mut tree, screen, &vis, &gaps, 2, (false, true, false, false), (80, 0));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 500, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 500, y: 0, w: 500, h: 500 }));
    }

    #[test]
    fn test_resize_tiled_keeps_one_pixel_minimum() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true);
        let vis: HashSet<Window> = [1, 2].into_iter().collect();
        let gaps = Gaps::default();
        resize_tiled(&mut tree, screen, &vis, &gaps, 2, (true, false, false, false), (5000, 0));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 999, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 999, y: 0, w: 1, h: 500 }));
    }

    #[test]
    fn test_resize_rect_keeps_one_pixel_minimum() {
        let r = Rect { x: 0, y: 0, w: 300, h: 300 };
        let left = resize_edges(r, (5, 150));
        assert_eq!(
            resize_rect(r, left, (400, 0)),
            Rect { x: 299, y: 0, w: 1, h: 300 }
        );
    }
}
