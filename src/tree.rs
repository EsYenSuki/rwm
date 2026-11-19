use std::collections::HashSet;

use x11rb::protocol::xproto::Window;

use crate::config;

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

    /// Collects every leaf window into `out`, including hidden ones. Used to
    /// reconcile the tree with the current client list.
    pub fn leaves(&self, out: &mut Vec<Window>) {
        match self {
            Node::Leaf(w) => out.push(*w),
            Node::Split { first, second, .. } => {
                first.leaves(out);
                second.leaves(out);
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

    /// Replaces the leaf `target` with an even dwindle split holding `target`
    /// and `new`.
    pub fn insert(&mut self, target: Window, new: Window, new_first: bool, side_by_side: bool) -> bool {
        self.insert_with_ratio(
            target,
            new,
            new_first,
            side_by_side,
            config::DWINDLE_DEFAULT_SPLIT_SHARE,
        )
    }

    /// Replaces the leaf `target` with a split holding `target` and `new`. The
    /// ratio is the first half's share; dwindle drops use `insert()` instead,
    /// which always uses the default even share.
    pub fn insert_with_ratio(
        &mut self,
        target: Window,
        new: Window,
        new_first: bool,
        side_by_side: bool,
        ratio: f64,
    ) -> bool {
        if let Node::Split { first, second, .. } = self {
            return first.insert_with_ratio(target, new, new_first, side_by_side, ratio)
                || second.insert_with_ratio(target, new, new_first, side_by_side, ratio);
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
            ratio: ratio.clamp(0.1, 0.9),
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

/// Rescales the ratios inside `node` so its along-axis length changes from
/// `old_len` to `new_len` while every leaf keeps its pixel size except the one
/// next to the moved boundary, which absorbs the difference. `anchor_second`
/// means the second child (right/bottom) is the one away from the boundary.
/// A cross-axis split has all its leaves spanning the full length, so it can
/// only scale as a whole and no internal ratio needs to change.
fn rescale_subtree(
    node: &mut Node,
    axis_side_by_side: bool,
    gaps: &Gaps,
    old_len: i32,
    new_len: i32,
    anchor_second: bool,
) {
    let Node::Split { side_by_side, ratio, first, second } = node else {
        return;
    };
    if *side_by_side != axis_side_by_side {
        return;
    }
    let gap = if axis_side_by_side { gaps.iv } else { gaps.ih };
    let old_usable = (old_len - gap).max(1);
    let new_usable = (new_len - gap).max(1);
    let old_first = first_len(old_usable, *ratio);
    let old_second = (old_usable - old_first).max(0);
    let delta = new_len - old_len;

    let (new_first, new_second) = if anchor_second {
        (old_first, (old_second + delta).max(0))
    } else {
        ((old_first + delta).max(0), old_second)
    };
    *ratio = (new_first as f64 / new_usable as f64).clamp(0.01, 0.99);

    if anchor_second {
        rescale_subtree(second, axis_side_by_side, gaps, old_second, new_second, true);
    } else {
        rescale_subtree(first, axis_side_by_side, gaps, old_first, new_first, false);
    }
}

/// One split on the path from the tree root to the window being resized,
/// captured before any ratio changes. Hyprland keeps the same information in
/// every node's cached `box`.
#[derive(Clone, Copy, Debug)]
struct PathEntry {
    side_by_side: bool,
    child_first: bool,
    total: i32,
    first: i32,
}

/// Walks root-to-leaf to `win`, pushing a `PathEntry` for each split that
/// actually separates two visible children. Splits with a hidden child have
/// no boundary to move, so they are traversed without an entry. The returned
/// path is leaf-first, matching the direction Hyprland walks parent links.
fn collect_path(
    node: &Node,
    rect: Rect,
    vis: &HashSet<Window>,
    win: Window,
    gaps: &Gaps,
    path: &mut Vec<PathEntry>,
) -> bool {
    let Node::Split { side_by_side, ratio, first, second } = node else {
        return matches!(node, Node::Leaf(w) if *w == win);
    };
    let (fv, sv) = (first.any_visible(vis), second.any_visible(vis));
    if !fv || !sv {
        return if fv {
            collect_path(first, rect, vis, win, gaps, path)
        } else if sv {
            collect_path(second, rect, vis, win, gaps, path)
        } else {
            false
        };
    }
    let gap = if *side_by_side { gaps.iv } else { gaps.ih };
    let (a, b) = rect.split(*side_by_side, gap, *ratio);
    let child_first = first.has_leaf(win);
    let found = if child_first {
        collect_path(first, a, vis, win, gaps, path)
    } else {
        collect_path(second, b, vis, win, gaps, path)
    };
    if found {
        let len = (if *side_by_side { rect.w } else { rect.h }) as i32;
        let total = (len - gap).max(0);
        path.push(PathEntry {
            side_by_side: *side_by_side,
            child_first,
            total,
            first: first_len(total, *ratio),
        });
    }
    found
}

/// The split on the dragged side of one axis, scanning the path from the
/// window towards the root. Moving this split's boundary is what resizes the
/// window: any shallower same-axis split would move a whole subtree instead.
fn resize_outer(path: &[PathEntry], side_by_side: bool, drag_first: bool) -> Option<usize> {
    for i in (0..path.len()).rev() {
        let e = &path[i];
        if e.side_by_side == side_by_side && e.child_first == drag_first {
            return Some(i);
        }
    }
    None
}

/// What to do with one split's ratio when applying the plan top-down.
#[derive(Clone, Copy)]
enum RatioTarget {
    /// Set the ratio directly. Used at the outer split, whose own box does not
    /// change size; only its boundary moves.
    Fraction(f64),
    /// Keep the first child at this many pixels. `total` is recomputed from
    /// the split's current box, so the far edge stays anchored even when an
    /// ancestor grew by a fraction of the drag.
    First(i32),
    /// Keep the second child at this many pixels.
    Second(i32),
}

/// A planned ratio change at one split on the focused path.
#[derive(Clone, Copy)]
struct RatioChange {
    target: RatioTarget,
    /// The outer split's other child shrinks as the focused side grows.
    /// `(anchor_second, old_len, new_len)` lets that child's far-side leaves
    /// keep their pixel sizes while the leaf next to the boundary absorbs it.
    sibling: Option<(bool, i32, i32)>,
}

/// Plans the ratio changes for one axis into `plan`, which is indexed in the
/// same root-first order as `path`.
fn apply_axis(
    plan: &mut [Option<RatioChange>],
    path: &[PathEntry],
    side_by_side: bool,
    drag_first: bool,
    d: i32,
) {
    let Some(outer) = resize_outer(path, side_by_side, drag_first) else {
        return;
    };
    let e = &path[outer];
    if e.total < 2 {
        return;
    }
    let new_first = (e.first + d).clamp(1, e.total - 1);
    let applied = new_first - e.first;
    let sibling = if e.child_first {
        // Focused side is first; the second child loses `applied` pixels.
        (false, e.total - e.first, e.total - e.first - applied)
    } else {
        // Focused side is second; the first child loses `-applied` pixels.
        (true, e.first, e.first + applied)
    };
    plan[outer] = Some(RatioChange {
        target: RatioTarget::Fraction(new_first as f64 / e.total as f64),
        sibling: Some(sibling),
    });

    // Every deeper split on the far side of the drag contributes length to
    // the window's far edge. Each one must keep its *other* child's pixel
    // length, otherwise that edge drifts as the outer boundary moves. A
    // spawned window adds another such split (the split it created), which is
    // exactly the case the old single-inner compensation could not handle.
    for i in (outer + 1)..path.len() {
        let a = &path[i];
        if a.side_by_side != side_by_side || a.child_first == drag_first {
            continue;
        }
        let kept = if a.child_first {
            // Window is first; the second child sits behind the far edge.
            a.total - a.first
        } else {
            // Window is second; the first child sits behind the far edge.
            a.first
        };
        let target = if a.child_first {
            RatioTarget::Second(kept)
        } else {
            RatioTarget::First(kept)
        };
        plan[i] = Some(RatioChange { target, sibling: None });
    }
}

fn axis_total(rect: Rect, side_by_side: bool, gaps: &Gaps) -> i32 {
    let gap = if side_by_side { gaps.iv } else { gaps.ih };
    let len = if side_by_side { rect.w } else { rect.h };
    (len as i32 - gap).max(0)
}

/// Applies the planned ratios while walking back down the focused path.
/// `depth` counts only splits with two visible children, like `collect_path`.
fn apply_plan(
    node: &mut Node,
    rect: Rect,
    vis: &HashSet<Window>,
    gaps: &Gaps,
    win: Window,
    plan: &[Option<RatioChange>],
    depth: usize,
) {
    let Node::Split { side_by_side, ratio, first, second } = node else {
        return;
    };
    let (fv, sv) = (first.any_visible(vis), second.any_visible(vis));
    if !(fv && sv) {
        if fv {
            apply_plan(first, rect, vis, gaps, win, plan, depth);
        } else if sv {
            apply_plan(second, rect, vis, gaps, win, plan, depth);
        }
        return;
    }
    let child_first = first.has_leaf(win);
    if let Some(change) = plan.get(depth).copied().flatten() {
        match change.target {
            RatioTarget::Fraction(r) => *ratio = r.clamp(0.0, 1.0),
            RatioTarget::First(keep) => {
                let total = axis_total(rect, *side_by_side, gaps);
                if total > 0 {
                    *ratio = keep.clamp(0, total) as f64 / total as f64;
                }
            }
            RatioTarget::Second(keep) => {
                let total = axis_total(rect, *side_by_side, gaps);
                if total > 0 {
                    *ratio = (total - keep.clamp(0, total)) as f64 / total as f64;
                }
            }
        }
        if let Some((anchor_second, old_len, new_len)) = change.sibling {
            if child_first {
                rescale_subtree(second, *side_by_side, gaps, old_len, new_len, anchor_second);
            } else {
                rescale_subtree(first, *side_by_side, gaps, old_len, new_len, anchor_second);
            }
        }
    }
    let gap = if *side_by_side { gaps.iv } else { gaps.ih };
    let (a, b) = rect.split(*side_by_side, gap, *ratio);
    if child_first {
        apply_plan(first, a, vis, gaps, win, plan, depth + 1);
    } else {
        apply_plan(second, b, vis, gaps, win, plan, depth + 1);
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
    let (left, right, top, bottom) = edges;
    if !(left || right || top || bottom) {
        return;
    }
    let mut path = Vec::new();
    if !collect_path(node, rect, vis, win, gaps, &mut path) {
        return;
    }
    path.reverse();
    let mut plan = vec![None; path.len()];
    if left || right {
        apply_axis(&mut plan, &path, true, right, delta.0);
    }
    if top || bottom {
        apply_axis(&mut plan, &path, false, bottom, delta.1);
    }
    apply_plan(node, rect, vis, gaps, win, &plan, 0);
}

/// Hyprland's dwindle split decision for a spawn or a pointer drop: wide tiles
/// split left/right, tall tiles split top/bottom, and the pointer's half decides
/// whether the new window becomes the first (left/top) or second child.
///
/// Returns `(new_first, side_by_side)`.
pub fn split_for_drop(rect: Rect, (px, py): (i32, i32)) -> (bool, bool) {
    let side_by_side =
        rect.w as f64 > rect.h as f64 * config::DWINDLE_SPLIT_WIDTH_MULTIPLIER;
    let new_first = if side_by_side {
        px < rect.x + (rect.w / 2) as i32
    } else {
        py < rect.y + (rect.h / 2) as i32
    };
    (new_first, side_by_side)
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
    fn test_insert_with_ratio_supports_custom_share() {
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        // A custom caller can still ask for a 30/70 split; dwindle drops use
        // `insert()`, which keeps the default even share.
        assert!(tree.insert_with_ratio(1, 2, true, true, 0.3));
        let out = layout_all(&tree, screen);
        assert_eq!(out[0], (2, Rect { x: 0, y: 0, w: 300, h: 500 }));
        assert_eq!(out[1], (1, Rect { x: 300, y: 0, w: 700, h: 500 }));
    }

    #[test]
    fn test_dwindle_split_uses_long_axis_and_cursor_half() {
        let wide = Rect { x: 100, y: 200, w: 1920, h: 1080 };
        assert_eq!(split_for_drop(wide, (300, 700)), (true, true));
        assert_eq!(split_for_drop(wide, (1500, 700)), (false, true));

        let tall = Rect { x: 100, y: 200, w: 960, h: 1080 };
        assert_eq!(split_for_drop(tall, (500, 400)), (true, false));
        assert_eq!(split_for_drop(tall, (500, 900)), (false, false));
    }

    #[test]
    fn test_repeated_drop_at_same_point_keeps_same_split() {
        let screen = Rect { x: 0, y: 0, w: 1920, h: 1080 };
        let (a, b): (Window, Window) = (1, 2);
        let mut tree = Node::Leaf(a);
        assert!(tree.insert(a, b, false, true));
        let expected = vec![
            (a, Rect { x: 0, y: 0, w: 960, h: 1080 }),
            (b, Rect { x: 960, y: 0, w: 960, h: 1080 }),
        ];

        for _ in 0..3 {
            // Hyprland removes the dragged window before re-tiling, so B is
            // full-screen when the target split is chosen.
            tree = tree.remove(a).unwrap();
            let leaves = layout_all(&tree, screen);
            assert_eq!(leaves, vec![(b, screen)]);

            let (target, rect) = leaves[0];
            let (new_first, side_by_side) = split_for_drop(rect, (200, 500));
            assert!(new_first);
            assert!(side_by_side);
            assert!(tree.insert(target, a, new_first, side_by_side));
            assert_eq!(layout_all(&tree, screen), expected);
        }
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
    fn test_resize_center_keeps_non_adjacent_window_size() {
        // Tree: Split(Split(W1, W2), W3) — W2 is the rightmost leaf of the
        // first subtree, so its right edge is the root boundary.
        // Layout: W1=[0,250], W2=[250,500], W3=[500,1000].
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut tree = Node::Leaf(1);
        tree.insert(1, 2, false, true); // W1 | W2
        tree = append(Some(tree), 3, screen); // (W1 | W2) | W3
        let vis: HashSet<Window> = [1, 2, 3].into_iter().collect();
        let gaps = Gaps::default();

        let mut initial = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut initial);
        assert_eq!(initial[0], (1, Rect { x: 0, y: 0, w: 250, h: 500 }));
        assert_eq!(initial[1], (2, Rect { x: 250, y: 0, w: 250, h: 500 }));
        assert_eq!(initial[2], (3, Rect { x: 500, y: 0, w: 500, h: 500 }));

        // Resize W2's right edge by +100: only W2/W3 boundary should move.
        // W1 must keep its 250px width; W2 grows to 350; W3 shrinks to 400.
        resize_tiled(&mut tree, screen, &vis, &gaps, 2, (false, true, false, false), (100, 0));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 250, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 250, y: 0, w: 350, h: 500 }));
        assert_eq!(out[2], (3, Rect { x: 600, y: 0, w: 400, h: 500 }));

        // Resize W3's left edge back by -100: W1 keeps 250, W2 shrinks to 250,
        // W3 grows back to 500.
        resize_tiled(&mut tree, screen, &vis, &gaps, 3, (true, false, false, false), (-100, 0));
        out.clear();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 250, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 250, y: 0, w: 250, h: 500 }));
        assert_eq!(out[2], (3, Rect { x: 500, y: 0, w: 500, h: 500 }));
    }

    #[test]
    fn test_resize_middle_boundary_four_windows() {
        // Tree: (W1|W2)|(W3|W4). Resizing W2/W3 boundary must change only W2
        // and W3; W1 and W4 keep their exact pixel sizes.
        let screen = Rect { x: 0, y: 0, w: 1000, h: 500 };
        let mut left = Node::Leaf(1);
        left.insert(1, 2, false, true);
        let mut right = Node::Leaf(3);
        right.insert(3, 4, false, true);
        let mut tree = Node::Split {
            side_by_side: true,
            ratio: 0.5,
            first: Box::new(left),
            second: Box::new(right),
        };
        let vis: HashSet<Window> = [1, 2, 3, 4].into_iter().collect();
        let gaps = Gaps::default();

        resize_tiled(&mut tree, screen, &vis, &gaps, 2, (false, true, false, false), (100, 0));
        let mut out = Vec::new();
        tree.layout(screen, &vis, &gaps, &mut out);
        assert_eq!(out[0], (1, Rect { x: 0, y: 0, w: 250, h: 500 }));
        assert_eq!(out[1], (2, Rect { x: 250, y: 0, w: 350, h: 500 }));
        assert_eq!(out[2], (3, Rect { x: 600, y: 0, w: 150, h: 500 }));
        assert_eq!(out[3], (4, Rect { x: 750, y: 0, w: 250, h: 500 }));
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

    fn pair(a: Node, b: Node, side_by_side: bool) -> Node {
        Node::Split {
            side_by_side,
            ratio: 0.5,
            first: Box::new(a),
            second: Box::new(b),
        }
    }

    fn leaf_pair(a: Window, b: Window, side_by_side: bool) -> Node {
        pair(Node::Leaf(a), Node::Leaf(b), side_by_side)
    }

    /// The balanced grid from the bug report: columns grouped in row pairs,
    /// row pairs grouped in halves.
    fn balanced_grid() -> Node {
        pair(
            pair(
                pair(leaf_pair(1, 5, false), leaf_pair(2, 6, false), true),
                pair(leaf_pair(9, 13, false), leaf_pair(10, 14, false), true),
                false,
            ),
            pair(
                pair(leaf_pair(3, 7, false), leaf_pair(4, 8, false), true),
                pair(leaf_pair(11, 15, false), leaf_pair(12, 16, false), true),
                false,
            ),
            true,
        )
    }

    /// A dwindle comb: four vertical columns, each an H-comb of four rows.
    fn comb_grid() -> Node {
        let column = |rows: [Window; 4]| -> Node {
            let mut n = Node::Leaf(rows[3]);
            for &w in rows[..3].iter().rev() {
                n = pair(Node::Leaf(w), n, false);
            }
            n
        };
        let mut n = column([4, 8, 12, 16]);
        for rows in [[3, 7, 11, 15], [2, 6, 10, 14], [1, 5, 9, 13]] {
            n = pair(column(rows), n, true);
        }
        n
    }

    fn layout_vis(node: &Node, rect: Rect, vis: &HashSet<Window>, gaps: &Gaps) -> Vec<(Window, Rect)> {
        let mut out = Vec::new();
        node.layout(rect, vis, gaps, &mut out);
        out
    }

    fn rect_of(out: &[(Window, Rect)], win: Window) -> Rect {
        out.iter().find(|(w, _)| *w == win).map(|(_, r)| *r).unwrap()
    }

    #[test]
    fn test_resize_grid_anchors_focused_corner() {
        let screen = Rect { x: 0, y: 0, w: 800, h: 800 };
        let vis: HashSet<Window> = (1..=16).collect();
        let gaps = Gaps::default();

        // W6 bottom-right: its top-left corner stays where it was. The old
        // code moved it to (220,220) and changed W2's height and W5's width.
        let mut t = balanced_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 6, (false, true, false, true), (40, 40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        assert_eq!((rect_of(&out, 6).x, rect_of(&out, 6).y), (200, 200));
        assert_eq!((rect_of(&out, 2).y, rect_of(&out, 2).h), (0, 200));
        assert_eq!((rect_of(&out, 5).x, rect_of(&out, 5).w), (0, 200));

        // W10 top-right: its bottom-left corner stays put.
        let mut t = balanced_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 10, (false, true, true, false), (40, -40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        let r10 = rect_of(&out, 10);
        assert_eq!((r10.x, r10.y + r10.h as i32), (200, 600));
        assert_eq!((rect_of(&out, 9).w, rect_of(&out, 13).w), (200, 200));

        // W7 bottom-left: its top-right corner stays put.
        let mut t = balanced_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 7, (true, false, false, true), (-40, 40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        let r7 = rect_of(&out, 7);
        assert_eq!((r7.x + r7.w as i32, r7.y), (600, 200));

        // W11 top-left: its bottom-right corner stays put.
        let mut t = balanced_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 11, (true, false, true, false), (-40, -40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        let r11 = rect_of(&out, 11);
        assert_eq!((r11.x + r11.w as i32, r11.y + r11.h as i32), (600, 600));
    }

    #[test]
    fn test_resize_comb_grid_keeps_unrelated_windows_fixed() {
        let screen = Rect { x: 0, y: 0, w: 800, h: 800 };
        let vis: HashSet<Window> = (1..=16).collect();
        let gaps = Gaps::default();

        let before = {
            let t = comb_grid();
            layout_vis(&t, screen, &vis, &gaps)
        };

        // A column comb shares fewer boundaries than the balanced grid: W1
        // and W5 are completely untouched by a W6 resize.
        let mut t = comb_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 6, (false, true, false, true), (40, 40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        assert_eq!(rect_of(&out, 1), rect_of(&before, 1));
        assert_eq!(rect_of(&out, 5), rect_of(&before, 5));
        assert_eq!((rect_of(&out, 2).y, rect_of(&out, 2).h), (0, 400));
        assert_eq!((rect_of(&out, 6).x, rect_of(&out, 6).y), (400, 400));

        // W10's top-right drag leaves the whole first column (W9, W13) alone.
        let mut t = comb_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 10, (false, true, true, false), (40, -40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        assert_eq!(rect_of(&out, 9), rect_of(&before, 9));
        assert_eq!(rect_of(&out, 13), rect_of(&before, 13));

        // W7's bottom-left drag leaves the fourth column (W8, W12, W16) alone.
        let mut t = comb_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 7, (true, false, false, true), (-40, 40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        assert_eq!(rect_of(&out, 8), rect_of(&before, 8));
        assert_eq!(rect_of(&out, 12), rect_of(&before, 12));
        assert_eq!(rect_of(&out, 16), rect_of(&before, 16));

        // W11's top-left drag leaves the first column (W1, W5, W9, W13) alone.
        let mut t = comb_grid();
        let out = {
            resize_tiled(&mut t, screen, &vis, &gaps, 11, (true, false, true, false), (-40, -40));
            layout_vis(&t, screen, &vis, &gaps)
        };
        assert_eq!(rect_of(&out, 1), rect_of(&before, 1));
        assert_eq!(rect_of(&out, 5), rect_of(&before, 5));
        assert_eq!(rect_of(&out, 9), rect_of(&before, 9));
        assert_eq!(rect_of(&out, 13), rect_of(&before, 13));
    }

    #[test]
    fn test_resize_spawned_window_inside_grid_corner() {
        let screen = Rect { x: 0, y: 0, w: 800, h: 800 };
        let vis: HashSet<Window> = (1..=17).collect();
        let gaps = Gaps::default();

        // Spawn W17 in the top half of W6: W6's 200x200 box splits into
        // W17 (top, 100px) and W6 (bottom, 100px).
        let mut t = balanced_grid();
        assert!(t.insert(6, 17, true, false));
        let before = layout_vis(&t, screen, &vis, &gaps);
        assert_eq!(rect_of(&before, 17), Rect { x: 200, y: 200, w: 200, h: 100 });

        // Drag W17's bottom edge down 40px. Only the W17/W6 split should move:
        // W17 grows to 140, W6 shrinks to 60. Every unrelated window stays put.
        resize_tiled(&mut t, screen, &vis, &gaps, 17, (false, false, false, true), (0, 40));
        let after = layout_vis(&t, screen, &vis, &gaps);
        assert_eq!(rect_of(&after, 17), Rect { x: 200, y: 200, w: 200, h: 140 });
        assert_eq!(rect_of(&after, 6), Rect { x: 200, y: 340, w: 200, h: 60 });
        for w in [1, 2, 5, 9, 10, 13, 14] {
            assert_eq!(rect_of(&after, w), rect_of(&before, w), "W{w} moved");
        }
    }

    #[test]
    fn test_resize_spawned_window_anchors_far_edge_on_every_side() {
        let screen = Rect { x: 0, y: 0, w: 800, h: 800 };
        let vis: HashSet<Window> = (1..=17).collect();
        let gaps = Gaps::default();

        // A spawned window is a split nested inside the host leaf. Its far
        // edge must stay anchored through that extra split, not just the host
        // column's split. The old single-inner compensation moved the window
        // as well as resizing it (e.g. W17 y 300 -> 305 on a bottom drag).
        let drags = [
            ((false, true, false, false), (20, 0)),  // right edge
            ((true, false, false, false), (-20, 0)), // left edge
            ((false, false, false, true), (0, 20)),  // bottom edge
            ((false, false, true, false), (0, -20)), // top edge
        ];
        for host in [6, 7, 10, 11] {
            for new_first in [true, false] {
                for (edges, delta) in drags {
                    let mut t = balanced_grid();
                    assert!(t.insert(host, 17, new_first, false));
                    let before = rect_of(&layout_vis(&t, screen, &vis, &gaps), 17);
                    resize_tiled(&mut t, screen, &vis, &gaps, 17, edges, delta);
                    let after = rect_of(&layout_vis(&t, screen, &vis, &gaps), 17);
                    assert_eq!(
                        after,
                        resize_rect(before, edges, delta),
                        "host={host} new_first={new_first} edges={edges:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_resize_grid_keeps_geometry_consistent_with_gaps() {
        let screen = Rect { x: 10, y: 20, w: 800, h: 800 };
        let vis: HashSet<Window> = (1..=16).collect();
        let gaps = Gaps { oh: 8, ov: 12, ih: 6, iv: 4 };
        let area = inset(screen, &gaps);
        let mut t = balanced_grid();
        resize_tiled(&mut t, area, &vis, &gaps, 6, (false, true, false, true), (37, 29));
        let out = layout_vis(&t, area, &vis, &gaps);
        assert_eq!(out.len(), 16);
        for (_, r) in &out {
            assert!(r.w > 0 && r.h > 0);
            assert!(r.x >= screen.x + gaps.ov && r.y >= screen.y + gaps.oh);
        }
        // The focused window keeps its top-left corner; nothing jumps across
        // the inner gaps.
        let before = layout_vis(&balanced_grid(), area, &vis, &gaps);
        let r6 = rect_of(&out, 6);
        let b6 = rect_of(&before, 6);
        assert_eq!((r6.x, r6.y), (b6.x, b6.y));
    }
}
