use super::{convex_hull::convex_hull, point::Point, polygon::diameter};
use std::{
    collections::BTreeSet,
    ops::{Add, Mul, Sub},
};

// O(n log n)
pub fn closest_pair(pts: &mut [Point<i64>]) -> (i64, Point<i64>, Point<i64>) {
    let n = pts.len();
    debug_assert!(n > 1);
    pts.sort_unstable();
    let mut s = BTreeSet::new();
    let mut best = (Point::new(0, 0), Point::new(0, 0));
    let mut best_dist = i64::MAX;
    let mut j = 0;
    for i in 0..n {
        let d = best_dist.isqrt() + 1;
        while pts[i].x - pts[j].x >= d {
            s.remove(&(pts[j].y, pts[j].x));
            j += 1;
        }
        for &(y, x) in s.range((pts[i].y - d, pts[i].x)..=(pts[i].y + d, pts[i].x)) {
            let (dx, dy) = (pts[i].x - x, pts[i].y - y);
            let dist = dx * dx + dy * dy;
            if dist < best_dist {
                best_dist = dist;
                best = (Point::new(x, y), pts[i]);
            }
        }
        s.insert((pts[i].y, pts[i].x));
    }

    (best_dist, best.0, best.1)
}

/// O(n log n)
/// Note this returns the squared distance.
pub fn furthest_pair<T>(pts: &mut [Point<T>]) -> Option<(T, (usize, usize))>
where
    T: Clone + Default + PartialOrd + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    let n = pts.len();
    if n < 2 {
        return None;
    }
    let hull = convex_hull(pts);
    diameter(&hull)
}
