use super::point::Point;
use std::collections::BTreeSet;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_closest_simple() {
        let mut pts = vec![
            Point { x: 0, y: 0 },
            Point { x: 5, y: 5 },
            Point { x: 1, y: 1 },
            Point { x: 8, y: 0 },
        ];
        let (d, a, b) = closest_pair(&mut pts);
        // (0,0)–(1,1) are the closest pair, dist2 = 2
        assert_eq!(d, 2);
        assert!(
            (a, b) == (Point { x: 0, y: 0 }, Point { x: 1, y: 1 })
                || (a, b) == (Point { x: 1, y: 1 }, Point { x: 0, y: 0 })
        );
    }

    #[test]
    fn test_closest_vertical_strip() {
        let mut pts = vec![
            Point { x: 10, y: 10 },
            Point { x: 11, y: 12 },
            Point { x: 11, y: 11 },
            Point { x: -5, y: 0 },
        ];
        let (d, a, b) = closest_pair(&mut pts);
        assert_eq!(d, 1);
        // (11,11)–(11,12) are the closest vertically
        assert!(
            (a, b) == (Point { x: 11, y: 11 }, Point { x: 11, y: 12 })
                || (a, b) == (Point { x: 11, y: 12 }, Point { x: 11, y: 11 })
        );
    }
}
