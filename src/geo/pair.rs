use super::{convex_hull::convex_hull, point::Point};
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

/// O(n)
pub fn poly_diameter<T>(pts: &[Point<T>]) -> Option<(Point<T>, Point<T>)>
where
    T: Clone + Default + Ord + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    let m = pts.len();
    if m == 1 {
        return Some((pts[0].clone(), pts[0].clone()));
    }
    let mut best = {
        let d = pts[1].clone() - pts[0].clone();
        d.dot(&d)
    };
    let mut ans = (pts[0].clone(), pts[1].clone());
    if m == 2 {
        return Some(ans);
    }
    let mut j = 1;
    for i in 0..m {
        let ni = (i + 1) % m;
        let mut nj = (j + 1) % m;
        while nj != i
            && (pts[ni].clone() - pts[i].clone()).cross(&(pts[nj].clone() - pts[j].clone()))
                > T::default()
        {
            j = (j + 1) % m;
            nj = (j + 1) % m;
        }
        let diff = pts[i].clone() - pts[j].clone();
        let d2 = diff.dot(&diff);
        if d2 > best {
            best = d2;
            ans = (pts[i].clone(), pts[j].clone());
        }
    }
    Some(ans)
}

/// O(n log n)
pub fn furthest_pair<T>(pts: &mut [Point<T>]) -> Option<(Point<T>, Point<T>)>
where
    T: Clone + Default + Ord + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    let n = pts.len();
    if n < 2 {
        return None;
    }
    let hull = convex_hull(pts);
    poly_diameter(&hull)
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

    // Helper function to create a point
    fn pt(x: i32, y: i32) -> Point<i32> {
        Point { x, y }
    }

    // Helper function to check if two points are equal (order doesn't matter for pairs)
    fn pairs_equal(p1: (Point<i32>, Point<i32>), p2: (Point<i32>, Point<i32>)) -> bool {
        (p1.0 == p2.0 && p1.1 == p2.1) || (p1.0 == p2.1 && p1.1 == p2.0)
    }

    #[test]
    fn test_empty_slice() {
        let mut pts: Vec<Point<i32>> = vec![];
        assert_eq!(furthest_pair(&mut pts), None);
    }

    #[test]
    fn test_single_point() {
        let mut pts = vec![pt(1, 1)];
        assert_eq!(furthest_pair(&mut pts), None);
    }

    #[test]
    fn test_two_points() {
        let mut pts = vec![pt(0, 0), pt(3, 4)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(pairs_equal(result, (pt(0, 0), pt(3, 4))));
    }

    #[test]
    fn test_two_identical_points() {
        let mut pts = vec![pt(1, 1), pt(1, 1)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(pairs_equal(result, (pt(1, 1), pt(1, 1))));
    }

    #[test]
    fn test_three_points_collinear() {
        let mut pts = vec![pt(0, 0), pt(1, 1), pt(2, 2)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(pairs_equal(result, (pt(0, 0), pt(2, 2))));
    }

    #[test]
    fn test_square_vertices() {
        let mut pts = vec![pt(0, 0), pt(0, 1), pt(1, 0), pt(1, 1)];
        let result = furthest_pair(&mut pts).unwrap();
        // Diagonal of unit square should be the furthest pair
        assert!(
            pairs_equal(result, (pt(0, 0), pt(1, 1))) || pairs_equal(result, (pt(0, 1), pt(1, 0)))
        );
    }

    #[test]
    fn test_rectangle() {
        let mut pts = vec![pt(0, 0), pt(0, 2), pt(3, 0), pt(3, 2)];
        let result = furthest_pair(&mut pts).unwrap();
        // Diagonal should be furthest
        assert!(
            pairs_equal(result, (pt(0, 0), pt(3, 2))) || pairs_equal(result, (pt(0, 2), pt(3, 0)))
        );
    }

    #[test]
    fn test_triangle() {
        let mut pts = vec![pt(0, 0), pt(4, 0), pt(2, 3)];
        let result = furthest_pair(&mut pts).unwrap();
        // Base of triangle (0,0) to (4,0) has distance 4
        // Other sides have distances sqrt(13) ≈ 3.6
        assert!(pairs_equal(result, (pt(0, 0), pt(4, 0))));
    }

    #[test]
    fn test_regular_hexagon_points() {
        // Points roughly forming a hexagon
        let mut pts = vec![
            pt(2, 0),   // right
            pt(1, 1),   // top-right
            pt(-1, 1),  // top-left
            pt(-2, 0),  // left
            pt(-1, -1), // bottom-left
            pt(1, -1),  // bottom-right
        ];
        let result = furthest_pair(&mut pts).unwrap();
        // Opposite vertices should be furthest
        assert!(pairs_equal(result, (pt(-2, 0), pt(2, 0))));
    }

    #[test]
    fn test_points_with_interior_points() {
        // Hull will be the outer square, interior point should be ignored
        let mut pts = vec![
            pt(0, 0),
            pt(0, 4),
            pt(4, 0),
            pt(4, 4), // square corners
            pt(2, 2), // interior point
        ];
        let result = furthest_pair(&mut pts).unwrap();
        // Diagonal of the square
        assert!(
            pairs_equal(result, (pt(0, 0), pt(4, 4))) || pairs_equal(result, (pt(0, 4), pt(4, 0)))
        );
    }

    #[test]
    fn test_large_coordinate_values() {
        let mut pts = vec![pt(0, 0), pt(1000, 0), pt(0, 1000), pt(1000, 1000)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(
            pairs_equal(result, (pt(0, 0), pt(1000, 1000)))
                || pairs_equal(result, (pt(0, 1000), pt(1000, 0)))
        );
    }

    #[test]
    fn test_negative_coordinates() {
        let mut pts = vec![pt(-2, -2), pt(-2, 2), pt(2, -2), pt(2, 2)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(
            pairs_equal(result, (pt(-2, -2), pt(2, 2)))
                || pairs_equal(result, (pt(-2, 2), pt(2, -2)))
        );
    }

    #[test]
    fn test_many_collinear_points() {
        let mut pts = vec![pt(0, 0), pt(1, 0), pt(2, 0), pt(3, 0), pt(4, 0), pt(5, 0)];
        let result = furthest_pair(&mut pts).unwrap();
        assert!(pairs_equal(result, (pt(0, 0), pt(5, 0))));
    }

    #[test]
    fn test_diamond_shape() {
        let mut pts = vec![
            pt(0, 3),  // top
            pt(3, 0),  // right
            pt(0, -3), // bottom
            pt(-3, 0), // left
        ];
        let result = furthest_pair(&mut pts).unwrap();
        // Vertical diameter is 6, horizontal diameter is 6
        // Both should have same distance
        assert!(
            pairs_equal(result, (pt(0, -3), pt(0, 3)))
                || pairs_equal(result, (pt(-3, 0), pt(3, 0)))
        );
    }

    #[test]
    fn test_random_cloud_with_known_extremes() {
        let mut pts = vec![
            pt(1, 1),
            pt(2, 3),
            pt(3, 1),
            pt(1, 2),
            pt(-5, 0), // leftmost extreme
            pt(7, 1),  // rightmost extreme
        ];
        let result = furthest_pair(&mut pts).unwrap();
        // The two extreme points should be furthest
        assert!(pairs_equal(result, (pt(-5, 0), pt(7, 1))));
    }

    #[test]
    fn test_all_same_points() {
        let mut pts = vec![pt(2, 3); 5]; // 5 identical points
        let result = furthest_pair(&mut pts).unwrap();
        assert!(pairs_equal(result, (pt(2, 3), pt(2, 3))));
    }

    #[test]
    fn test_l_shaped_points() {
        let mut pts = vec![
            pt(0, 0),
            pt(0, 1),
            pt(0, 2),
            pt(0, 3), // vertical line
            pt(1, 0),
            pt(2, 0),
            pt(3, 0),
            pt(4, 0), // horizontal line
        ];
        let result = furthest_pair(&mut pts).unwrap();
        // Furthest should be from (0,3) to (4,0)
        assert!(pairs_equal(result, (pt(0, 3), pt(4, 0))));
    }

    // Property-based test: result should always be from the convex hull
    #[test]
    fn test_result_comes_from_convex_hull() {
        let mut pts = vec![
            pt(0, 0),
            pt(1, 1),
            pt(2, 0),
            pt(1, -1), // diamond
            pt(0, 0),
            pt(1, 0), // duplicate and interior point
        ];
        let hull = convex_hull(&mut pts.clone());
        let result = furthest_pair(&mut pts).unwrap();

        // Both points in the result should be in the convex hull
        assert!(hull.contains(&result.0));
        assert!(hull.contains(&result.1));
    }
}
