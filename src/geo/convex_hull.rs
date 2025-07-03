use super::point::Point;
use std::ops::{Mul, Sub};

pub fn convex_hull<T: Clone + Ord + Default + Mul<T, Output = T> + Sub<T, Output = T>>(
    pts: &mut [Point<T>],
) -> Vec<Point<T>> {
    let n = pts.len();
    let mut hull = Vec::new();
    if n < 3 {
        hull.extend_from_slice(pts);
        return hull;
    }
    pts.sort_unstable();
    for i in 0..n {
        while hull.len() > 1
            && hull[hull.len() - 2]
                .clone()
                .area(&hull[hull.len() - 1], &pts[i])
                <= T::default()
        {
            hull.pop();
        }
        hull.push(pts[i].clone());
    }
    let lower_len = hull.len();
    for i in (0..n).rev() {
        while hull.len() > lower_len
            && hull[hull.len() - 2]
                .clone()
                .area(&hull[hull.len() - 1], &pts[i])
                <= T::default()
        {
            hull.pop();
        }
        hull.push(pts[i].clone());
    }
    hull.pop();
    hull
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny helper to build a point.
    fn pt(x: i64, y: i64) -> Point<i64> {
        Point { x, y }
    }

    #[test]
    fn test_empty_and_small() {
        let mut v: Vec<Point<i64>> = vec![];
        assert_eq!(convex_hull(&mut v), Vec::new());

        let mut v = vec![pt(1, 2)];
        assert_eq!(convex_hull(&mut v), vec![pt(1, 2)]);

        let mut v = vec![pt(2, 2), pt(1, 1)];
        let mut got = convex_hull(&mut v);
        got.sort_unstable();
        let mut want = vec![pt(1, 1), pt(2, 2)];
        want.sort_unstable();
        assert_eq!(got, want);
    }

    #[test]
    fn test_collinear_points() {
        let mut v = vec![pt(0, 0), pt(1, 1), pt(2, 2), pt(3, 3)];
        let hull = convex_hull(&mut v);
        // should be just endpoints
        assert_eq!(hull, vec![pt(0, 0), pt(3, 3)]);
    }

    #[test]
    fn test_rectangle_and_duplicates() {
        // corners of a rectangle plus duplicate interior and duplicate corner
        let mut v = vec![
            pt(0, 0),
            pt(4, 0),
            pt(4, 3),
            pt(0, 3),
            pt(2, 1),
            pt(2, 1),
            pt(0, 0),
        ];
        let mut hull = convex_hull(&mut v);
        hull.sort_unstable();
        let mut want = vec![pt(0, 0), pt(4, 0), pt(4, 3), pt(0, 3)];
        want.sort_unstable();
        assert_eq!(hull, want);
    }

    #[test]
    fn test_concave_shape() {
        // a "U" shape: concave interior point should not appear
        let mut v = vec![
            pt(0, 0),
            pt(2, 0),
            pt(4, 0),
            pt(4, 2),
            pt(3, 2),
            pt(3, 1),
            pt(1, 1),
            pt(1, 2),
            pt(0, 2),
        ];
        let hull = convex_hull(&mut v);
        // should go around outer boundary (excluding the U bottom middle)
        let expected = vec![pt(0, 0), pt(4, 0), pt(4, 2), pt(0, 2)];
        assert_eq!(hull, expected);
    }

    #[test]
    fn test_random_points_inside_circle() {
        // generate points on circle plus random interior
        let mut pts = Vec::new();
        let n = 100;
        for i in 0..n {
            let theta = (i as f64) / (n as f64) * std::f64::consts::PI * 2.0;
            let x = (theta.cos() * 100.0).round() as i64;
            let y = (theta.sin() * 100.0).round() as i64;
            pts.push(pt(x, y));
        }
        // add some interior noise
        for &p in pts.clone().iter() {
            pts.push(pt(p.x / 2, p.y / 2));
        }
        let h = convex_hull(&mut pts);
        // direction count should be >= 8 (octagon approx) and <= n
        assert!(h.len() >= 8 && h.len() <= n);
        // all hull points must lie on the original circle set
        for &p in &h {
            assert!(pts.contains(&p));
        }
    }
}
