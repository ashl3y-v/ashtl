use rand::seq::SliceRandom;

use crate::geo::circle::{Circle, circumcenter};
use crate::geo::point::Point;

/// O(n) ex.
pub fn min_enclosing_circle(mut pts: Vec<Point<f64>>) -> Circle<f64> {
    let n = pts.len();
    if n == 0 {
        return Circle {
            center: Point::new(0.0, 0.0),
            radius: 0.0,
        };
    }
    pts.shuffle(&mut rand::rng());
    let mut boundary: Vec<Point<_>> = Vec::with_capacity(3);
    fn trivial(boundary: &[Point<f64>]) -> Circle<f64> {
        match boundary.len() {
            0 => Circle {
                center: Point::new(0.0, 0.0),
                radius: 0.0,
            },
            1 => Circle {
                center: boundary[0],
                radius: 0.0,
            },
            2 => {
                let c = Point::new(
                    (boundary[0].x + boundary[1].x) * 0.5,
                    (boundary[0].y + boundary[1].y) * 0.5,
                );
                Circle {
                    center: c,
                    radius: boundary[0].dist_to(c),
                }
            }
            _ => {
                let c = circumcenter(boundary[0], boundary[1], boundary[2]);
                Circle {
                    center: c,
                    radius: boundary[0].dist_to(c),
                }
            }
        }
    }
    fn welzl(pts: &[Point<f64>], n: usize, boundary: &mut Vec<Point<f64>>) -> Circle<f64> {
        if n == 0 || boundary.len() == 3 {
            return trivial(boundary);
        }
        let c = welzl(pts, n - 1, boundary);
        let p = pts[n - 1];
        if p.dist_to(c.center) <= c.radius + 1e-12 {
            return c;
        }
        boundary.push(p);
        let c = welzl(pts, n - 1, boundary);
        boundary.pop();
        c
    }
    welzl(&pts, n, &mut boundary)
}
