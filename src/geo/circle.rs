use crate::geo::point::Point;

#[derive(Clone)]
pub struct Circle<T> {
    pub center: Point<T>,
    pub radius: T,
}

pub fn circumcenter(a: Point<f64>, b: Point<f64>, c: Point<f64>) -> Point<f64> {
    let ax = b.x - a.x;
    let ay = b.y - a.y;
    let bx = c.x - a.x;
    let by = c.y - a.y;
    let d = 2.0 * (ax * by - ay * bx);
    let a2 = ax * ax + ay * ay;
    let b2 = bx * bx + by * by;
    Point::new(a.x + (by * a2 - ay * b2) / d, a.y + (ax * b2 - bx * a2) / d)
}
