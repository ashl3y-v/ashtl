use std::{
    cmp::Ordering,
    ops::{Add, Mul, Sub},
};

use crate::geo::point::Point;

pub fn sort_angle<
    T: Clone + Default + PartialEq + PartialOrd + Sub<Output = T> + Mul<Output = T>,
>(
    vectors: &mut [Point<T>],
) {
    vectors.sort_by(|a, b| {
        let a_top = a.y > T::default() || (a.y == T::default() && a.x > T::default());
        let b_top = b.y > T::default() || (b.y == T::default() && b.x > T::default());
        if a_top != b_top {
            if a_top {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        } else {
            let cross = a.cross(b);
            if cross > T::default() {
                Ordering::Less
            } else if cross < T::default() {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
    });
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Angle {
    pub x: i64,
    pub y: i64,
    pub t: i64,
}

impl Angle {
    pub fn new(x: i64, y: i64, t: i64) -> Self {
        Self { x, y, t }
    }

    pub fn half(&self) -> bool {
        assert!(self.x != 0 || self.y != 0);
        if self.y < 0 || (self.y == 0 && self.x < 0) {
            true
        } else {
            false
        }
    }

    pub fn t90(&self) -> Self {
        Self {
            x: -self.y,
            y: self.x,
            t: self.t + if self.half() && self.x >= 0 { 1 } else { 0 },
        }
    }

    pub fn t180(&self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
            t: self.t + if self.half() { 1 } else { 0 },
        }
    }

    pub fn t360(&self) -> Self {
        Self {
            x: self.x,
            y: self.y,
            t: self.t + 1,
        }
    }

    pub fn segment_angles(mut self, mut rhs: Self) -> (Self, Self) {
        if rhs < self {
            std::mem::swap(&mut self, &mut rhs);
        }
        if rhs < self.t180() {
            (self, rhs)
        } else {
            (rhs, self.t360())
        }
    }

    pub fn angle_diff(mut self, rhs: Self) -> Self {
        let tu = rhs.t - self.t;
        self.t = rhs.t;
        let lt = if rhs < self { 1 } else { 0 };
        Angle {
            x: self.x * rhs.x + self.y * rhs.y,
            y: self.x * rhs.y - self.y * rhs.x,
            t: tu - lt,
        }
    }
}

impl Sub for Angle {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
            t: self.t,
        }
    }
}

impl PartialOrd for Angle {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Angle {
    fn cmp(&self, other: &Self) -> Ordering {
        let t_cmp = self.t.cmp(&other.t);
        if t_cmp != Ordering::Equal {
            return t_cmp;
        }
        let half_cmp = self.half().cmp(&other.half());
        if half_cmp != Ordering::Equal {
            return half_cmp;
        }
        let lhs = (self.y as i128) * (other.x as i128);
        let rhs = (self.x as i128) * (other.y as i128);
        lhs.cmp(&rhs)
    }
}

impl Add for Angle {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut r = Angle {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            t: self.t,
        };
        if self.t180() < r {
            r.t -= 1;
        }
        if r.t180() < self { r.t360() } else { r }
    }
}
