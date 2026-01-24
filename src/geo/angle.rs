use std::{
    cmp::Ordering,
    ops::{Mul, Sub},
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
