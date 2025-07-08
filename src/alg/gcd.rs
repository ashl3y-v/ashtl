use std::ops::{Div, Mul, Rem};

#[inline]
pub fn gcd<T>(mut a: T, mut b: T) -> T
where
    T: Copy + Default + PartialEq + Rem<Output = T>,
{
    while b != T::default() {
        (a, b) = (b, a % b);
    }
    a
}

#[inline]
pub fn lcm<T>(a: T, b: T) -> T
where
    T: Copy + Default + PartialEq + Mul<Output = T> + Div<Output = T> + Rem<Output = T>,
{
    let d = gcd(a, b);
    if d == T::default() {
        T::default()
    } else {
        a * b / d
    }
}

pub const fn euclidean(a: i128, b: i128) -> (i128, i128, i128) {
    let (mut r0, mut r1) = (a.abs(), b.abs());
    let (mut s0, mut s1) = (1, 0);
    let (mut t0, mut t1) = (0, 1);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    let (s0, t0) = match (a < 0, b < 0) {
        (true, true) => (-s0, -t0),
        (true, false) => (-s0, t0),
        (false, true) => (s0, -t0),
        (false, false) => (s0, t0),
    };
    (r0, s0, t0)
}
