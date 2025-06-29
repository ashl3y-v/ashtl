use std::ops::{Rem, Shr, Sub};

pub fn gcd<T>(mut a: T, mut b: T) -> T
where
    T: Copy
        + Default
        + PartialEq
        + PartialOrd
        + Sub<Output = T>
        + Shr<u32, Output = T>
        + Rem<Output = T>,
{
    while b != T::default() {
        (a, b) = (b, a % b);
    }
    a
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
    let (s0, t0) = if a < 0 && b < 0 {
        (-s0, -t0)
    } else if a < 0 {
        (-s0, t0)
    } else if b < 0 {
        (s0, -t0)
    } else {
        (s0, t0)
    };
    (r0, s0, t0)
}
