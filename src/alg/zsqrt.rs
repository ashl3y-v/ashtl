use super::ops::inverse_euclidean;
use std::{
    fmt::Debug,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub},
};

type E = i128;

#[derive(Clone, Copy)]
pub struct ZSqrt<const M: u64, const D: E> {
    pub a: E,
    pub b: E,
}

impl<const M: u64, const D: E> ZSqrt<M, D> {
    pub fn new(a: E, b: E) -> Self {
        ZSqrt { a, b }
    }

    pub fn conj(self) -> Self {
        let ZSqrt { a, b } = self;
        ZSqrt { a, b: -b }
    }

    pub fn norm(self) -> E {
        let ZSqrt { a, b } = self;
        (a * a % M as E - b * b % M as E * D as E % M as E) % M as E
    }

    pub fn inv(self) -> Self {
        self.conj() / self.norm()
    }

    pub fn normalize(self) -> Self {
        let ZSqrt { a, b } = self;
        ZSqrt::new(a % M as E, b % M as E)
    }

    pub fn pos_normalize(self) -> Self {
        let ZSqrt { a, b } = self;
        ZSqrt::new(a.rem_euclid(M as E), b.rem_euclid(M as E))
    }

    /// O(log n)
    pub fn pow(mut self, mut n: u64) -> Self {
        let mut ak = ZSqrt::new(1, 0);
        while n != 0 {
            if n & 1 != 0 {
                ak = ak * self;
            }
            self = self * self;
            n >>= 1;
        }
        ak
    }
}

impl<const M: u64, const D: E> Debug for ZSqrt<M, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} + {} √{}", self.a, self.b, D))
    }
}

impl<const M: u64, const D: E> Add<Self> for ZSqrt<M, D> {
    type Output = Self;

    fn add(self, ZSqrt { a: c, b: d }: Self) -> Self::Output {
        let ZSqrt { a, b } = self;
        ZSqrt::new(a + c % M as E, b + d % M as E)
    }
}

impl<const M: u64, const D: E> AddAssign<Self> for ZSqrt<M, D> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const M: u64, const D: E> Sub<Self> for ZSqrt<M, D> {
    type Output = Self;

    fn sub(self, ZSqrt { a: c, b: d }: Self) -> Self::Output {
        let ZSqrt { a, b } = self;
        ZSqrt::new(a - c % M as E, b - d % M as E)
    }
}

impl<const M: u64, const D: E> Mul<Self> for ZSqrt<M, D> {
    type Output = Self;

    fn mul(self, ZSqrt { a: c, b: d }: Self) -> Self::Output {
        let ZSqrt { a, b } = self;
        ZSqrt::new(
            (a * c % M as E + d * b % M as E * D as E % M as E) % M as E,
            (b * c % M as E + a * d % M as E) % M as E,
        )
    }
}

impl<const M: u64, const D: E> MulAssign for ZSqrt<M, D> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<const M: u64, const D: E> Mul<E> for ZSqrt<M, D> {
    type Output = Self;

    fn mul(self, rhs: E) -> Self::Output {
        let ZSqrt { a, b } = self;
        ZSqrt::new(a * rhs % M as E, b * rhs % M as E)
    }
}

impl<const M: u64, const D: E> MulAssign<E> for ZSqrt<M, D> {
    fn mul_assign(&mut self, rhs: E) {
        *self = *self * rhs
    }
}

impl<const M: u64, const D: E> Div<E> for ZSqrt<M, D> {
    type Output = Self;

    fn div(self, rhs: E) -> Self::Output {
        self * inverse_euclidean::<M, _>(rhs)
    }
}

impl<const M: u64, const D: E> DivAssign<E> for ZSqrt<M, D> {
    fn div_assign(&mut self, rhs: E) {
        *self = *self / rhs;
    }
}
