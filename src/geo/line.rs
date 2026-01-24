use std::ops::{Add, Mul};

use crate::tree::li_chao::LiChaoFunc;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Line<T> {
    m: T,
    b: T,
}

impl<T> Line<T> {
    pub fn new(m: T, b: T) -> Self {
        Self { m, b }
    }
}

pub trait Eval<T> {
    fn eval(&self, x: T) -> T;
}

impl<T: Copy + Add<T, Output = T> + Mul<T, Output = T>> Eval<T> for Line<T> {
    fn eval(&self, x: T) -> T {
        self.m * x + self.b
    }
}

impl LiChaoFunc for Line<i64> {
    #[inline(always)]
    fn eval(&self, x: i64) -> i64 {
        if self.b == i64::MAX {
            i64::MAX
        } else {
            self.m.wrapping_mul(x).wrapping_add(self.b)
        }
    }

    fn max() -> Self {
        Self { m: 0, b: i64::MAX }
    }
}
