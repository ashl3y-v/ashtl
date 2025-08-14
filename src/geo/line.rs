use std::ops::{Add, Mul};

pub struct Line<T> {
    m: T,
    b: T,
}

pub trait Eval<T> {
    fn eval(&self, x: T) -> T;
}

impl<T: Copy + Add<T, Output = T> + Mul<T, Output = T>> Eval<T> for Line<T> {
    fn eval(&self, x: T) -> T {
        self.m * x + self.b
    }
}
