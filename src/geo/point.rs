use std::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

impl<T> Point<T> {
    pub fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
}

impl<T: Display> Debug for Point<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "⟨{}, {}⟩", self.x, self.y)
    }
}

impl<S, R: Add<Output = S>, T: Clone + Mul<Output = R>> Point<T> {
    pub fn dot(&self, rhs: &Point<T>) -> S {
        self.x.clone() * rhs.x.clone() + self.y.clone() * rhs.y.clone()
    }
}

impl<S, R: Sub<Output = S>, T: Clone + Mul<Output = R> + Sub<Output = T>> Point<T> {
    pub fn cross(&self, rhs: &Point<T>) -> S {
        self.x.clone() * rhs.y.clone() - self.y.clone() * rhs.x.clone()
    }
}

impl<S, R: Sub<Output = S>, T: Clone + Mul<Output = R> + Sub<Output = T>> Point<T> {
    pub fn area(&self, a: &Point<T>, b: &Point<T>) -> S {
        (a.clone() - self.clone()).cross(&(b.clone() - self.clone()))
    }
}

impl<S, R: Add<Output = S>, T: Clone + Mul<Output = R> + Sub<Output = T>> Point<T> {
    pub fn dist2(self) -> S {
        self.x.clone() * self.x + self.y.clone() * self.y
    }
}

impl Point<f32> {
    pub fn dist(&self) -> f32 {
        self.dist2().sqrt()
    }
}

impl Point<f64> {
    pub fn dist(&self) -> f64 {
        self.dist2().sqrt()
    }
}

impl Point<f32> {
    pub fn dist_to(&self, rhs: Self) -> f32 {
        (rhs - *self).dist2().sqrt()
    }
}

impl Point<f64> {
    pub fn dist_to(&self, rhs: Self) -> f64 {
        (rhs - *self).dist2().sqrt()
    }
}

impl Point<f32> {
    pub fn angle(&self) -> f32 {
        f32::atan2(self.y, self.x)
    }
}

impl Point<f64> {
    pub fn angle(&self) -> f64 {
        f64::atan2(self.y, self.x)
    }
}

impl Point<f32> {
    pub fn unit(self) -> Point<f32> {
        self / self.dist()
    }
}

impl Point<f64> {
    pub fn unit(self) -> Point<f64> {
        self / self.dist()
    }
}

impl<T: Clone + Neg<Output = T>> Point<T> {
    pub fn perp(&self) -> Self {
        Point {
            x: -self.y.clone(),
            y: self.x.clone(),
        }
    }
}

impl<T: Clone> Point<T> {
    pub fn flip(&self) -> Self {
        Point {
            x: self.y.clone(),
            y: self.x.clone(),
        }
    }
}

impl Point<f32> {
    pub fn normal(self) -> Point<f32> {
        self.perp().unit()
    }
}

impl Point<f64> {
    pub fn normal(self) -> Point<f64> {
        self.perp().unit()
    }
}

impl Point<f32> {
    pub fn rotate(self, a: f32) -> Point<f32> {
        Point {
            x: self.x * a.cos() - self.y * a.sin(),
            y: self.x * a.sin() + self.y * a.cos(),
        }
    }
}

impl Point<f64> {
    pub fn rotate(self, a: f64) -> Point<f64> {
        Point {
            x: self.x * a.cos() - self.y * a.sin(),
            y: self.x * a.sin() + self.y * a.cos(),
        }
    }
}

impl<R, S, T: Add<S, Output = R>> Add<Point<S>> for Point<T> {
    type Output = Point<R>;

    fn add(self, rhs: Point<S>) -> Self::Output {
        Point {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<S, T: AddAssign<S>> AddAssign<Point<S>> for Point<T> {
    fn add_assign(&mut self, rhs: Point<S>) {
        self.x += rhs.x;
        self.y += rhs.y;
    }
}

impl<R, S, T: Sub<S, Output = R>> Sub<Point<S>> for Point<T> {
    type Output = Point<R>;

    fn sub(self, rhs: Point<S>) -> Self::Output {
        Point {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<S, T: SubAssign<S>> SubAssign<Point<S>> for Point<T> {
    fn sub_assign(&mut self, rhs: Point<S>) {
        self.x -= rhs.x;
        self.y -= rhs.y;
    }
}

impl<R, S: Clone, T: Mul<S, Output = R>> Mul<S> for Point<T> {
    type Output = Point<R>;

    fn mul(self, rhs: S) -> Self::Output {
        Point {
            x: self.x * rhs.clone(),
            y: self.y * rhs,
        }
    }
}

impl<S: Clone, T: MulAssign<S>> MulAssign<S> for Point<T> {
    fn mul_assign(&mut self, rhs: S) {
        self.x *= rhs.clone();
        self.y *= rhs;
    }
}

impl<R, S: Clone, T: Div<S, Output = R>> Div<S> for Point<T> {
    type Output = Point<R>;

    fn div(self, rhs: S) -> Self::Output {
        Point {
            x: self.x / rhs.clone(),
            y: self.y / rhs,
        }
    }
}

impl<S: Clone, T: DivAssign<S>> DivAssign<S> for Point<T> {
    fn div_assign(&mut self, rhs: S) {
        self.x /= rhs.clone();
        self.y /= rhs;
    }
}
