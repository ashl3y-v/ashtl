pub trait Monoid {
    type S: Clone + Copy;
    fn id() -> Self::S;
    fn op(a: &Self::S, b: &Self::S) -> Self::S;
}

pub trait Group {
    type T: Clone + Copy + PartialEq;

    fn identity() -> Self::T;
    fn op(x: &Self::T, y: &Self::T) -> Self::T;
    fn inverse(x: &Self::T) -> Self::T;
}
