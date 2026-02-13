pub trait Monoid {
    type S: Clone + Copy;
    fn id() -> Self::S;
    fn op(a: &Self::S, b: &Self::S) -> Self::S;
}

pub fn monoid_pow<M: Monoid>(mut base: M::S, mut exp: u64) -> M::S {
    let mut res = M::id();
    while exp > 0 {
        if exp & 1 == 1 {
            res = M::op(&res, &base);
        }
        base = M::op(&base, &base);
        exp >>= 1;
    }
    res
}

pub trait Group {
    type T: Clone + Copy + PartialEq;

    fn identity() -> Self::T;
    fn op(x: &Self::T, y: &Self::T) -> Self::T;
    fn inverse(x: &Self::T) -> Self::T;
}
