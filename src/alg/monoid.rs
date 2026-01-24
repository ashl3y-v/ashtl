pub trait Monoid {
    type S: Clone + Copy;
    fn id() -> Self::S;
    fn op(a: &Self::S, b: &Self::S) -> Self::S;
}
