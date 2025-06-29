use std::ops::{Bound, RangeBounds};

pub struct SparseTable<T, F: FnMut(&T, &T) -> T> {
    n: usize,
    st: Vec<T>,
    f: F,
}

impl<T: Clone, F: FnMut(&T, &T) -> T> SparseTable<T, F> {
    pub fn new(mut st: Vec<T>, mut f: F) -> Self {
        let n = st.len();
        st.resize(n * (n.ilog2() as usize + 1), st[0].clone());
        let mut i = 1;
        let mut p = 2;
        while p < n {
            for j in 0..=n - p {
                st[i * n + j] = f(&st[(i - 1) * n + j], &st[(i - 1) * n + j + (p >> 1)]);
            }
            p <<= 1;
            i += 1;
        }

        Self { n, st, f }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> T {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        let n = self.n;
        let i = (r - l).ilog2() as usize;
        (self.f)(&self.st[i * n + l], &self.st[i * n + r - (1 << i)])
    }
}
