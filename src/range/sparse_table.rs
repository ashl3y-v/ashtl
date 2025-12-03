use std::{
    mem::MaybeUninit,
    ops::{Bound, RangeBounds},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseTable<T, F: FnMut(&T, &T) -> T> {
    pub n: usize,
    pub t: Vec<T>,
    pub f: F,
}

impl<T: Clone, F: FnMut(&T, &T) -> T> SparseTable<T, F> {
    pub fn new(a: Vec<T>, mut f: F) -> Self {
        let n = a.len();
        let l = if n == 0 { 0 } else { n.ilog2() as usize + 1 };
        let mut t: Vec<MaybeUninit<T>> = Vec::with_capacity(n * l);
        unsafe {
            t.set_len(n * l);
        }
        for (i, v) in a.into_iter().enumerate() {
            t[i].write(v);
        }
        let mut i = 1;
        let mut p = 2;
        while p <= n {
            let off = i * n;
            for j in 0..=n - p {
                let r = f(unsafe { t[(i - 1) * n + j].assume_init_ref() }, unsafe {
                    t[(i - 1) * n + j + (p >> 1)].assume_init_ref()
                });
                t[off + j].write(r);
            }
            i += 1;
            p <<= 1;
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(t) };
        Self { n, t, f }
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
        debug_assert!(l < r);
        debug_assert!(r <= self.n);
        let n = self.n;
        let i = (r - l).ilog2() as usize;
        (self.f)(&self.t[i * n + l], &self.t[i * n + r - (1 << i)])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisjointSparseTable<T, F> {
    pub n: usize,
    pub t: Vec<T>,
    pub f: F,
}

impl<T: Clone + std::fmt::Debug, F> DisjointSparseTable<T, F>
where
    F: FnMut(&T, &T) -> T,
{
    pub fn new(a: Vec<T>, mut f: F) -> Self {
        let n = a.len();
        let l = if n == 0 { 0 } else { n.ilog2() as usize + 1 };
        let total = n * l;
        let mut buf: Vec<MaybeUninit<T>> = Vec::with_capacity(total);
        unsafe {
            buf.set_len(total);
        }
        for h in 0..l {
            let l = 1 << h;
            let mut c = l;
            while c < n + l {
                if c < n {
                    buf[h * n + c].write(a[c].clone());
                }
                if c - 1 < n {
                    buf[h * n + c - 1].write(a[c - 1].clone());
                }
                for i in (c + 1)..n.min(c + l) {
                    let prev_val = unsafe { buf[h * n + i - 1].assume_init_ref() };
                    let curr_val = &a[i];
                    let result = f(prev_val, curr_val);
                    buf[h * n + i].write(result);
                }
                for i in (c - l..n.min(c - 1)).rev() {
                    let curr_val = &a[i];
                    let next_val = unsafe { buf[h * n + i + 1].assume_init_ref() };
                    let result = f(curr_val, next_val);
                    buf[h * n + i].write(result);
                }
                c += l << 1;
            }
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(buf) };
        Self { n, t, f }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> T {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r,
            Bound::Excluded(r) => *r - 1,
            Bound::Unbounded => self.n - 1,
        };
        debug_assert!(l <= r);
        debug_assert!(r < self.n);
        if l == r {
            return self.t[l].clone();
        }
        let n = self.n;
        let h = (l ^ r).ilog2() as usize;
        (self.f)(&self.t[h * n + l], &self.t[h * n + r])
    }
}

// TODO: xor disjoint sparse table
// https://maspypy.github.io/library/ds/sparse_table/xor_disjoint_sparse_table.hpp

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_query() {
        let arr = vec![1, 3, 2, 7, 9, 11];
        let mut dst = SparseTable::new(arr, |a, b| *a.max(b));

        assert_eq!(dst.query(1..=3), 7);
        assert_eq!(dst.query(0..=2), 3);
        assert_eq!(dst.query(3..=5), 11);
    }

    #[test]
    fn test_with_stored_function() {
        let arr = vec![1, 3, 2, 7, 9, 11];
        let mut dst = SparseTable::new(arr, |a, b| *a.max(b));

        assert_eq!(dst.query(1..=3), 7);
        assert_eq!(dst.query(0..=2), 3);
        assert_eq!(dst.query(3..=5), 11);
    }

    #[test]
    fn test_sum_query_disjoint() {
        let arr = vec![1, 3, 2, 7, 9, 11];
        let mut dst = DisjointSparseTable::new(arr, |a, b| a + b);

        assert_eq!(dst.query(1..=3), 12); // 3 + 2 + 7 = 12
        assert_eq!(dst.query(0..=2), 6); // 1 + 3 + 2 = 6
        assert_eq!(dst.query(3..=5), 27); // 7 + 9 + 11 = 27
    }

    #[test]
    fn test_with_stored_function_disjoint() {
        let arr = vec![1, 3, 2, 7, 9, 11];
        let mut dst = DisjointSparseTable::new(arr, |a: &i32, b: &i32| a + b);

        assert_eq!(dst.query(1..=3), 12); // 3 + 2 + 7 = 12
        assert_eq!(dst.query(0..=2), 6); // 1 + 3 + 2 = 6
        assert_eq!(dst.query(3..=5), 27); // 7 + 9 + 11 = 27
    }
}
