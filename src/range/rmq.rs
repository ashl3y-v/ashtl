use std::{
    cmp::Ordering,
    ops::{Bound, RangeBounds},
};

type E = u64;
const B: usize = E::BITS as usize;

pub struct RMQ<F: FnMut(usize, usize) -> Ordering> {
    n: usize,
    f: F,
    mask: Vec<E>,
    st: Vec<usize>,
}

impl<F: FnMut(usize, usize) -> Ordering> RMQ<F> {
    pub fn new(n: usize, mut f: F) -> Self {
        let mut curr_mask: E = 0;
        let mut mask = Vec::with_capacity(n);
        for i in 0..n {
            curr_mask = curr_mask << 1;
            while curr_mask != 0 && f(i, i - curr_mask.trailing_zeros() as usize).is_lt() {
                curr_mask &= curr_mask - 1;
            }
            curr_mask |= 1;
            mask.push(curr_mask);
        }
        let n_b_log = (n / B).checked_ilog2().unwrap_or_default() as usize;
        let st_size = (n / B) * (n_b_log + 1);
        let mut st = Vec::with_capacity(st_size);
        st.extend((0..n / B).map(|i| i * B + B - 1 - mask[i * B + B - 1].ilog2() as usize));
        st.resize(st_size, 0);
        let mut min = |i, j| if f(i, j).is_le() { i } else { j };
        for i in 1..=n_b_log {
            for j in 0..=n / B - (1 << i) {
                st[i * n / B + j] = min(
                    st[(i - 1) * n / B + j],
                    st[(i - 1) * n / B + j + (1 << i - 1)],
                )
            }
        }
        Self { n, f, mask, st }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> usize {
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
        let n = self.n;
        match (r - l + 1).cmp(&B) {
            Ordering::Less => {
                return r - (self.mask[r] & ((1 << r - l + 1) - 1)).ilog2() as usize;
            }
            Ordering::Equal => return r - self.mask[r].ilog2() as usize,
            _ => (),
        }
        let mut min = |i, j| if (self.f)(i, j).is_le() { i } else { j };
        let mut ans = min(
            l + B - 1 - self.mask[l + B - 1].ilog2() as usize,
            r - self.mask[r].ilog2() as usize,
        );
        let (x, y) = (l / B + 1, r / B - 1);
        if x <= y {
            let i = (y - x + 1).ilog2() as usize;
            let q = min(
                self.st[i * n / B + x],
                self.st[i * n / B + y - (1 << i) + 1],
            );
            ans = min(ans, q);
        }

        ans
    }
}
