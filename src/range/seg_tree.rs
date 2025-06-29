use bit_vec::BitVec;
use std::{
    mem::MaybeUninit,
    ops::{Bound, RangeBounds},
};

pub struct SegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, &mut [T]),
    Push: FnMut(usize, usize, &mut [T]),
{
    pub n: usize,
    pub t: Vec<T>,
    pub pull: Pull,
    pub push: Push,
}

impl<T, Pull, Push> SegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, &mut [T]),
    Push: FnMut(usize, usize, &mut [T]),
    T: std::fmt::Debug,
{
    pub fn new<Init: FnMut(usize, usize, &mut [T])>(
        a: Vec<T>,
        mut init: Init,
        pull: Pull,
        push: Push,
    ) -> Self {
        let n = a.len();
        let total = n << 1;
        let mut buf: Vec<MaybeUninit<T>> = Vec::with_capacity(total);
        unsafe {
            buf.set_len(total);
        }
        for (i, v) in a.into_iter().enumerate() {
            buf[n + i].write(v);
        }
        let mut l = n;
        let mut r = total - 1;
        let mut k = 2;
        while l > 1 {
            l >>= 1;
            r >>= 1;
            for p in (l..=r).rev() {
                (init)(p, k, unsafe {
                    std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut T, total)
                });
            }
            k <<= 1;
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(buf) };
        SegTree { n, t, pull, push }
    }

    pub fn build(&mut self, mut l: usize, mut r: usize) -> &mut Self {
        let mut k = 2;
        l += self.n;
        r += self.n - 1;
        while l > 1 {
            l >>= 1;
            r >>= 1;
            for i in (l..=r).rev() {
                (self.pull)(i, k, &mut self.t);
            }
            k <<= 1;
        }
        self
    }

    pub fn push(&mut self, mut l: usize, mut r: usize) -> &mut Self {
        let h = self.n.ilog2();
        let mut s = h;
        let mut k = 1 << h;
        l += self.n;
        r += self.n - 1;
        while s > 0 {
            for i in l >> s..=r >> s {
                (self.push)(i, k, &mut self.t);
            }
            s -= 1;
            k >>= 1;
        }
        self
    }

    pub fn update(
        &mut self,
        range: impl RangeBounds<usize>,
        mut update: impl FnMut(usize, usize, &mut [T]),
    ) -> &mut Self {
        let mut l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let mut r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        self.push(l, l + 1);
        self.push(r - 1, r);
        let (mut cl, mut cr) = (false, false);
        let mut k = 1;
        l += self.n;
        r += self.n;
        while l < r {
            if cl {
                (self.pull)(l - 1, k, &mut self.t)
            };
            if cr {
                (self.pull)(r, k, &mut self.t)
            };
            if l & 1 != 0 {
                update(l, k, &mut self.t);
                cl = true;
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                update(r, k, &mut self.t);
                cr = true;
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
        l -= 1;
        while r > 0 {
            if cl {
                (self.pull)(l, k, &mut self.t)
            };
            if cr && (!cl || l != r) {
                (self.pull)(r, k, &mut self.t);
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
        self
    }

    pub fn query<S>(
        &mut self,
        range: impl RangeBounds<usize>,
        init_l: S,
        init_r: S,
        mut op_l: impl FnMut(S, &T) -> S,
        mut op_r: impl FnMut(&T, S) -> S,
        mut op_s: impl FnMut(S, S) -> S,
    ) -> S {
        let mut l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let mut r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        self.push(l, l + 1);
        if r > 0 {
            self.push(r - 1, r);
        }
        let mut res_l = init_l;
        let mut res_r = init_r;
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                res_l = (op_l)(res_l, &self.t[l]);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res_r = (op_r)(&self.t[r], res_r);
            }
            l >>= 1;
            r >>= 1;
        }
        op_s(res_l, res_r)
    }

    // O(log n)
    // array must be length 2^k
    pub fn max_right<S, P>(
        &mut self,
        l: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(S, &T) -> S,
    ) -> usize
    where
        S: Clone,
        P: FnMut(&S) -> bool,
    {
        if l == self.n {
            return self.n;
        }
        self.push(l, l + 1);
        let mut acc = init;
        let mut i = l + self.n;
        let mut k = 0;
        loop {
            while i & 1 == 0 {
                i >>= 1;
                k += 1;
            }
            let combined = (op)(acc.clone(), &self.t[i]);
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, 1 << k, &mut self.t);
                    i <<= 1;
                    k -= 1;
                    let cand = (op)(acc.clone(), &self.t[i]);
                    if p(&cand) {
                        acc = cand;
                        i += 1;
                    }
                }
                return i - self.n;
            }
            acc = combined;
            i += 1;
            if i.is_power_of_two() {
                break;
            }
        }
        self.n
    }

    // O(log n)
    // array must be length 2^k
    pub fn min_left<S, P>(
        &mut self,
        r: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(&T, S) -> S,
    ) -> usize
    where
        S: Clone,
        P: FnMut(&S) -> bool,
    {
        if r == 0 {
            return 0;
        }
        self.push(r, r + 1);
        let mut acc = init;
        let mut i = r + self.n;
        let mut k = 0;
        loop {
            i -= 1;
            while i > 1 && i & 1 == 1 {
                i >>= 1;
                k += 1;
            }
            let combined = (op)(&self.t[i], acc.clone());
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, k, &mut self.t);
                    i = i << 1 | 1;
                    k -= 1;
                    let cand = (op)(&self.t[i], acc.clone());
                    if p(&cand) {
                        acc = cand;
                        i -= 1;
                    }
                }
                return i + 1 - self.n;
            }
            acc = combined;
            if i.is_power_of_two() {
                break;
            }
        }
        0
    }
}

pub struct BitSegTree<F: FnMut(bool, bool) -> bool> {
    pub n: usize,
    pub st: BitVec,
    pub op: F,
}

impl<F: FnMut(bool, bool) -> bool> BitSegTree<F> {
    /// preconditions: n = 2^k
    pub fn new(n: usize, init: bool, op: F) -> Self {
        Self {
            n,
            st: BitVec::from_elem(n << 1, init),
            op,
        }
    }

    /// preconditions: op == &&
    pub fn first_zero(&self) -> Option<usize> {
        if !self.st[1] {
            return None;
        }
        let mut i = 1;
        while i < self.n {
            i = (i << 1) | self.st[i << 1] as usize;
        }
        Some(i - self.n)
    }

    /// preconditions: op == ||
    pub fn first_one(&self) -> Option<usize> {
        if !self.st[1] {
            return None;
        }
        let mut i = 1;
        while i < self.n {
            i = (i << 1) | !self.st[i << 1] as usize;
        }
        Some(i - self.n)
    }

    pub fn update(&mut self, mut i: usize, v: bool) {
        i += self.n;
        self.st.set(i, v);
        while i > 1 {
            i >>= 1;
            self.st
                .set(i, (self.op)(self.st[i << 1], self.st[i << 1 | 1]));
        }
    }
}
