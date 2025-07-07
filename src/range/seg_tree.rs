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

    pub fn update<R>(
        &mut self,
        range: impl RangeBounds<usize>,
        mut left: impl FnMut(usize, usize, &mut [T], &mut R),
        mut right: impl FnMut(usize, usize, &mut [T], &mut R),
        data: &mut R,
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
                left(l, k, &mut self.t, data);
                cl = true;
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                right(r, k, &mut self.t, data);
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

    pub fn query<R>(
        &mut self,
        range: impl RangeBounds<usize>,
        data: &mut R,
        mut left: impl FnMut(usize, usize, &mut [T], &mut R),
        mut right: impl FnMut(usize, usize, &mut [T], &mut R),
    ) {
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
        let mut k = 1;
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                left(l, k, &mut self.t, data);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                right(r, k, &mut self.t, data);
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
    }

    pub fn descend<S>(
        &mut self,
        mut right: impl FnMut(usize, usize, &mut [T]) -> bool,
        mut leaf: impl FnMut(usize, &mut [T]) -> S,
    ) -> S {
        let mut i = 1;
        let mut k = self.n;
        while i < self.n {
            (self.push)(i, k, &mut self.t);
            i = (i >> 1) | right(i, k, &mut self.t) as usize;
            k >>= 1;
        }
        leaf(i, &mut self.t)
    }

    pub fn traverse<S: ?Sized, R>(
        &mut self,
        data: &S,
        mut quit: impl FnMut(usize, usize, usize, usize, &S, &mut [T]) -> Option<R>,
        mut rec: impl FnMut(usize, usize, &S, &mut [T], R, R, &mut Push) -> R,
    ) -> R {
        self.traverse_descend(1, self.n, 0, self.n, data, &mut quit, &mut rec)
    }

    fn traverse_descend<S: ?Sized, R>(
        &mut self,
        i: usize,
        k: usize,
        il: usize,
        ir: usize,
        data: &S,
        quit: &mut impl FnMut(usize, usize, usize, usize, &S, &mut [T]) -> Option<R>,
        rec: &mut impl FnMut(usize, usize, &S, &mut [T], R, R, &mut Push) -> R,
    ) -> R {
        if let Some(v) = quit(i, k, il, ir, data, &mut self.t) {
            return v;
        }
        (self.push)(i, k, &mut self.t);
        let im = il + (ir - il >> 1);
        let v = self.traverse_descend(i << 1, k >> 1, il, im, data, quit, rec);
        let w = self.traverse_descend(i << 1 | 1, k >> 1, im, ir, data, quit, rec);
        rec(i, k, data, &mut self.t, v, w, &mut self.push)
    }

    pub fn max_right<S, P>(
        &mut self,
        l: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(&S, &T) -> S,
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
            let combined = (op)(&acc, &self.t[i]);
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, 1 << k, &mut self.t);
                    i <<= 1;
                    k -= 1;
                    let cand = (op)(&acc, &self.t[i]);
                    if p(&cand) {
                        acc = cand;
                        i += 1;
                    }
                }
                break i - self.n;
            }
            acc = combined;
            i += 1;
            if i.is_power_of_two() {
                break self.n;
            }
        }
    }

    pub fn min_left<S, P>(
        &mut self,
        r: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(&T, &S) -> S,
    ) -> usize
    where
        S: Clone,
        P: FnMut(&S) -> bool,
    {
        if r == 0 {
            return 0;
        }
        self.push(r - 1, r);
        let mut acc = init;
        let mut i = r + self.n;
        let mut k = 0;
        loop {
            i -= 1;
            while i > 1 && i & 1 == 1 {
                i >>= 1;
                k += 1;
            }
            let combined = (op)(&self.t[i], &acc);
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, k, &mut self.t);
                    i = i << 1 | 1;
                    k -= 1;
                    let cand = (op)(&self.t[i], &acc);
                    if p(&cand) {
                        acc = cand;
                        i -= 1;
                    }
                }
                break i + 1 - self.n;
            }
            acc = combined;
            if i.is_power_of_two() {
                break 0;
            }
        }
    }

    pub fn n(&self) -> usize {
        self.n
    }
}

// TODO: wide segment tree
// https://judge.yosupo.jp/submission/254992
// https://en.algorithmica.org/hpc/data-structures/segment-trees/
