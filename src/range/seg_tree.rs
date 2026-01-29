use std::{
    mem::MaybeUninit,
    ops::{Bound, RangeBounds},
};

pub struct SegTree<T, Pull>
where
    Pull: FnMut(usize, &mut [T]),
{
    pub n: usize,
    pub t: Vec<T>,
    pub pull: Pull,
}

impl<T, Pull> SegTree<T, Pull>
where
    Pull: FnMut(usize, &mut [T]),
{
    pub fn new<Init: FnMut(usize, &mut [T])>(a: Vec<T>, mut init: Init, pull: Pull) -> Self {
        let n = a.len();
        let total = n << 1;
        let mut buf: Vec<MaybeUninit<T>> = Vec::with_capacity(total);
        unsafe {
            buf.set_len(total);
        }
        for (i, v) in a.into_iter().enumerate() {
            buf[n + i].write(v);
        }
        for p in (1..n).rev() {
            (init)(p, unsafe {
                std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut T, total)
            });
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(buf) };
        Self { n, t, pull }
    }

    pub fn set(&mut self, mut i: usize, val: T) -> &mut Self {
        i += self.n;
        self.t[i] = val;
        while i > 1 {
            (self.pull)(i >> 1, &mut self.t);
            i >>= 1;
        }
        self
    }

    pub fn update(
        &mut self,
        mut l: usize,
        mut r: usize,
        mut visit: impl FnMut(usize, bool, &mut [T]),
    ) -> &mut Self {
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                visit(l, false, &mut self.t);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                visit(r, true, &mut self.t);
            }
            l >>= 1;
            r >>= 1;
        }
        self
    }

    pub fn query(
        &mut self,
        mut l: usize,
        mut r: usize,
        mut visit: impl FnMut(usize, bool, &mut [T]),
    ) {
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                visit(l, false, &mut self.t);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                visit(r, true, &mut self.t);
            }
            l >>= 1;
            r >>= 1;
        }
    }

    pub fn get(&mut self, mut i: usize, mut visit: impl FnMut(usize, &mut [T])) {
        i += self.n;
        while i > 0 {
            visit(i, &mut self.t);
            i >>= 1;
        }
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
        let mut acc = init;
        let mut i = l + self.n;
        loop {
            while i & 1 == 0 {
                i >>= 1;
            }
            let combined = (op)(&acc, &self.t[i]);
            if !p(&combined) {
                while i < self.n {
                    i <<= 1;
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
        let mut acc = init;
        let mut i = r + self.n;
        loop {
            i -= 1;
            while i > 1 && i & 1 == 1 {
                i >>= 1;
            }
            let combined = (op)(&self.t[i], &acc);
            if !p(&combined) {
                while i < self.n {
                    i = i << 1 | 1;
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
}

pub struct LazySegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, &mut [T]),
    Push: FnMut(usize, usize, &mut [T]),
{
    pub n: usize,
    pub t: Vec<T>,
    pub pull: Pull,
    pub push: Push,
}

impl<T, Pull, Push> LazySegTree<T, Pull, Push>
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
        Self { n, t, pull, push }
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
        mut l: usize,
        mut r: usize,
        mut visit: impl FnMut(usize, bool, usize, &mut [T]),
    ) -> &mut Self {
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
                visit(l, false, k, &mut self.t);
                cl = true;
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                visit(r, true, k, &mut self.t);
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

    pub fn query(
        &mut self,
        mut l: usize,
        mut r: usize,
        mut visit: impl FnMut(usize, bool, usize, &mut [T]),
    ) {
        self.push(l, l + 1);
        if r > 0 {
            self.push(r - 1, r);
        }
        let mut k = 1;
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                visit(l, false, k, &mut self.t);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                visit(r, true, k, &mut self.t);
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
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
}

#[derive(Clone, Default, Debug)]
pub struct SparseSegTreeNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
}

pub struct SparseSegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, usize, &mut [SparseSegTreeNode<T>]),
    Push: FnMut(usize, usize, usize, i64, i64, &mut [SparseSegTreeNode<T>]),
{
    n: i64,
    pub tree: Vec<SparseSegTreeNode<T>>,
    pub pull: Pull,
    pub push: Push,
}

impl<T: Default + Clone, Pull, Push> SparseSegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, usize, &mut [SparseSegTreeNode<T>]),
    Push: FnMut(usize, usize, usize, i64, i64, &mut [SparseSegTreeNode<T>]),
{
    pub fn new(n: i64, capacity_hint: usize, pull: Pull, push: Push) -> Self {
        let mut tree = Vec::with_capacity(capacity_hint);
        tree.push(SparseSegTreeNode::default());
        tree.push(SparseSegTreeNode::default());
        Self {
            n,
            tree,
            pull,
            push,
        }
    }

    fn ensure_ch(&mut self, cur: usize) -> (usize, usize) {
        if self.tree[cur].l == 0 {
            let idx = self.tree.len();
            self.tree.push(SparseSegTreeNode::default());
            self.tree[cur].l = idx;
        }
        if self.tree[cur].r == 0 {
            let idx = self.tree.len();
            self.tree.push(SparseSegTreeNode::default());
            self.tree[cur].r = idx;
        }
        (self.tree[cur].l, self.tree[cur].r)
    }

    pub fn update<Op>(&mut self, range: impl RangeBounds<i64>, mut op: Op)
    where
        Op: FnMut(usize, i64, &mut [SparseSegTreeNode<T>]),
    {
        let l = match range.start_bound() {
            Bound::Included(x) => *x,
            Bound::Excluded(x) => *x + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(x) => *x + 1,
            Bound::Excluded(x) => *x,
            Bound::Unbounded => self.n,
        };
        if l >= r {
            return;
        }
        self.update_rec(1, 0, self.n, l, r, &mut op);
    }

    fn update_rec<Op>(&mut self, cur: usize, tl: i64, tr: i64, ql: i64, qr: i64, op: &mut Op)
    where
        Op: FnMut(usize, i64, &mut [SparseSegTreeNode<T>]),
    {
        if qr <= tl || tr <= ql {
            return;
        } else if ql <= tl && tr <= qr {
            op(cur, tr - tl, &mut self.tree);
            return;
        }
        let (lc, rc) = self.ensure_ch(cur);
        let m = tl.midpoint(tr);
        (self.push)(cur, lc, rc, m - tl, tr - m, &mut self.tree);
        self.update_rec(lc, tl, m, ql, qr, op);
        self.update_rec(rc, m, tr, ql, qr, op);
        (self.pull)(cur, lc, rc, &mut self.tree);
    }

    pub fn query<Visitor>(&mut self, range: impl RangeBounds<i64>, mut visitor: Visitor)
    where
        Visitor: FnMut(usize, i64, &mut [SparseSegTreeNode<T>]),
    {
        let l = match range.start_bound() {
            Bound::Included(x) => *x,
            Bound::Excluded(x) => *x + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(x) => *x + 1,
            Bound::Excluded(x) => *x,
            Bound::Unbounded => self.n,
        };
        if l >= r {
            return;
        }
        self.query_rec(1, 0, self.n, l, r, &mut visitor);
    }

    fn query_rec<Visitor>(
        &mut self,
        cur: usize,
        tl: i64,
        tr: i64,
        ql: i64,
        qr: i64,
        visitor: &mut Visitor,
    ) where
        Visitor: FnMut(usize, i64, &mut [SparseSegTreeNode<T>]),
    {
        if qr <= tl || tr <= ql {
            return;
        } else if ql <= tl && tr <= qr {
            visitor(cur, tr - tl, &mut self.tree);
            return;
        }
        let (lc, rc) = self.ensure_ch(cur);
        let m = tl.midpoint(tr);
        (self.push)(cur, lc, rc, m - tl, tr - m, &mut self.tree);
        self.query_rec(lc, tl, m, ql, qr, visitor);
        self.query_rec(rc, m, tr, ql, qr, visitor);
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }
}
