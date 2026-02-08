use crate::ds::bit_vec::BitVec;
use std::ops::{Bound, RangeBounds};

const NULL: usize = 0;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplayNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
    pub size: usize,
}

#[derive(Clone, Debug)]
pub struct Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    pub ns: Vec<SplayNode<T>>,
    pub push: Push,
    pub pull: Pull,
    pub rt: usize,
    pub nxt: usize,
    pub removed: usize,
    pub open: BitVec,
}

impl<T, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    #[inline]
    pub fn new(init: T, push: Push, pull: Pull) -> Self {
        Self {
            ns: vec![SplayNode {
                v: init,
                l: NULL,
                r: NULL,
                size: 0,
            }],
            push,
            pull,
            rt: NULL,
            nxt: 1,
            removed: 0,
            open: BitVec::new(1, false),
        }
    }

    #[inline]
    fn pull(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.ns[x];
            let (l, r) = (n.l, n.r);
            self.ns[x].size = self.ns[l].size + self.ns[r].size + 1;
            (self.pull)(x, l, r, &mut self.ns);
        }
        self
    }

    #[inline]
    fn push(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.ns[x];
            (self.push)(x, n.l, n.r, &mut self.ns);
        }
        self
    }

    #[inline]
    fn zig(&mut self, x: usize) -> usize {
        let l = self.ns[x].l;
        self.ns[x].l = self.ns[l].r;
        self.pull(x);
        self.ns[l].r = x;
        l
    }

    #[inline]
    fn zag(&mut self, x: usize) -> usize {
        let r = self.ns[x].r;
        self.ns[x].r = self.ns[r].l;
        self.pull(x);
        self.ns[r].l = x;
        r
    }

    pub fn splay(&mut self, x: usize, mut k: usize) -> usize {
        self.push(x);
        let l = self.ns[x].l;
        let size = self.ns[l].size;
        if k == size {
            x
        } else if k < size {
            self.push(l);
            let (ll, lr) = (self.ns[l].l, self.ns[l].r);
            let ll_size = self.ns[ll].size;
            if k == ll_size {
                self.zig(x)
            } else if k < ll_size {
                self.ns[l].l = self.splay(ll, k);
                let new_l = self.zig(x);
                self.zig(new_l)
            } else {
                self.ns[l].r = self.splay(lr, k - ll_size - 1);
                self.ns[x].l = self.zag(l);
                self.zig(x)
            }
        } else {
            let r = self.ns[x].r;
            self.push(r);
            k -= size + 1;
            let (rl, rr) = (self.ns[r].l, self.ns[r].r);
            let rl_size = self.ns[rl].size;
            if k == rl_size {
                self.zag(x)
            } else if k < rl_size {
                self.ns[r].l = self.splay(rl, k);
                self.ns[x].r = self.zig(r);
                self.zag(x)
            } else {
                self.ns[r].r = self.splay(rr, k - rl_size - 1);
                let new_r = self.zag(x);
                self.zag(new_r)
            }
        }
    }

    #[inline]
    pub fn get(&mut self, k: usize) -> Option<&T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&self.ns[self.rt].v)
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: usize) -> Option<&mut T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&mut self.ns[self.rt].v)
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: usize, v: T) -> &mut Self {
        let len = self.ns.len();
        while self.nxt < self.ns.len() && !self.open[self.nxt] {
            self.nxt += 1;
        }
        let nxt = self.nxt;
        if self.len() <= k {
            let n = SplayNode {
                v,
                l: self.rt,
                r: NULL,
                size: 0,
            };
            if nxt < len {
                self.ns[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.ns.push(n);
                self.open.push(false);
            }
        } else {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            let l = self.ns[self.rt].l;
            self.ns[self.rt].l = NULL;
            self.pull(self.rt);
            let n = SplayNode {
                v,
                l,
                r: self.rt,
                size: 0,
            };
            if nxt < len {
                self.ns[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.ns.push(n);
                self.open.push(false);
            }
        }
        self.pull(nxt);
        self.push(nxt);
        self.rt = nxt;
        self.nxt += 1;
        self
    }

    pub fn remove(&mut self, k: usize) -> &mut Self {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.open.set(self.rt, true);
            self.push(self.rt);
            let r = self.ns[self.rt].r;
            if r != NULL {
                let r = self.splay(r, 0);
                (self.ns[r].l, self.ns[self.rt].l, self.rt) = (self.ns[self.rt].l, NULL, r);
                self.pull(r);
            } else {
                (self.rt, self.ns[self.rt].l) = (self.ns[self.rt].l, NULL);
            }
        }
        self.removed += 1;
        let len = self.ns.len();
        if self.removed << 1 > len {
            self.nxt = self.open.iter().position(|v| v == true).unwrap_or(len);
            self.removed = 0;
        }
        self
    }

    pub fn merge_nodes(&mut self, mut a: usize, b: usize) -> usize {
        if a == NULL {
            return b;
        } else if b == NULL {
            return a;
        }
        let a_size = self.ns[a].size;
        a = self.splay(a, a_size - 1);
        self.pull(a);
        self.push(a);
        self.ns[a].r = b;
        self.pull(a);
        a
    }

    pub fn split_node(&mut self, mut a: usize, k: usize) -> (usize, usize) {
        if a == NULL {
            (NULL, NULL)
        } else if k == NULL {
            self.push(a);
            (NULL, a)
        } else if k >= self.ns[a].size {
            self.push(a);
            (a, NULL)
        } else {
            a = self.splay(a, k - 1);
            self.pull(a);
            self.push(a);
            let r = self.ns[a].r;
            self.ns[a].r = NULL;
            if r != NULL {
                self.push(r);
            }
            self.pull(a);
            (a, r)
        }
    }

    pub fn range<R, F>(&mut self, range: impl RangeBounds<usize>, mut f: F) -> Option<R>
    where
        F: FnMut(usize, &mut [SplayNode<T>]) -> R,
    {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.len(),
        };
        if l >= r {
            return None;
        }
        let (a, b) = self.split_node(self.rt, l);
        let (b, c) = self.split_node(b, r - l);
        let res = if b != NULL {
            Some(f(b, &mut self.ns))
        } else {
            None
        };
        let merged_ab = self.merge_nodes(a, b);
        self.rt = self.merge_nodes(merged_ab, c);
        res
    }

    #[inline]
    pub fn for_each<F>(&mut self, mut f: F) -> &mut Self
    where
        F: FnMut(&T),
    {
        self.for_each_node(self.rt, &mut f);
        self
    }

    fn for_each_node<F>(&mut self, n: usize, f: &mut F)
    where
        F: FnMut(&T),
    {
        if n != NULL {
            let (l, r) = (self.ns[n].l, self.ns[n].r);
            self.push(n);
            self.for_each_node(l, f);
            f(&self.ns[n].v);
            self.for_each_node(r, f);
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.rt != NULL {
            self.ns[self.rt].size
        } else {
            0
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rt == NULL
    }
}

impl<T: Clone, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    fn build<S>(&mut self, v: &[S], elem: &mut impl FnMut(&S) -> T, l: usize, r: usize) -> usize {
        if l == r {
            NULL
        } else if l + 1 == r {
            self.ns[l].v = elem(&v[l - 1]);
            self.pull(l);
            l
        } else {
            let m = l.midpoint(r);
            self.ns[m].v = elem(&v[m - 1]);
            self.ns[m].l = self.build(v, elem, l, m);
            self.ns[m].r = self.build(v, elem, m + 1, r);
            self.pull(m);
            m
        }
    }

    pub fn from_slice<S>(
        v: &[S],
        init: T,
        mut elem: impl FnMut(&S) -> T,
        push: Push,
        pull: Pull,
    ) -> Splay<T, Push, Pull> {
        let len = v.len();
        let mut s = Splay {
            ns: vec![
                SplayNode {
                    v: init,
                    l: NULL,
                    r: NULL,
                    size: 0
                };
                len + 1
            ],
            push,
            pull,
            rt: NULL,
            nxt: len,
            removed: 0,
            open: BitVec::new(len + 1, false),
        };
        s.rt = s.build(v, &mut elem, 1, len + 1);
        s
    }
}
