const NULL: usize = usize::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArrayNode<T> {
    pub v: Option<T>,
    pub l: usize,
    pub r: usize,
}

impl<T> ArrayNode<T> {
    pub fn new(v: T, l: usize, r: usize) -> Self {
        Self { v: Some(v), l, r }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersistentArray<T> {
    pub n: usize,
    pub v: Vec<ArrayNode<T>>,
}

impl<T: Clone> PersistentArray<T> {
    pub fn new(n: usize) -> (Self, usize) {
        (
            Self {
                n,
                v: vec![ArrayNode {
                    v: None,
                    l: NULL,
                    r: NULL,
                }],
            },
            0,
        )
    }

    pub fn from_slice(a: &[T]) -> (Self, usize) {
        let mut s = Self {
            n: a.len(),
            v: Vec::new(),
        };
        let r = s.build(0, a.len(), &a);
        (s, r)
    }

    fn build(&mut self, l: usize, r: usize, a: &[T]) -> usize {
        if r - l == 1 {
            self.v.push(ArrayNode::new(a[l].clone(), NULL, NULL));
        } else {
            let m = l.midpoint(r);
            let l = self.build(l, m, a);
            let r = self.build(m, r, a);
            self.v.push(ArrayNode { v: None, l, r });
        }
        self.v.len() - 1
    }

    pub fn query(&self, mut rt: usize, i: usize) -> Option<&T> {
        let (mut l, mut r) = (0, self.n);
        while r - l > 1 {
            let m = l.midpoint(r);
            if i < m {
                (rt, r) = (self.v[rt].l, m);
            } else {
                (rt, l) = (self.v[rt].r, m);
            }
            if rt == NULL {
                return None;
            }
        }
        self.v[rt].v.as_ref()
    }

    pub fn update(&mut self, rt: usize, i: usize, v: T) -> usize {
        self.update_rec(rt, i, 0, self.n, v)
    }

    fn update_rec(&mut self, rt: usize, i: usize, l: usize, r: usize, v: T) -> usize {
        if r - l == 1 {
            self.v.push(ArrayNode::new(v, NULL, NULL));
            self.v.len() - 1
        } else {
            let m = l.midpoint(r);
            if i < m {
                let cl = if self.v[rt].l == NULL {
                    self.v.push(ArrayNode {
                        v: None,
                        l: NULL,
                        r: NULL,
                    });
                    self.v.len() - 1
                } else {
                    self.v[rt].l
                };
                let cl = self.update_rec(cl, i, l, m, v);
                self.v.push(ArrayNode {
                    v: None,
                    l: cl,
                    r: self.v[rt].r,
                });
                self.v.len() - 1
            } else {
                let cr = if self.v[rt].r == NULL {
                    self.v.push(ArrayNode {
                        v: None,
                        l: NULL,
                        r: NULL,
                    });
                    self.v.len() - 1
                } else {
                    self.v[rt].r
                };
                let cr = self.update_rec(cr, i, m, r, v);
                self.v.push(ArrayNode {
                    v: None,
                    l: self.v[rt].l,
                    r: cr,
                });
                self.v.len() - 1
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SkewNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
}

impl<T> SkewNode<T> {
    pub fn new(v: T, l: usize, r: usize) -> Self {
        Self { v, l, r }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersistentSkew<T> {
    pub n: Vec<SkewNode<T>>,
    pub nxt: usize,
}

impl<T: Clone + PartialOrd> PersistentSkew<T> {
    pub fn new() -> Self {
        Self {
            n: Vec::new(),
            nxt: 0,
        }
    }

    /// O(n)
    pub fn from_vec(a: Vec<T>) -> (Self, usize) {
        let mut s = Self::new();
        if a.is_empty() {
            return (s, NULL);
        }
        let l = s.nxt;
        for v in a {
            s.new_node(SkewNode::new(v, NULL, NULL));
        }
        let r = s.nxt;
        fn meld<T: Clone + PartialOrd>(
            s: &mut PersistentSkew<T>,
            mut p: usize,
            mut q: usize,
        ) -> usize {
            if p == NULL {
                return q;
            } else if q == NULL {
                return p;
            } else if s.n[p].v > s.n[q].v {
                (p, q) = (q, p);
            }
            (s.n[p].l, s.n[p].r) = (meld(s, s.n[p].r, q), s.n[p].l);
            p
        }
        fn rec<T: Clone + PartialOrd>(s: &mut PersistentSkew<T>, l: usize, r: usize) -> usize {
            if l + 1 == r {
                return l;
            }
            let m = l + (r - l) / 2;
            let lh = rec(s, l, m);
            let rh = rec(s, m, r);
            meld(s, lh, rh)
        }
        let rt = rec(&mut s, l, r);
        (s, rt)
    }

    fn new_node(&mut self, node: SkewNode<T>) -> usize {
        let nxt = self.nxt;
        if nxt < self.n.len() {
            self.n[nxt] = node;
        } else {
            self.n.push(node);
        }
        self.nxt += 1;
        nxt
    }

    /// O(log n)
    fn meld(&mut self, mut p: usize, mut q: usize) -> usize {
        if p == NULL {
            return q;
        } else if q == NULL {
            return p;
        } else if self.n[p].v > self.n[q].v {
            (p, q) = (q, p);
        }
        let mut np = self.n[p].clone();
        let nr = self.meld(np.r, q);
        np.r = nr;
        let npr = self.new_node(np);
        (self.n[npr].l, self.n[npr].r) = (self.n[npr].r, self.n[npr].l);
        npr
    }

    /// O(log n)
    pub fn insert(&mut self, rt: usize, v: T) -> usize {
        let s = SkewNode::new(v, NULL, NULL);
        let sr = self.new_node(s);
        self.meld(rt, sr)
    }

    pub fn peek(&self, rt: usize) -> &T {
        &self.n[rt].v
    }

    /// O(log n)
    pub fn pop(&mut self, rt: usize) -> (T, usize) {
        let m = self.n[rt].v.clone();
        let l = self.n[rt].l;
        let r = self.n[rt].r;
        let nr = self.meld(l, r);
        (m, nr)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueueNode<T> {
    pub v: T,
    pub p: usize,
    pub fr: usize,
    pub jmp: usize,
    pub depth: usize,
}

impl<T> QueueNode<T> {
    pub fn new(v: T, p: usize, fr: usize, jmp: usize, depth: usize) -> Self {
        Self {
            v,
            p,
            fr,
            jmp,
            depth,
        }
    }
}

pub struct PersistentQueue<T> {
    pub n: Vec<QueueNode<T>>,
    pub nxt: usize,
}

impl<T: Clone> PersistentQueue<T> {
    pub fn new() -> Self {
        Self {
            n: Vec::new(),
            nxt: 0,
        }
    }

    pub fn new_node(&mut self, v: T, p: usize) -> usize {
        let nxt = self.n.len();
        let node = if p != NULL {
            let fr = self.n[p].fr;
            let pj = self.n[p].jmp;
            let pjj = self.n[pj].jmp;
            let jmp = if self.n[p].depth - self.n[pj].depth == self.n[pj].depth - self.n[pjj].depth
            {
                pjj
            } else {
                p
            };
            let depth = self.n[p].depth + 1;
            QueueNode::new(v, p, fr, jmp, depth)
        } else {
            QueueNode::new(v, p, nxt, nxt, 0)
        };
        self.n.push(node);
        nxt
    }

    pub fn push(&mut self, v: T, p: usize) -> usize {
        self.new_node(v, p)
    }

    /// O(log n)
    pub fn query(&self, mut p: usize, i: usize) -> usize {
        debug_assert!(i <= self.n[p].depth);
        while self.n[p].depth != i {
            if self.n[self.n[p].jmp].depth >= i {
                p = self.n[p].jmp;
            } else {
                p = self.n[p].p;
            }
        }
        p
    }

    /// O(1)
    pub fn front(&self, p: usize) -> Option<&T> {
        if self.n.is_empty() {
            return None;
        }
        Some(&self.n[self.n[p].fr].v)
    }

    /// O(log n)
    pub fn pop(&mut self, p: usize) -> usize {
        self.n.push(self.n[p].clone());
        let p = self.n.len() - 1;
        self.n[p].fr = self.query(p, self.n[self.n[p].fr].depth + 1);
        p
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub struct PersistentSegTreeNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
}

pub struct PersistentSegTree<T, Pull>
where
    Pull: Fn(usize, usize, usize, &mut [PersistentSegTreeNode<T>]),
{
    n: usize,
    pub tree: Vec<PersistentSegTreeNode<T>>,
    timer: usize,
    pull: Pull,
}

impl<T, Pull> PersistentSegTree<T, Pull>
where
    T: Clone + Default,
    Pull: Fn(usize, usize, usize, &mut [PersistentSegTreeNode<T>]),
{
    pub fn new(n: usize, mx_nodes: usize, pull: Pull) -> Self {
        let tree = vec![PersistentSegTreeNode::default(); mx_nodes];
        Self {
            n,
            tree,
            timer: 1,
            pull,
        }
    }

    fn build_rec(&mut self, tl: usize, tr: usize, arr: &[T]) -> usize {
        let cur = self.timer;
        self.timer += 1;
        if tl + 1 == tr {
            self.tree[cur].v = arr[tl].clone();
            return cur;
        }
        let m = tl.midpoint(tr);
        let lc = self.build_rec(tl, m, arr);
        let rc = self.build_rec(m, tr, arr);
        self.tree[cur].l = lc;
        self.tree[cur].r = rc;
        (self.pull)(cur, lc, rc, &mut self.tree);
        cur
    }

    pub fn build(&mut self, arr: &[T]) -> usize {
        self.build_rec(0, self.n, arr)
    }

    fn update_rec(&mut self, prev_node: usize, pos: usize, val: T, tl: usize, tr: usize) -> usize {
        let cur = self.timer;
        self.timer += 1;
        self.tree[cur] = self.tree[prev_node].clone();
        if tl + 1 == tr {
            self.tree[cur].v = val;
            return cur;
        }
        let m = tl.midpoint(tr);
        if pos < m {
            let new_l = self.update_rec(self.tree[prev_node].l, pos, val, tl, m);
            self.tree[cur].l = new_l;
        } else {
            let new_r = self.update_rec(self.tree[prev_node].r, pos, val, m, tr);
            self.tree[cur].r = new_r;
        }
        (self.pull)(cur, self.tree[cur].l, self.tree[cur].r, &mut self.tree);
        cur
    }

    pub fn update(&mut self, root: usize, pos: usize, val: T) -> usize {
        self.update_rec(root, pos, val, 0, self.n)
    }

    fn query_rec<Visitor>(
        &self,
        v: usize,
        ql: usize,
        qr: usize,
        tl: usize,
        tr: usize,
        visitor: &mut Visitor,
    ) where
        Visitor: FnMut(usize, usize, &[PersistentSegTreeNode<T>]),
    {
        if qr <= tl || tr <= ql {
            return;
        } else if ql <= tl && tr <= qr {
            visitor(v, tr - tl, &self.tree);
            return;
        }
        let mid = (tl + tr) / 2;
        self.query_rec(self.tree[v].l, ql, qr, tl, mid, visitor);
        self.query_rec(self.tree[v].r, ql, qr, mid, tr, visitor);
    }

    pub fn query<Visitor>(&mut self, root: usize, l: usize, r: usize, mut visitor: Visitor)
    where
        Visitor: FnMut(usize, usize, &[PersistentSegTreeNode<T>]),
    {
        self.query_rec(root, l, r, 0, self.n, &mut visitor);
    }

    pub fn copy(&mut self, root: usize) -> usize {
        let cur = self.timer;
        self.timer += 1;
        self.tree[cur] = self.tree[root].clone();
        cur
    }
}
