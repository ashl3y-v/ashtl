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
    pub fn new(a: &[T]) -> (Self, usize) {
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
            let m = l + (r - l >> 1);
            let l = self.build(l, m, a);
            let r = self.build(m, r, a);
            self.v.push(ArrayNode { v: None, l, r });
        }
        self.v.len() - 1
    }

    pub fn query(&self, mut rt: usize, i: usize) -> &T {
        let (mut l, mut r) = (0, self.n);
        while r - l > 1 {
            let m = l + (r - l >> 1);
            if i < m {
                (rt, r) = (self.v[rt].l, m);
            } else {
                (rt, l) = (self.v[rt].r, m);
            }
        }
        self.v[rt].v.as_ref().unwrap()
    }

    pub fn update(&mut self, rt: usize, i: usize, v: T) -> usize {
        self.update_rec(rt, i, 0, self.n, v)
    }

    fn update_rec(&mut self, rt: usize, i: usize, l: usize, r: usize, v: T) -> usize {
        if r - l == 1 {
            self.v.push(ArrayNode::new(v, NULL, NULL));
            self.v.len() - 1
        } else {
            let m = l + (r - l >> 1);
            if i < m {
                let l = self.update_rec(self.v[rt].l, i, l, m, v);
                self.v.push(ArrayNode {
                    v: None,
                    l: l,
                    r: self.v[rt].r,
                });
                self.v.len() - 1
            } else {
                let r = self.update_rec(self.v[rt].r, i, m, r, v);
                self.v.push(ArrayNode {
                    v: None,
                    l: self.v[rt].l,
                    r,
                });
                self.v.len() - 1
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeftistNode<T> {
    pub v: T,
    pub s: usize,
    pub l: usize,
    pub r: usize,
}

impl<T> LeftistNode<T> {
    pub fn new(v: T, l: usize, r: usize, s: usize) -> Self {
        Self { v, s, l, r }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersistentLeftist<T> {
    pub n: Vec<LeftistNode<T>>,
    pub nxt: usize,
}

impl<T: Clone + PartialOrd> PersistentLeftist<T> {
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
            s.new_node(LeftistNode::new(v, NULL, NULL, 1));
        }
        let r = s.nxt;
        fn meld<T: Clone + PartialOrd>(
            s: &mut PersistentLeftist<T>,
            mut p: usize,
            mut q: usize,
        ) -> usize {
            if s.n[p].v > s.n[q].v {
                (p, q) = (q, p);
            }
            s.n[p].r = s.meld(s.n[p].r, q);
            s.restructure(p);
            p
        }
        fn rec<T: Clone + PartialOrd>(s: &mut PersistentLeftist<T>, l: usize, r: usize) -> usize {
            if l + 1 == r {
                return l;
            }
            let m = l + (r - l >> 1);
            let lh = rec(s, l, m);
            let rh = rec(s, m, r);
            meld(s, lh, rh)
        }
        let rt = rec(&mut s, l, r);
        (s, rt)
    }

    fn new_node(&mut self, node: LeftistNode<T>) -> usize {
        let nxt = self.nxt;
        if nxt < self.n.len() {
            self.n[nxt] = node;
        } else {
            self.n.push(node);
        }
        self.nxt += 1;
        nxt
    }

    fn get_s(&self, u: usize) -> usize {
        if u == NULL { 0 } else { self.n[u].s }
    }

    fn restructure(&mut self, x: usize) {
        if x == NULL {
            return;
        }
        if self.get_s(self.n[x].l) < self.get_s(self.n[x].r) {
            (self.n[x].l, self.n[x].r) = (self.n[x].r, self.n[x].l);
        }
        self.n[x].s = self.get_s(self.n[x].r) + 1;
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
        self.restructure(npr);
        npr
    }

    /// O(log n)
    pub fn insert(&mut self, rt: usize, v: T) -> usize {
        let s = LeftistNode::new(v, NULL, NULL, 1);
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

// TODO: persistent segment tree
// https://usaco.guide/adv/persistent?lang=cpp
