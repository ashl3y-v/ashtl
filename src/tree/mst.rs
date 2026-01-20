use std::ops::{AddAssign, SubAssign};

use crate::ds::dsu::{DSU, RollbackDSU};

pub struct DirectedMST<T> {
    n: usize,
    ns: Vec<DirectedMSTNode<T>>,
    heap: Vec<usize>,
}

struct DirectedMSTNode<T> {
    l: usize,
    r: usize,
    from: usize,
    to: usize,
    weight: T,
    lz: T,
}

impl<T: Copy + Default + AddAssign + SubAssign + PartialOrd> DirectedMST<T> {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            ns: Vec::new(),
            heap: vec![usize::MAX; n],
        }
    }

    pub fn with_capacity(n: usize, m: usize) -> Self {
        let mut s = Self::new(n);
        s.ns.reserve(m);
        s
    }

    pub fn add_edge(&mut self, from: usize, to: usize, weight: T) {
        let i = self.ns.len();
        self.ns.push(DirectedMSTNode {
            l: usize::MAX,
            r: usize::MAX,
            from,
            to,
            weight,
            lz: T::default(),
        });
        self.heap[to] = self.merge(self.heap[to], i);
    }

    fn apply(&mut self, i: usize, upd: T) {
        self.ns[i].weight -= upd;
        self.ns[i].lz += upd;
    }

    fn push(&mut self, i: usize) {
        let lz = self.ns[i].lz;
        if self.ns[i].l != usize::MAX {
            self.apply(self.ns[i].l, lz);
        }
        if self.ns[i].r != usize::MAX {
            self.apply(self.ns[i].r, lz);
        }
        self.ns[i].lz = T::default();
    }

    fn merge(&mut self, u: usize, v: usize) -> usize {
        if u == usize::MAX {
            return v;
        } else if v == usize::MAX {
            return u;
        }
        let (u, v) = if self.ns[v].weight < self.ns[u].weight {
            (v, u)
        } else {
            (u, v)
        };
        self.push(u);
        self.ns[u].r = self.merge(self.ns[u].r, v);
        (self.ns[u].r, self.ns[u].l) = (self.ns[u].l, self.ns[u].r);
        u
    }

    fn pop(&mut self, v: usize) {
        let h = self.heap[v];
        self.push(h);
        self.heap[v] = self.merge(self.ns[h].l, self.ns[h].r);
    }

    /// O(m log n)
    pub fn calc<C: Default + AddAssign<T>>(&mut self, r: usize) -> Option<(C, Vec<usize>)> {
        let n = self.n;
        let mut ans = C::default();
        let mut edge = vec![usize::MAX; n];
        let mut cycles: Vec<(usize, usize)> = Vec::new();
        let mut dsu_cyc = DSU::new(n);
        let mut dsu_cntr = RollbackDSU::new(n);
        for i in 0..n {
            if i == r {
                continue;
            }
            let mut v = i;
            loop {
                if self.heap[v] == usize::MAX {
                    return None;
                }
                edge[v] = self.heap[v];
                let w = self.ns[edge[v]].weight;
                ans += w;
                self.apply(edge[v], w);
                let from_v = dsu_cntr.find(self.ns[edge[v]].from);
                if dsu_cyc.union(v, from_v).1 {
                    break;
                }
                let t = dsu_cntr.joins.len();
                let mut v_nxt = from_v;
                loop {
                    let (v_new, b) = dsu_cntr.union(v, v_nxt);
                    if !b {
                        break;
                    }
                    self.heap[v_new] = self.merge(self.heap[v], self.heap[v_nxt]);
                    v = v_new;
                    v_nxt = dsu_cntr.find(self.ns[edge[v_nxt]].from);
                }
                cycles.push((edge[v], t));
                while self.heap[v] != usize::MAX && dsu_cntr.same(self.ns[self.heap[v]].from, v) {
                    self.pop(v);
                }
            }
        }
        for &(cyc_edge, t) in cycles.iter().rev() {
            let v_repr = dsu_cntr.find(self.ns[cyc_edge].to);
            dsu_cntr.rollback(t);
            let v_inc = dsu_cntr.find(self.ns[edge[v_repr]].to);
            (edge[v_repr], edge[v_inc]) = (cyc_edge, edge[v_repr]);
        }
        for i in 0..n {
            if i != r {
                edge[i] = self.ns[edge[i]].from;
            } else {
                edge[i] = r;
            }
        }
        Some((ans, edge))
    }
}
