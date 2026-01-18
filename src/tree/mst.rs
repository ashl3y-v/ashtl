use std::ops::{AddAssign, SubAssign};

use crate::ds::dsu::{DSU, RollbackDSU};

pub struct DirectedMST<T> {
    n: usize,
    nodes: Vec<Node<T>>,
    heap: Vec<usize>,
}

struct Node<T> {
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
            nodes: Vec::new(),
            heap: vec![usize::MAX; n],
        }
    }

    pub fn with_capacity(n: usize, m: usize) -> Self {
        let mut s = Self::new(n);
        s.nodes.reserve(m);
        s
    }

    pub fn add_edge(&mut self, from: usize, to: usize, weight: T) {
        let i = self.nodes.len();
        self.nodes.push(Node {
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
        self.nodes[i].weight -= upd;
        self.nodes[i].lz += upd;
    }

    fn push(&mut self, i: usize) {
        let lz = self.nodes[i].lz;
        if self.nodes[i].l != usize::MAX {
            self.apply(self.nodes[i].l, lz);
        }
        if self.nodes[i].r != usize::MAX {
            self.apply(self.nodes[i].r, lz);
        }
        self.nodes[i].lz = T::default();
    }

    fn merge(&mut self, u: usize, v: usize) -> usize {
        if u == usize::MAX {
            return v;
        } else if v == usize::MAX {
            return u;
        }
        let (u, v) = if self.nodes[v].weight < self.nodes[u].weight {
            (v, u)
        } else {
            (u, v)
        };
        self.push(u);
        self.nodes[u].r = self.merge(self.nodes[u].r, v);
        (self.nodes[u].r, self.nodes[u].l) = (self.nodes[u].l, self.nodes[u].r);
        u
    }

    fn pop(&mut self, v: usize) {
        let h = self.heap[v];
        self.push(h);
        self.heap[v] = self.merge(self.nodes[h].l, self.nodes[h].r);
    }

    /// O(m log n)
    pub fn calc<C: Default + AddAssign<T>>(&mut self, root: usize) -> Option<(C, Vec<usize>)> {
        let n = self.n;
        let mut ans = C::default();
        let mut edge = vec![usize::MAX; n];
        let mut cycles: Vec<(usize, usize)> = Vec::new();
        let mut dsu_cyc = DSU::new(n);
        let mut dsu_cntr = RollbackDSU::new(n);
        for i in 0..n {
            if i == root {
                continue;
            }
            let mut v = i;
            loop {
                if self.heap[v] == usize::MAX {
                    return None;
                }
                edge[v] = self.heap[v];
                let w = self.nodes[edge[v]].weight;
                ans += w;
                self.apply(edge[v], w);
                let from_v = dsu_cntr.find(self.nodes[edge[v]].from);
                if dsu_cyc.union(v, from_v).0 {
                    break;
                }
                let mut vnext = from_v;
                let t = dsu_cntr.joins.len();
                while dsu_cntr.union(v, vnext).0 {
                    let new_v = dsu_cntr.find(v);
                    let (hv, hnext) = (self.heap[v], self.heap[vnext]);
                    self.heap[new_v] = self.merge(hv, hnext);
                    v = new_v;
                    vnext = dsu_cntr.find(self.nodes[edge[vnext]].from);
                }
                cycles.push((edge[v], t));
                while self.heap[v] != usize::MAX && dsu_cntr.same(self.nodes[self.heap[v]].from, v)
                {
                    self.pop(v);
                }
            }
        }
        for &(cyc_edge, t) in cycles.iter().rev() {
            let vrepr = dsu_cntr.find(self.nodes[cyc_edge].to);
            dsu_cntr.rollback(t);
            let vinc = dsu_cntr.find(self.nodes[edge[vrepr]].to);
            let tmp = edge[vrepr];
            edge[vrepr] = cyc_edge;
            edge[vinc] = tmp;
        }
        let parent: Vec<usize> = (0..n)
            .map(|i| {
                if i == root {
                    root
                } else {
                    self.nodes[edge[i]].from
                }
            })
            .collect();
        Some((ans, parent))
    }
}
