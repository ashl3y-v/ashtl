use crate::ds::dsu::DSU;
use bit_vec::BitVec;

/// Online Bridge Tree O(n log n α(n) + m α(n))
pub struct BridgeTree {
    pub par: Vec<usize>,
    pub dsu_2ecc: DSU,
    pub dsu_cc: DSU,
    pub count: usize,
    pub mask: BitVec,
    pub lca_iteration: usize,
    pub last_visit: Vec<usize>,
}

impl BridgeTree {
    pub fn new(n: usize) -> Self {
        BridgeTree {
            par: vec![usize::MAX; n],
            dsu_2ecc: DSU::new(n),
            dsu_cc: DSU::new(n),
            count: 0,
            mask: BitVec::from_elem(n, false),
            lca_iteration: 0,
            last_visit: vec![0; n],
        }
    }

    fn make_root(&mut self, v: usize) -> &mut Self {
        if self.par[v] == usize::MAX {
            return self;
        }
        let mut cur = v;
        let root = v;
        let mut child = usize::MAX;
        while self.par[cur] != usize::MAX {
            let p = self.dsu_2ecc.find(self.par[cur]);
            self.par[cur] = child;
            self.dsu_cc.dsu[cur] = root as isize;
            child = cur;
            cur = p;
        }
        self.par[cur] = child;
        self.dsu_cc.dsu[child] = self.dsu_cc.dsu[cur];
        self.dsu_cc.dsu[cur] = root as isize;
        self
    }

    fn merge_path(&mut self, mut a: usize, mut b: usize) -> &mut Self {
        self.lca_iteration += 1;
        let iter = self.lca_iteration;
        let mut path_a = Vec::new();
        let mut path_b = Vec::new();
        let mut lca = usize::MAX;

        while lca == usize::MAX {
            if a != usize::MAX {
                a = self.dsu_2ecc.find(a);
                path_a.push(a);
                if self.last_visit[a] == iter {
                    lca = a;
                    break;
                } else {
                    self.last_visit[a] = iter;
                    a = self.par[a];
                }
            }
            if b != usize::MAX {
                b = self.dsu_2ecc.find(b);
                path_b.push(b);
                if self.last_visit[b] == iter {
                    lca = b;
                    break;
                } else {
                    self.last_visit[b] = iter;
                    b = self.par[b];
                }
            }
        }

        let mut r = self.dsu_2ecc.find(lca);
        for i in 0..path_a.len() {
            let v = path_a[i];
            if v == lca {
                break;
            }
            self.mask.set(v, true);
            self.count -= 1;
            (_, r) = self.dsu_2ecc.union_root(v, r);
        }
        for i in 0..path_b.len() {
            let v = path_b[i];
            if v == lca {
                break;
            }
            self.mask.set(v, true);
            self.count -= 1;
            (_, r) = self.dsu_2ecc.union_root(v, r);
        }
        self.par[r] = self.par[lca];
        self
    }

    pub fn add_edge(&mut self, mut a: usize, mut b: usize) -> &mut Self {
        a = self.dsu_2ecc.find(a);
        b = self.dsu_2ecc.find(b);
        if a == b {
            return self;
        }
        let ca = self.dsu_cc.find(a);
        let mut cb = self.dsu_cc.find(b);
        if ca != cb {
            if self.dsu_cc.dsu[ca] < self.dsu_cc.dsu[cb] {
                (a, b) = (b, a);
                cb = ca;
            }
            self.count += 1;
            self.make_root(a);
            self.par[a] = b;
            self.dsu_cc.dsu[cb] += self.dsu_cc.dsu[a];
            self.dsu_cc.dsu[a] = b as isize;
        } else {
            self.merge_path(a, b);
        }
        self
    }

    pub fn bridges(&self) -> Vec<(usize, usize)> {
        self.par
            .iter()
            .enumerate()
            .filter_map(|(i, &j)| (j != usize::MAX && !self.mask[i]).then_some((i, j)))
            .collect()
    }
}
