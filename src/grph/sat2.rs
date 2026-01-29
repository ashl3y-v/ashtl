use crate::{ds::bit_vec::BitVec, grph::cc::scc};

pub struct SAT2 {
    n: usize,
    adj: Vec<Vec<usize>>,
    pub values: BitVec,
}

impl SAT2 {
    #[inline]
    pub fn new(n: usize) -> Self {
        SAT2 {
            n,
            adj: vec![Vec::new(); n << 1],
            values: BitVec::new(0, false),
        }
    }

    #[inline]
    pub fn add_var(&mut self) -> isize {
        let v = self.n;
        self.adj.push(Vec::new());
        self.adj.push(Vec::new());
        self.n += 1;
        v as isize
    }

    #[inline]
    fn idx(lit: isize) -> usize {
        if lit >= 0 {
            (lit as usize) << 1
        } else {
            ((!lit) as usize) << 1 | 1
        }
    }

    #[inline]
    pub fn set_value(&mut self, x: isize) -> &mut Self {
        self.either(x, x);
        self
    }

    #[inline]
    pub fn either(&mut self, f: isize, j: isize) -> &mut Self {
        let u = Self::idx(f) ^ 1;
        let v = Self::idx(j);
        self.adj[u].push(v);
        let u2 = Self::idx(j) ^ 1;
        let v2 = Self::idx(f);
        self.adj[u2].push(v2);
        self
    }

    #[inline]
    pub fn at_most_one(&mut self, li: &[isize]) -> &mut Self {
        if li.len() <= 1 {
            return self;
        }
        let mut cur = !li[0];
        for &lit in &li[2..] {
            let nxt = self.add_var();
            self.either(cur, !lit);
            self.either(cur, nxt);
            self.either(!lit, nxt);
            cur = !nxt;
        }
        self.either(cur, !li[1]);
        self
    }

    pub fn solve(&mut self) -> bool {
        let num_nodes = self.adj.len();
        let mut g = vec![0; num_nodes + 1];
        let mut edge_count = 0;
        for (i, neighbors) in self.adj.iter().enumerate() {
            edge_count += neighbors.len();
            g[i + 1] = edge_count;
        }
        let mut d = vec![0; edge_count];
        let mut ptr = 0;
        for neighbors in &self.adj {
            for &v in neighbors {
                d[ptr] = v;
                ptr += 1;
            }
        }
        let scc_res = scc(num_nodes, &g, &d);
        let comp_id = scc_res.comp_id;
        self.values = BitVec::new(self.n, false);
        for i in 0..self.n {
            if comp_id[i << 1] == comp_id[i << 1 | 1] {
                return false;
            }
            let val = comp_id[i << 1] < comp_id[i << 1 | 1];
            self.values.set(i, val);
        }
        true
    }
}
