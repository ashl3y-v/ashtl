use super::ancestor::LCA;
use crate::range::rmq::RMQ;
use std::cmp::Ordering;

/// Kruskal reconstruction tree
/// O(n log n) construction
pub struct KRT<F: FnMut(usize, usize, usize)> {
    pub n: usize,
    pub chs: Vec<[usize; 2]>,
    pub nxt: usize,
    pub p: Vec<usize>,
    pub idx: Vec<usize>,
    pub dsu: Vec<usize>,
    pub on_union: F,
}

impl<F: FnMut(usize, usize, usize)> KRT<F> {
    pub fn new(n: usize, on_union: F) -> Self {
        let mut dsu = Vec::with_capacity(n << 1);
        dsu.extend(0..n << 1);
        let mut p = Vec::with_capacity(n << 1);
        p.extend(0..n << 1);
        Self {
            n,
            chs: vec![[usize::MAX; 2]; n << 1],
            nxt: n,
            p,
            idx: vec![usize::MAX; n],
            dsu,
            on_union,
        }
    }

    /// O(log n)
    pub fn find(&mut self, mut x: usize) -> usize {
        while self.dsu[x] != x {
            let p = self.dsu[x];
            self.dsu[x] = self.dsu[p];
            x = p;
        }
        x
    }

    /// O(log n)
    pub fn add_edge(&mut self, u: usize, v: usize, idx: usize) -> &mut Self {
        let (ru, rv) = (self.find(u), self.find(v));
        if ru != rv {
            self.chs[self.nxt] = [ru, rv];
            self.idx[self.nxt - self.n] = idx;
            (self.p[ru], self.p[rv]) = (self.nxt, self.nxt);
            self.dsu[ru] = self.nxt;
            self.dsu[rv] = self.nxt;
            self.nxt += 1;
            (self.on_union)(ru, rv, self.nxt);
        }
        self
    }

    /// O(n)
    pub fn dfs(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let k = self.nxt;
        let mut ss = vec![1; k];
        let mut depth = vec![0; k];
        let mut pos = vec![0; k];
        let mut dfs = vec![0; k];
        for u in 0..k - 1 {
            ss[self.p[u]] += ss[u];
        }
        pos.copy_from_slice(&ss);
        for u in (0..k - 1).rev() {
            let v = self.p[u];
            depth[u] = depth[v] + 1;
            (pos[u], pos[v]) = (pos[v], pos[v] - pos[u]);
        }
        for i in 0..k {
            pos[i] -= 1;
            dfs[pos[i]] = i;
        }
        (ss, pos, dfs, depth)
    }

    /// O(n) construction, O(1) query
    pub fn leaf_pos_rmq(
        &self,
        pos: &[usize],
    ) -> (
        RMQ<impl FnMut(usize, usize) -> Ordering>,
        RMQ<impl FnMut(usize, usize) -> Ordering>,
    ) {
        (
            RMQ::new(self.n, |i, j| pos[i].cmp(&pos[j])),
            RMQ::new(self.n, |i, j| pos[j].cmp(&pos[i])),
        )
    }

    /// O(n) construction O(1) query
    pub fn lca<'a>(
        &'a self,
        dfs: &'a [usize],
        pos: &'a [usize],
        depth: &'a [usize],
    ) -> LCA<'a, impl FnMut(usize, usize) -> Ordering> {
        let k = self.nxt;
        let mut z = Vec::with_capacity(k);
        z.extend((0..k).map(|i| depth[self.p[dfs[i]]]));
        let lca = LCA::new(k, &self.p, dfs, pos, move |i, j| z[i].cmp(&z[j]));
        lca
    }
}

// TODO: line tree
// https://codeforces.com/blog/entry/71568

#[cfg(test)]
mod tests {
    use super::KRT;

    /// Helper to build LCA + RMQs and query the max-edge index over [l..r]
    fn max_edge_in_interval(
        krt: &mut KRT<impl FnMut(usize, usize, usize)>,
        l: usize,
        r: usize,
    ) -> usize {
        // run dfs to compute ss, pos, dfs order, depth
        let (_ss, pos, dfs, depth) = krt.dfs();
        // build the LCA and two RMQs
        let (mut rmq_min, mut rmq_max) = krt.leaf_pos_rmq(&pos);
        let mut lca = krt.lca(&dfs, &pos, &depth);
        // find the two extremal leaves
        let i = rmq_min.query(l..=r);
        let j = rmq_max.query(l..=r);
        // their LCA in the reconstruction tree
        let anc = lca.query(i, j);
        // internal edge idx stored at anc - original_n
        if anc < krt.n {
            // interval of size 1
            usize::MAX
        } else {
            krt.idx[anc - krt.n]
        }
    }

    #[test]
    fn test_single_leaf() {
        let mut krt = KRT::new(1, |_, _, _| {});
        // no edges to add
        assert_eq!(max_edge_in_interval(&mut krt, 0, 0), usize::MAX);
    }

    #[test]
    fn test_two_leaves() {
        let mut krt = KRT::new(2, |_, _, _| {});
        // add a single edge (0,1) with index 42
        krt.add_edge(0, 1, 42);
        assert_eq!(max_edge_in_interval(&mut krt, 0, 1), 42);
    }

    #[test]
    fn test_chain_of_three() {
        let mut krt = KRT::new(3, |_, _, _| {});
        // edges sorted by weight: (0-1)->5, (1-2)->7
        krt.add_edge(0, 1, 5).add_edge(1, 2, 7);
        // full span [0..2] should pick the heavier edge (index 7)
        assert_eq!(max_edge_in_interval(&mut krt, 0, 2), 7);
        // sub-span [0..1] => edge 5
        assert_eq!(max_edge_in_interval(&mut krt, 0, 1), 5);
        // sub-span [1..2] => edge 7
        assert_eq!(max_edge_in_interval(&mut krt, 1, 2), 7);
    }

    #[test]
    fn test_chain_of_four() {
        let mut krt = KRT::new(4, |_, _, _| {});
        // add edges in increasing "weight" order by idx
        krt.add_edge(0, 1, 1).add_edge(1, 2, 2).add_edge(2, 3, 3);
        // [0..3] => the max-index is 3
        assert_eq!(max_edge_in_interval(&mut krt, 0, 3), 3);
        // [1..3] => max-index among edges (1-2),(2-3) is 3
        assert_eq!(max_edge_in_interval(&mut krt, 1, 3), 3);
        // [2..3] => 3
        assert_eq!(max_edge_in_interval(&mut krt, 2, 3), 3);
    }

    #[test]
    fn test_star_topology() {
        let mut krt = KRT::new(4, |_, _, _| {});
        // We connect leaves 1,2,3 each to center 0:
        krt.add_edge(0, 1, 10).add_edge(0, 2, 20).add_edge(0, 3, 30);
        // in a star, the heaviest connection in any multi-leaf interval
        // is the maximum of those edge-indices
        assert_eq!(max_edge_in_interval(&mut krt, 1, 3), 30);
        assert_eq!(max_edge_in_interval(&mut krt, 2, 3), 30);
        assert_eq!(max_edge_in_interval(&mut krt, 1, 2), 20);
    }

    #[test]
    fn test_unordered_additions() {
        let mut krt = KRT::new(3, |_, _, _| {});
        // add in non-sorted order: but behavior requires sorted edges
        // here we simulate user error: the heavier edge is added first
        krt.add_edge(1, 2, 99).add_edge(0, 1, 11);
        // since we did 1-2 first, that edge becomes the first internal node,
        // then 0-1 merges the component {1,2} with 0, so second internal node
        // => [0..2] returns the idx of the second merge = 11
        assert_eq!(max_edge_in_interval(&mut krt, 0, 2), 11);
    }
}
