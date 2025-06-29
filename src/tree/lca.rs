use crate::range::rmq::RMQ;
use std::cmp::Ordering;

pub struct LCA<'a, F: FnMut(usize, usize) -> Ordering> {
    p: &'a [usize],
    dfs: &'a [usize],
    pos: &'a [usize],
    rmq: RMQ<F>,
}

impl<'a, F: FnMut(usize, usize) -> Ordering> LCA<'a, F> {
    /// O(n)
    /// cmp must be
    /// z\[i\].cmp(&z\[j\])
    /// where z\[i\] = depth\[p\[dfs\[i\]\]\]
    /// can't be done ahead of time without boxing
    pub fn new(n: usize, p: &'a [usize], dfs: &'a [usize], pos: &'a [usize], cmp: F) -> Self {
        Self {
            p,
            dfs,
            pos,
            rmq: RMQ::new(n, cmp),
        }
    }

    /// O(1)
    pub fn query(&mut self, a: usize, b: usize) -> usize {
        let (l, r) = if self.pos[a] <= self.pos[b] {
            (self.pos[a], self.pos[b])
        } else {
            (self.pos[b], self.pos[a])
        };
        if a == b {
            a
        } else {
            self.p[self.dfs[self.rmq.query(l + 1..=r)]]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LCA;
    use std::cmp::Ordering;

    /// Construct an LCA instance given parent array, DFS order, positions, and depths
    fn make_lca<'a>(
        p: &'a [usize],
        dfs: &'a [usize],
        pos: &'a [usize],
        depth: &'a [usize],
    ) -> LCA<'a, impl FnMut(usize, usize) -> Ordering> {
        let cmp = move |i: usize, j: usize| depth[dfs[i]].cmp(&depth[dfs[j]]);
        LCA::new(dfs.len(), p, dfs, pos, cmp)
    }

    #[test]
    fn test_simple_star() {
        // 0
        // |\
        // 1 2
        let p = vec![0, 0, 0];
        let depth = vec![0, 1, 1];
        let dfs = vec![0, 1, 2];
        let pos = vec![0, 1, 2];
        let mut lca = make_lca(&p, &dfs, &pos, &depth);
        assert_eq!(lca.query(1, 2), 0);
        assert_eq!(lca.query(1, 1), 1);
        assert_eq!(lca.query(0, 2), 0);
        assert_eq!(lca.query(2, 2), 2);
    }

    #[test]
    fn test_chain() {
        // 0 - 1 - 2 - 3
        let p = vec![0, 0, 1, 2];
        let depth = vec![0, 1, 2, 3];
        let dfs = vec![0, 1, 2, 3];
        let pos = vec![0, 1, 2, 3];
        let mut lca = make_lca(&p, &dfs, &pos, &depth);
        assert_eq!(lca.query(2, 3), 2);
        assert_eq!(lca.query(1, 3), 1);
        assert_eq!(lca.query(0, 3), 0);
        assert_eq!(lca.query(2, 2), 2);
    }

    #[test]
    fn test_balanced_binary() {
        //      0
        //    /   \
        //   1     2
        //  / \   / \
        // 3   4 5   6
        let p = vec![0, 0, 0, 1, 1, 2, 2];
        let depth = vec![0, 1, 1, 2, 2, 2, 2];
        let dfs = vec![0, 1, 3, 4, 2, 5, 6];
        let pos = vec![0, 1, 4, 2, 3, 5, 6];
        let mut lca = make_lca(&p, &dfs, &pos, &depth);
        assert_eq!(lca.query(3, 4), 1);
        assert_eq!(lca.query(3, 5), 0);
        assert_eq!(lca.query(4, 6), 0);
        assert_eq!(lca.query(5, 6), 2);
        assert_eq!(lca.query(6, 6), 6);
    }
}
