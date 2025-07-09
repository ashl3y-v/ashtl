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

// builds jmp table for binary lifting in O(n)
pub fn build_jmp(par: &[usize], dfs: &[usize], depth: &[usize]) -> Vec<usize> {
    let n = par.len();
    let mut jmp = vec![0; n];
    for &v in dfs {
        let p = par[v];
        if v == p {
            jmp[v] = v;
        } else {
            let pj = jmp[p];
            let ppj = jmp[pj];
            if depth[p] - depth[pj] == depth[pj] - depth[ppj] {
                jmp[v] = ppj;
            } else {
                jmp[v] = p;
            }
        }
    }
    jmp
}

// O(log n)
pub fn depth_jmp(mut u: usize, d: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    while depth[u] > d {
        if depth[jmp[u]] < d {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

// O(log n)
pub fn search_jmp(
    mut u: usize,
    mut p: impl FnMut(usize) -> bool,
    par: &[usize],
    jmp: &[usize],
) -> usize {
    while !p(u) {
        if p(jmp[u]) {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

// O(log n)
pub fn lca_jmp(mut u: usize, mut v: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    if depth[u] > depth[v] {
        (u, v) = (v, u);
    }
    v = depth_jmp(v, depth[u], par, jmp, depth);
    while u != v {
        if jmp[u] == jmp[v] {
            (u, v) = (par[u], par[v]);
        } else {
            (u, v) = (jmp[u], jmp[v]);
        }
    }
    u
}

// TODO: level ancestor, ladder decomposition
// https://codeforces.com/blog/entry/126580
// https://codeforces.com/blog/entry/52062?#comment-360824
// https://codeforces.com/blog/entry/71567?#comment-559299
// https://courses.csail.mit.edu/6.851/spring21/lectures/L15.html?notes=8

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

    use super::{build_jmp, depth_jmp, lca_jmp, search_jmp};

    /// Utility: build parent/dfs/depth for chain of length n
    fn chain(n: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        let mut parent = vec![0; n];
        let mut depth = vec![0; n];
        let mut dfs = Vec::with_capacity(n);
        for v in 0..n {
            parent[v] = if v == 0 { 0 } else { v - 1 };
            depth[v] = v;
            dfs.push(v);
        }
        (parent, dfs, depth)
    }

    /// Utility: build parent/dfs/depth for star with center 0
    fn star(n: usize) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        let parent = vec![0; n];
        let mut depth = vec![1; n];
        depth[0] = 0;
        let dfs = (0..n).collect();
        (parent, dfs, depth)
    }

    /// Utility: build parent/dfs/depth for small binary tree
    ///      0
    ///    /   \
    ///   1     2
    ///  / \   / \
    /// 3  4  5   6
    fn bin_tree() -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        let parent = vec![0, 0, 0, 1, 1, 2, 2];
        let dfs = vec![0, 1, 3, 4, 2, 5, 6];
        let depth = vec![0, 1, 1, 2, 2, 2, 2];
        (parent, dfs, depth)
    }

    #[test]
    fn test_build_jmp_chain_and_star() {
        // Chain
        let (par, dfs, depth) = chain(5);
        let jmp = build_jmp(&par, &dfs, &depth);
        assert_eq!(jmp, vec![0, 0, 1, 0, 3]);

        // Star
        let (par2, dfs2, depth2) = star(5);
        let jmp2 = build_jmp(&par2, &dfs2, &depth2);
        assert_eq!(jmp2, vec![0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_depth_jmp_on_chain() {
        let (par, dfs, depth) = chain(5);
        let jmp = build_jmp(&par, &dfs, &depth);
        // climb 4->2
        assert_eq!(depth_jmp(4, 2, &par, &jmp, &depth), 2);
        // climb 4->0
        assert_eq!(depth_jmp(4, 0, &par, &jmp, &depth), 0);
        // no climb when already at depth
        assert_eq!(depth_jmp(3, 3, &par, &jmp, &depth), 3);
    }

    #[test]
    fn test_search_jmp_on_chain() {
        let (par, dfs, depth) = chain(5);
        let jmp = build_jmp(&par, &dfs, &depth);
        // find first even ancestor
        let is_even = |x: usize| x % 2 == 0;
        assert_eq!(search_jmp(3, is_even, &par, &jmp), 2);
        assert_eq!(search_jmp(4, is_even, &par, &jmp), 4);
    }

    #[test]
    fn test_lca_jmp_chain() {
        let (par, dfs, depth) = chain(5);
        let jmp = build_jmp(&par, &dfs, &depth);
        // lca in a chain is the shallower node
        assert_eq!(lca_jmp(3, 4, &par, &jmp, &depth), 3);
        assert_eq!(lca_jmp(1, 4, &par, &jmp, &depth), 1);
        assert_eq!(lca_jmp(2, 3, &par, &jmp, &depth), 2);
    }

    #[test]
    fn test_lca_jmp_binary_tree() {
        let (par, dfs, depth) = bin_tree();
        let jmp = build_jmp(&par, &dfs, &depth);
        // siblings under same parent
        assert_eq!(lca_jmp(3, 4, &par, &jmp, &depth), 1);
        assert_eq!(lca_jmp(5, 6, &par, &jmp, &depth), 2);
        // nodes in different subtrees
        assert_eq!(lca_jmp(3, 5, &par, &jmp, &depth), 0);
        assert_eq!(lca_jmp(4, 6, &par, &jmp, &depth), 0);
    }
}
