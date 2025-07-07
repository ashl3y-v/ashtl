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

#[cfg(test)]
mod tests {
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
        let mut parent = vec![0; n];
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
