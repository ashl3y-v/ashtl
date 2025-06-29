use bit_vec::BitVec;

/// Heavy-light decomposition
/// MODE = 0 indicates values are on vertices, 1 is values are on edges
pub struct HLD<const MODE: u8> {
    pub n: usize,
    pub pos: Vec<usize>,
    pub rt: Vec<usize>,
    pub ss: Vec<usize>,
    pub tim: usize,
    pub p: Vec<usize>,
}

impl<const MODE: u8> HLD<MODE> {
    pub fn new(adj: &mut [Vec<usize>]) -> Self {
        let n = adj.len();
        let mut pos = vec![0; n];
        let mut rt = vec![0; n];
        let mut ss = vec![1; n];
        let mut tim = 0;
        let mut p = vec![usize::MAX; n];
        let mut stk = Vec::with_capacity(n);
        let mut done = BitVec::from_elem(n, false);
        stk.push((0, 0));
        while let Some((u, e)) = stk.last_mut() {
            let u = *u;
            if *e < adj[u].len() {
                let v = adj[u][*e];
                if v == p[u] {
                    *e += 1;
                    continue;
                }
                if done[v] {
                    ss[u] += ss[v];
                    if ss[v] > ss[adj[u][0]] {
                        adj[u].swap(0, *e);
                    }
                    *e += 1;
                } else {
                    p[v] = u;
                    stk.push((v, 0));
                }
            } else {
                done.set(u, true);
                stk.pop();
            }
        }
        stk.clear();
        done.clear();
        stk.push((0, 0));
        while let Some((u, e)) = stk.last_mut() {
            let u = *u;
            if *e < adj[u].len() {
                let v = adj[u][*e];
                if v == p[u] {
                    *e += 1;
                    continue;
                }
                if done[v] {
                    *e += 1;
                } else {
                    tim += 1;
                    pos[v] = tim;
                    rt[v] = if v == adj[u][0] { rt[u] } else { v };
                    stk.push((v, 0));
                }
            } else {
                done.set(u, true);
                stk.pop();
            }
        }
        Self {
            n,
            pos,
            rt,
            ss,
            tim,
            p,
        }
    }

    #[inline]
    pub fn lca(&self, mut u: usize, mut v: usize) -> usize {
        let (rt, p, pos) = (&self.rt, &self.p, &self.pos);
        while rt[u] != rt[v] {
            if pos[rt[u]] > pos[rt[v]] {
                u = p[rt[u]];
            } else {
                v = p[rt[v]];
            }
        }
        if pos[u] < pos[v] { u } else { v }
    }

    #[inline]
    /// calls o on (inclusive) ranges summing to path from u to v
    pub fn path(&self, mut u: usize, mut v: usize, mut o: impl FnMut(usize, usize)) -> &Self {
        let (rt, p, pos) = (&self.rt, &self.p, &self.pos);
        loop {
            if pos[u] > pos[v] {
                (u, v) = (v, u);
            }
            if rt[u] == rt[v] {
                break;
            }
            o(pos[rt[v]], pos[v]);
            v = p[rt[v]];
        }
        o(pos[u] + MODE as usize, pos[v]);
        self
    }

    /// calls o on (inclusive) range of subtree
    #[inline]
    pub fn subtree(&self, u: usize, o: impl FnOnce(usize, usize)) -> &Self {
        o(self.pos[u] + MODE as usize, self.pos[u] + self.ss[u] - 1);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashSet, VecDeque};

    /// Build an HLD from a list of edges and return both the HLD
    /// and the original adjacency (so we can validate against it).
    fn make_hld<const MODE: u8>(
        n: usize,
        edges: &[(usize, usize)],
    ) -> (Vec<Vec<usize>>, HLD<MODE>) {
        // build adjacency
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        // clone for validation before HLD mutates it
        let mut hld_adj = adj.clone();
        let hld = HLD::new(&mut hld_adj);
        (adj, hld)
    }

    fn build_adj(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        adj
    }

    /// Find the actual unique path between u and v by BFS.
    fn actual_path(n: usize, adj: &Vec<Vec<usize>>, u: usize, v: usize) -> Vec<usize> {
        let mut q = VecDeque::new();
        let mut parent = vec![None; n];
        parent[u] = Some(u);
        q.push_back(u);
        while let Some(x) = q.pop_front() {
            if x == v {
                break;
            }
            for &w in &adj[x] {
                if parent[w].is_none() {
                    parent[w] = Some(x);
                    q.push_back(w);
                }
            }
        }
        // reconstruct
        let mut path = Vec::new();
        let mut cur = v;
        while parent[cur] != Some(cur) {
            path.push(cur);
            cur = parent[cur].unwrap();
        }
        path.push(u);
        path.reverse();
        path
    }

    /// Compute parent pointers in the rooted tree at 0.
    fn compute_parent(n: usize, adj: &Vec<Vec<usize>>) -> Vec<Option<usize>> {
        let mut parent = vec![None; n];
        let mut q = VecDeque::new();
        parent[0] = Some(0);
        q.push_back(0);
        while let Some(u) = q.pop_front() {
            for &v in &adj[u] {
                if parent[v].is_none() {
                    parent[v] = Some(u);
                    q.push_back(v);
                }
            }
        }
        parent
    }

    /// Test that `hld.path(u,v,…)` covers exactly the vertices on the true tree path.
    fn check_all_pairs<const MODE: u8>(adj: &Vec<Vec<usize>>, hld: &HLD<MODE>) {
        let n = adj.len();
        // invert pos -> node
        let mut inv = vec![0; n];
        for i in 0..n {
            let p = hld.pos[i];
            assert!(p < n, "pos out of range for node {}", i);
            inv[p] = i;
        }

        for u in 0..n {
            for v in 0..n {
                // collect segments
                let mut segs = Vec::new();
                hld.path(u, v, |l, r| segs.push((l, r + 1)));
                // flatten
                let mut seen = HashSet::new();
                for (l, r) in segs {
                    for i in l..r {
                        // should never panic if pos/range correct
                        let node = inv[i];
                        seen.insert(node);
                        if u == 0 && v == 0 {
                            println!("{} {} {:?}", i, node, seen);
                        }
                    }
                }
                let actual = actual_path(n, adj, u, v)
                    .into_iter()
                    .collect::<HashSet<_>>();
                assert_eq!(
                    seen, actual,
                    "path mismatch between {} and {}: got {:?}, expected {:?}",
                    u, v, seen, actual
                );
            }
        }
    }

    /// Test that `hld.subtree(u,…)` covers exactly the descendants of u in the rooted tree.
    fn check_subtrees<const MODE: u8>(adj: &Vec<Vec<usize>>, hld: &HLD<MODE>) {
        let n = adj.len();
        let parent = compute_parent(n, adj);

        // invert pos -> node
        let mut inv = vec![0; n];
        for i in 0..n {
            let p = hld.pos[i];
            assert!(p < n, "pos out of range for node {}", i);
            inv[p] = i;
        }

        for u in 0..n {
            // collect HLD range
            let mut seen = HashSet::new();
            hld.subtree(u, |l, r| {
                for i in l..=r {
                    let node = inv[i];
                    seen.insert(node);
                }
            });
            // compute actual descendants
            let mut actual = HashSet::new();
            for v in 0..n {
                let mut x = Some(v);
                while let Some(px) = x {
                    if px == u {
                        actual.insert(v);
                        break;
                    }
                    if parent[px] == Some(px) {
                        // reached root
                        break;
                    }
                    x = parent[px];
                }
            }
            assert_eq!(
                seen, actual,
                "subtree mismatch at {}: got {:?}, expected {:?}",
                u, seen, actual
            );
        }
    }

    #[test]
    fn test_balanced_binary_tree() {
        // perfect binary tree of height 3, nodes 0..14
        let mut edges = Vec::new();
        for i in 0..7 {
            edges.push((i, 2 * i + 1));
            edges.push((i, 2 * i + 2));
        }
        let (adj0, hld0) = make_hld::<0>(15, &edges);
        check_all_pairs(&adj0, &hld0);
        check_subtrees(&adj0, &hld0);
    }

    #[test]
    fn test_random_tree_vertex_mode() {
        // small random tree; if RNG changes, still catches structure bugs
        let n = 20;
        let mut edges = Vec::new();
        for v in 1..n {
            // attach to a random earlier node
            edges.push((v, rand::random::<u64>() as usize % v));
        }
        let (adj0, hld0) = make_hld::<0>(n, &edges);
        check_all_pairs(&adj0, &hld0);
        check_subtrees(&adj0, &hld0);
    }

    #[test]
    fn test_hld_lca_chain() {
        // Chain: 0 - 1 - 2 - 3 - 4
        let edges = vec![(0, 1), (1, 2), (2, 3), (3, 4)];
        let mut adj = build_adj(5, &edges);
        let hld = HLD::<0>::new(&mut adj);
        // In a chain, LCA is the shallower node
        for (u, v) in (0..5).flat_map(|u| (0..5).map(move |v| (u, v))) {
            let expected = std::cmp::min(u, v);
            assert_eq!(
                hld.lca(u, v),
                expected,
                "LCA of {} and {} should be {}",
                u,
                v,
                expected
            );
        }
    }

    #[test]
    fn test_hld_lca_star() {
        // Star: 0 is center, leaves 1,2,3,4
        let edges = vec![(0, 1), (0, 2), (0, 3), (0, 4)];
        let mut adj = build_adj(5, &edges);
        let hld = HLD::<0>::new(&mut adj);
        // LCA of any two leaves is 0, and leaf with center is leaf
        for u in 1..5 {
            assert_eq!(hld.lca(u, u), u);
            assert_eq!(hld.lca(0, u), 0);
            assert_eq!(hld.lca(u, 0), 0);
            for v in 1..5 {
                let expect = if u == v { u } else { 0 };
                assert_eq!(hld.lca(u, v), expect, "LCA of {} and {}", u, v);
            }
        }
    }

    #[test]
    fn test_hld_lca_balanced_binary() {
        // Balanced binary tree of 7 nodes
        //      0
        //    /   \
        //   1     2
        //  / \   / \
        // 3   4 5   6
        let edges = vec![(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)];
        let mut adj = build_adj(7, &edges);
        let hld = HLD::<0>::new(&mut adj);
        let test_cases = vec![
            (3, 4, 1),
            (3, 5, 0),
            (4, 6, 0),
            (5, 6, 2),
            (3, 3, 3),
            (0, 6, 0),
        ];
        for (u, v, exp) in test_cases {
            assert_eq!(
                hld.lca(u, v),
                exp,
                "LCA of {} and {} should be {}",
                u,
                v,
                exp
            );
            assert_eq!(
                hld.lca(v, u),
                exp,
                "LCA of {} and {} should be {} (sym)",
                v,
                u,
                exp
            );
        }
    }
}
