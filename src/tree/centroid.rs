use bit_vec::BitVec;

/// O(n log n + sum_{cd} F(cd)) where F(cd) is the cost of calling F on that centroid
pub fn centroid_decomp(
    adj: &[Vec<usize>],
    mut f: impl FnMut([usize; 3], &mut BitVec, &mut [usize]),
) {
    let n = adj.len();
    let mut is_removed = BitVec::from_elem(n, false);
    let mut ss = vec![0; n];
    let mut stk = Vec::with_capacity(n);
    let mut get_ss = |u, p, is_removed: &BitVec, ss: &mut [usize]| {
        stk.push((u, p, 0, 1));
        while let Some((u, p, idx_m, acc)) = stk.last_mut() {
            let (u, p, idx, acc) = (*u, *p, *idx_m, *acc);
            let ws: &Vec<usize> = &adj[u];
            if idx < ws.len() {
                let v = ws[idx];
                *idx_m += 1;
                if v != p && !is_removed[v] {
                    stk.push((v, u, 0, 1));
                }
            } else {
                stk.pop();
                ss[u] = acc;
                if let Some(top) = stk.last_mut() {
                    top.3 += acc;
                }
            }
        }
        ss[u]
    };
    let mut stk = Vec::with_capacity(n);
    stk.push((0, usize::MAX, 0));
    while let Some((u, pcd, d)) = stk.pop() {
        let mut v = u;
        let mut p = usize::MAX;
        let tree_size = get_ss(u, usize::MAX, &is_removed, &mut ss);
        let cd = 'a: loop {
            for &w in &adj[v] {
                if w != p && !is_removed[w] && ss[w] * 2 > tree_size {
                    (p, v) = (v, w);
                    continue 'a;
                }
            }
            break v;
        };
        f([cd, pcd, d], &mut is_removed, &mut ss);
        is_removed.set(cd, true);
        for &v in &adj[cd] {
            if !is_removed[v] {
                stk.push((v, cd, d + 1));
            }
        }
    }
}

// TODO: shallowest decomposition tree
// https://codeforces.com/blog/entry/125018

// TODO: contour
// https://judge.yosupo.jp/submission/260870
// https://judge.yosupo.jp/submission/260575

#[cfg(test)]
mod tests {
    use super::centroid_decomp;
    use bit_vec::BitVec;
    use std::usize;

    /// Run centroid decomposition and record the parent of each centroid.
    fn build_centroid_parents(adj: &[Vec<usize>]) -> Vec<usize> {
        let n = adj.len();
        let mut parent_cd = vec![usize::MAX; n];
        // Closure f: record parent as the removed neighbor
        let mut f = |[cd, pcd, _]: [usize; 3], _: &mut BitVec, _: &mut [usize]| {
            parent_cd[cd] = pcd;
        };
        centroid_decomp(adj, &mut f);
        parent_cd
    }

    #[test]
    fn test_centroid_chain() {
        // Chain 0-1-2-3-4
        let n = 5;
        let edges = [(0, 1), (1, 2), (2, 3), (3, 4)];
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in &edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        let parent_cd = build_centroid_parents(&adj);
        // Expected centroid tree: 2 is root; children 3 and 1; then 4->3, 0->1
        let expected = vec![1, 2, usize::MAX, 2, 3];
        assert_eq!(parent_cd, expected);
    }

    #[test]
    fn test_centroid_star() {
        // Star: 0 center, leaves 1-4
        let n = 5;
        let mut adj = vec![vec![]; n];
        for leaf in 1..5 {
            adj[0].push(leaf);
            adj[leaf].push(0);
        }
        let parent_cd = build_centroid_parents(&adj);
        // Expected: 0 is root, leaves attach to 0
        let mut expected = vec![usize::MAX; n];
        for i in 1..n {
            expected[i] = 0;
        }
        assert_eq!(parent_cd, expected);
    }

    #[test]
    fn test_centroid_balanced() {
        // Balanced binary tree of 7 nodes
        //       0
        //     /   \
        //    1     2
        //   / \   / \
        //  3   4 5   6
        let n = 7;
        let edges = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)];
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in &edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        let parent_cd = build_centroid_parents(&adj);
        // Expected centroid tree:
        // 0: root
        // 1->0,2->0
        // 3->1,4->1,5->2,6->2
        let expected = vec![usize::MAX, 0, 0, 1, 1, 2, 2];
        assert_eq!(parent_cd, expected);
    }
}
