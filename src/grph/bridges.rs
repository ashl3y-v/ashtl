pub fn bridges(adj: &Vec<Vec<usize>>) -> (usize, Vec<(usize, usize)>, Vec<isize>, Vec<usize>) {
    let n = adj.len();
    let mut depth = vec![0usize; n];
    let mut dp = vec![0isize; n];
    let mut bridges = Vec::new();
    let mut bridgec = 0usize;
    fn visit(
        v: usize,
        p: usize,
        adj: &Vec<Vec<usize>>,
        lvl: &mut [usize],
        dp: &mut [isize],
        bridgec: &mut usize,
        bridges: &mut Vec<(usize, usize)>,
    ) {
        for &nxt in &adj[v] {
            if lvl[nxt] == 0 {
                lvl[nxt] = lvl[v] + 1;
                visit(nxt, v, adj, lvl, dp, bridgec, bridges);
                dp[v] += dp[nxt];
            } else if lvl[nxt] < lvl[v] {
                dp[v] += 1;
            } else if lvl[nxt] > lvl[v] {
                dp[v] -= 1;
            }
        }
        dp[v] -= 1;
        if lvl[v] > 1 && dp[v] == 0 {
            bridges.push((v, p));
            *bridgec += 1;
        }
    }
    for i in 0..n {
        if depth[i] == 0 {
            depth[i] = 1;
            visit(
                i,
                usize::MAX,
                adj,
                &mut depth,
                &mut dp,
                &mut bridgec,
                &mut bridges,
            );
        }
    }
    (bridgec, bridges, dp, depth)
}

pub fn count_bridges(adj: &Vec<Vec<usize>>) -> (usize, Vec<isize>, Vec<usize>) {
    let n = adj.len();
    let mut depth = vec![0usize; n];
    let mut dp = vec![0isize; n];
    let mut bridgec = 0usize;
    fn visit(
        v: usize,
        adj: &Vec<Vec<usize>>,
        lvl: &mut [usize],
        dp: &mut [isize],
        bridgec: &mut usize,
    ) {
        for &nxt in &adj[v] {
            if lvl[nxt] == 0 {
                lvl[nxt] = lvl[v] + 1;
                visit(nxt, adj, lvl, dp, bridgec);
                dp[v] += dp[nxt];
            } else if lvl[nxt] < lvl[v] {
                dp[v] += 1;
            } else if lvl[nxt] > lvl[v] {
                dp[v] -= 1;
            }
        }
        dp[v] -= 1;
        if lvl[v] > 1 && dp[v] == 0 {
            *bridgec += 1;
        }
    }
    for i in 0..n {
        if depth[i] == 0 {
            depth[i] = 1;
            visit(i, adj, &mut depth, &mut dp, &mut bridgec);
        }
    }
    (bridgec, dp, depth)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Utility: build undirected adjacency list
    fn make_graph(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        adj
    }

    #[test]
    fn test_empty_graph() {
        let adj: Vec<Vec<usize>> = Vec::new();
        let (c1, bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 0);
        assert!(bs.is_empty());
        assert!(dp1.is_empty());
        assert!(dep1.is_empty());
        assert_eq!(c1, c2);
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_single_node() {
        let adj = make_graph(1, &[]);
        let (c1, bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 0);
        assert!(bs.is_empty());
        assert_eq!(dp1, vec![-1]);
        assert_eq!(dep1, vec![1]);
        assert_eq!(c1, c2);
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_chain() {
        // 0-1-2
        let adj = make_graph(3, &[(0, 1), (1, 2)]);
        let (c1, mut bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 2);
        // bridges: (2,1) and (1,0)
        bs.sort();
        assert_eq!(bs, vec![(1, 0), (2, 1)]);
        assert_eq!(dp1, vec![-1, 0, 0]);
        assert_eq!(dep1, vec![1, 2, 3]);
        assert_eq!(c1, c2);
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_cycle() {
        // triangle: 0-1-2-0
        let adj = make_graph(3, &[(0, 1), (1, 2), (2, 0)]);
        let (c1, bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 0);
        assert!(bs.is_empty());
        // in a cycle, dp values are all -1 (one back-edge each)
        assert_eq!(dp1, vec![-1, 1, 1]);
        // depth is 1,2,3 or some spanning tree ordering
        assert_eq!(dep1.len(), 3);
        assert_eq!(c1, c2);
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_mixed_graph() {
        // 0-1-2-3 with extra edge 1-3 and tail 3-4
        let adj = make_graph(5, &[(0, 1), (1, 2), (2, 3), (1, 3), (3, 4)]);
        let (c1, mut bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 2);
        // expected bridges: (1,0) and (4,3)
        bs.sort();
        assert_eq!(bs, vec![(1, 0), (4, 3)]);
        // check dp and depth match between functions
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_disconnected() {
        // two components: 0-1, 2-3
        let adj = make_graph(4, &[(0, 1), (2, 3)]);
        let (c1, mut bs, dp1, dep1) = bridges(&adj);
        let (c2, dp2, dep2) = count_bridges(&adj);
        assert_eq!(c1, 2);
        bs.sort();
        assert_eq!(bs, vec![(1, 0), (3, 2)]);
        assert_eq!(dp1, dp2);
        assert_eq!(dep1, dep2);
        assert_eq!(c1, c2);
    }
}
