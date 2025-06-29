pub fn floyd_warshall(d: &mut [Vec<i64>], mut p: Option<&mut [Vec<usize>]>) {
    let n = d.len();
    for i in 0..n {
        d[i][i] = d[i][i].min(0);
    }
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                let (dist, overflow) = d[i][k].overflowing_add(d[k][j]);
                if !overflow && d[i][j] > dist {
                    d[i][j] = dist;
                    if let Some(ref mut p) = p {
                        p[i][j] = p[k][j];
                    }
                }
            }
        }
    }
    for k in 0..n {
        if d[k][k] < 0 {
            for i in 0..n {
                for j in 0..n {
                    if d[i][k] != i64::MAX && d[k][j] != i64::MAX {
                        d[i][j] = i64::MIN;
                    }
                }
            }
        }
    }
}

pub fn recover_path(u: usize, v: usize, p: &[Vec<usize>]) -> Vec<usize> {
    if u == v {
        return vec![u];
    }
    if p[u][v] == usize::MAX {
        return Vec::new();
    }
    let mut path = Vec::new();
    let mut cur = v;
    path.push(cur);
    while cur != u {
        cur = p[u][cur];
        path.push(cur);
    }
    path.reverse();
    path
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Initialize distance and predecessor matrices for a graph of size `n`.
    /// - d[i][j] = weight for each (i,j) in `edges`, else i64::MAX
    /// - p[i][j] = i for each (i,j) in `edges`, p[i][i] = i, else usize::MAX
    fn init_dp(n: usize, edges: &[(usize, usize, i64)]) -> (Vec<Vec<i64>>, Vec<Vec<usize>>) {
        let mut d = vec![vec![i64::MAX; n]; n];
        let mut p = vec![vec![usize::MAX; n]; n];
        for i in 0..n {
            d[i][i] = 0;
            p[i][i] = i;
        }
        for &(u, v, w) in edges {
            d[u][v] = w;
            p[u][v] = u;
        }
        (d, p)
    }

    #[test]
    fn test_simple_positive() {
        // 0→1 (3), 0→2 (8), 1→2 (2), 1→3 (5), 2→3 (1)
        let edges = &[(0, 1, 3), (0, 2, 8), (1, 2, 2), (1, 3, 5), (2, 3, 1)];
        let n = 4;
        let (mut d, mut p) = init_dp(n, edges);
        floyd_warshall(&mut d, Some(&mut p));

        // Check a couple of distances
        assert_eq!(d[0][2], 5); // 0→1→2 = 3+2
        assert_eq!(d[0][3], 6); // 0→1→2→3 = 3+2+1

        // Check that recover_path gives the correct route
        let path = recover_path(0, 3, &p);
        assert_eq!(path, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_unreachable() {
        // Two disconnected components: 0↔1 and 2↔3
        let edges = &[(0, 1, 1), (2, 3, 1)];
        let n = 4;
        let (mut d, mut p) = init_dp(n, edges);
        floyd_warshall(&mut d, Some(&mut p));

        // 0→3 is unreachable
        assert_eq!(d[0][3], i64::MAX);
        assert!(recover_path(0, 3, &p).is_empty());
    }

    #[test]
    fn test_negative_weights() {
        // A graph with a negative edge but no cycle
        // 0→1 (4), 1→2 (-2), 2→3 (1), 0→3 (10)
        let edges = &[(0, 1, 4), (1, 2, -2), (2, 3, 1), (0, 3, 10)];
        let n = 4;
        let (mut d, mut p) = init_dp(n, edges);
        floyd_warshall(&mut d, Some(&mut p));

        // Best 0→3 is via 1,2: 4 + (-2) + 1 = 3
        assert_eq!(d[0][3], 3);

        let path = recover_path(0, 3, &p);
        assert_eq!(path, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_negative_cycle_detection() {
        // Create a 3-cycle with total weight -1: 0→1→2→0
        let edges = &[(0, 1, 1), (1, 2, -2), (2, 0, 0)];
        let n = 3;
        let (mut d, mut p) = init_dp(n, edges);
        floyd_warshall(&mut d, Some(&mut p));

        // Every pair in that cycle should become -∞ (i64::MIN)
        assert_eq!(d[0][1], i64::MIN);
        assert_eq!(d[1][2], i64::MIN);
        assert_eq!(d[2][0], i64::MIN);
        // And also transitive through the cycle...
        assert_eq!(d[0][0], i64::MIN);
        assert_eq!(d[1][1], i64::MIN);
        assert_eq!(d[2][2], i64::MIN);
    }

    #[test]
    fn test_self_negative_loop() {
        // A single-node negative self‐loop is itself a negative cycle
        let edges = &[(0, 0, -5)];
        let n = 1;
        let (mut d, mut p) = init_dp(n, edges);
        floyd_warshall(&mut d, Some(&mut p));

        // Should detect negative cycle and mark d[0][0] = -∞
        assert_eq!(d[0][0], i64::MIN);
    }

    #[test]
    fn test_trivial_paths() {
        // No edges at all ⇒ only trivial paths exist
        let n = 5;
        let (mut d, mut p) = init_dp(n, &[]);
        floyd_warshall(&mut d, Some(&mut p));

        // For every node u, the path u→u is [u]
        for u in 0..n {
            let path = recover_path(u, u, &p);
            assert_eq!(path, vec![u]);
            // And no nontrivial reachability
            for v in 0..n {
                if v != u {
                    assert!(recover_path(u, v, &p).is_empty());
                }
            }
        }
    }
}
