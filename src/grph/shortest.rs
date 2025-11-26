use crate::ds::bit_vec::BitVec;
use crate::ds::score::MinScore;
use std::{collections::BinaryHeap, ops::Add};

/// O(n m)
pub fn bellman_ford<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> Result<(Vec<Option<T>>, Vec<usize>), (usize, Vec<Option<T>>, Vec<usize>)> {
    let n = adj.len();
    let (d, p) = bellman_ford_unchecked(v, adj);
    for i in 0..n {
        if let Some(d_i) = d[i] {
            for &(j, w) in &adj[i] {
                let dist = d_i + w;
                if d[j].is_none() || Some(dist) < d[j] {
                    return Err((i, d, p));
                }
            }
        }
    }
    Ok((d, p))
}

/// O(n m)
pub fn spfa<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> Result<(Vec<Option<T>>, Vec<usize>), (usize, Vec<Option<T>>, Vec<usize>)> {
    let n = adj.len();
    let mut p = vec![usize::MAX; n];
    let mut d = vec![None; n];
    d[v] = Some(T::default());
    let mut q = Vec::with_capacity(n);
    let mut in_q = BitVec::new(n, false);
    q.push(v);
    in_q.set(v, true);
    let mut visits = vec![0; n];
    while let Some(i) = q.pop() {
        in_q.set(i, false);
        if visits[i] >= n {
            return Err((i, d, p));
        }
        visits[i] += 1;
        if let Some(d_i) = d[i] {
            for &(j, w) in &adj[i] {
                let dist = d_i + w;
                if d[j].is_none() || Some(dist) < d[j] {
                    d[j] = Some(dist);
                    p[j] = i;
                    if !in_q[j] {
                        in_q.set(j, true);
                        q.push(j);
                    }
                }
            }
        }
    }
    Ok((d, p))
}

/// O(n)
pub fn recover_negative_cycle<T>(v: usize, d: &[T], p: &[usize]) -> Vec<usize> {
    let n = d.len();
    let mut path = Vec::new();
    let start = v;
    let mut node = start;
    let mut visited = BitVec::new(n, false);
    loop {
        let ancestor = if p[node] == usize::MAX { node } else { p[node] };
        if ancestor == start {
            path.push(ancestor);
            break;
        } else if visited[ancestor] {
            let pos = path.iter().position(|&p| p == ancestor).unwrap();
            path = path[pos..].to_vec();
            break;
        }
        path.push(ancestor);
        visited.set(ancestor, true);
        node = ancestor;
    }
    path.reverse();
    path
}

/// O(n m)
pub fn bellman_ford_unchecked<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> (Vec<Option<T>>, Vec<usize>) {
    let n = adj.len();
    let mut p = vec![usize::MAX; n];
    let mut d = vec![None; n];
    d[v] = Some(T::default());
    for _ in 0..n {
        let mut did_update = false;
        for i in 0..n {
            if let Some(d_i) = d[i] {
                for &(j, w) in &adj[i] {
                    let dist = d_i + w;
                    if d[j].is_none() || Some(dist) < d[j] {
                        d[j] = Some(dist);
                        p[j] = i;
                        did_update = true;
                    }
                }
            }
        }
        if !did_update {
            break;
        }
    }
    (d, p)
}

/// O((n + m) log n)
/// Works for any type T such that:
/// For source T::default() is correct initialization
/// sum(p) + v >= sum(p) if v adjacent to end of p
/// if p, q have same end and sum(p) >= sum(q), then sum(p) + v >= sum(q) + v for all v adjacent to end
/// https://codeforces.com/blog/entry/107810
pub fn dijkstra<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    u: usize,
    v: Option<usize>,
    adj: &[Vec<(usize, T)>],
) -> Vec<Option<T>> {
    let n = adj.len();
    let mut seen = BitVec::new(n, false);
    let mut scores = vec![None; n];
    let mut visit = BinaryHeap::new();
    scores[u] = Some(T::default());
    visit.push(MinScore(T::default(), u));
    while let Some(MinScore(s, i)) = visit.pop() {
        if seen[i] {
            continue;
        }
        if v == Some(i) {
            break;
        }
        for &(j, w) in &adj[i] {
            if seen[j] {
                continue;
            }
            let ns = s + w;
            if scores[j].is_none() || Some(ns) < scores[j] {
                scores[j] = Some(ns);
                visit.push(MinScore(ns, j));
            }
        }
        seen.set(i, true);
    }
    scores
}

/// O(n^3)
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

/// O(n)
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

    // 1) Simple 3‐node positive‐weight graph
    //
    //    0 →1→ 1 →2→ 2
    #[test]
    fn test_simple_positive() {
        let adj = vec![
            vec![(1, 1)], // 0→1 (1)
            vec![(2, 2)], // 1→2 (2)
            vec![],       // 2
        ];
        let (d, p) = bellman_ford(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0), Some(1), Some(3)]);
        assert_eq!(p, vec![usize::MAX, 0, 1]);
    }

    // 2) Negative edges but no cycle
    //
    //    0 →1→ 1 →(-2)→ 2
    #[test]
    fn test_negative_edge_no_cycle() {
        let adj = vec![
            vec![(1, 1)],  // 0→1 (1)
            vec![(2, -2)], // 1→2 (-2)
            vec![],        // 2
        ];
        let (d, p) = bellman_ford(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0), Some(1), Some(-1)]);
        assert_eq!(p, vec![usize::MAX, 0, 1]);
    }

    // 3) Tiny negative cycle: 0→1→2→0
    #[test]
    fn test_detect_negative_cycle() {
        // cycle weights: 0→1 (-1), 1→2 (0), 2→0 (0)
        let adj = vec![
            vec![(1, -1)], // 0→1
            vec![(2, 0)],  // 1→2
            vec![(0, 0)],  // 2→0
        ];
        if let Err((v, d, p)) = bellman_ford(0, &adj) {
            let path = recover_negative_cycle(v, &d, &p);
            // cycle must include all three in some rotation
            assert_eq!(path.len(), 3);
            assert!(path.contains(&0) && path.contains(&1) && path.contains(&2));
            assert_eq!(d.len(), 3);
            assert_eq!(p.len(), 3);
        } else {
            panic!("Expected negative cycle detection");
        }
    }

    // 4) Disconnected components
    #[test]
    fn test_disconnected_graph() {
        let adj = vec![
            vec![(1, 5)], // component A
            vec![],
            vec![(3, 7)], // component B
            vec![],
        ];
        // start at 0: nodes 2,3 unreachable
        let (d, p) = bellman_ford(0, &adj).unwrap();
        assert_eq!(d[0], Some(0));
        assert_eq!(d[1], Some(5));
        assert_eq!(d[2], None);
        assert_eq!(d[3], None);
        assert_eq!(p[2], usize::MAX);
    }

    // 5) Single‐vertex graph trivially has no cycle
    #[test]
    fn test_single_vertex() {
        let adj: Vec<Vec<(usize, i64)>> = vec![vec![]];
        let (d, p) = bellman_ford(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0)]);
        assert_eq!(p, vec![usize::MAX]);
    }

    #[test]
    fn test_simple_positive_spfa() {
        let adj = vec![
            vec![(1, 1)], // 0→1 (1)
            vec![(2, 2)], // 1→2 (2)
            vec![],       // 2
        ];
        let (d, p) = spfa(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0), Some(1), Some(3)]);
        assert_eq!(p, vec![usize::MAX, 0, 1]);
    }

    #[test]
    fn test_negative_edge_no_cycle_spfa() {
        let adj = vec![
            vec![(1, 1)],  // 0→1 (1)
            vec![(2, -2)], // 1→2 (-2)
            vec![],        // 2
        ];
        let (d, p) = spfa(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0), Some(1), Some(-1)]);
        assert_eq!(p, vec![usize::MAX, 0, 1]);
    }

    #[test]
    fn test_detect_negative_cycle_spfa() {
        // cycle weights: 0→1 (-1), 1→2 (0), 2→0 (0)
        let adj = vec![
            vec![(1, -1)], // 0→1
            vec![(2, 0)],  // 1→2
            vec![(0, 0)],  // 2→0
        ];
        if let Err((v, d, p)) = spfa(0, &adj) {
            let path = recover_negative_cycle(v, &d, &p);
            // cycle must include all three in some rotation
            assert_eq!(path.len(), 3);
            assert!(path.contains(&0) && path.contains(&1) && path.contains(&2));
            assert_eq!(d.len(), 3);
            assert_eq!(p.len(), 3);
        } else {
            panic!("Expected negative cycle detection");
        }
    }

    #[test]
    fn test_disconnected_graph_spfa() {
        let adj = vec![
            vec![(1, 5)], // component A
            vec![],
            vec![(3, 7)], // component B
            vec![],
        ];
        // start at 0: nodes 2,3 unreachable
        let (d, p) = spfa(0, &adj).unwrap();
        assert_eq!(d[0], Some(0));
        assert_eq!(d[1], Some(5));
        assert_eq!(d[2], None);
        assert_eq!(d[3], None);
        assert_eq!(p[2], usize::MAX);
    }

    #[test]
    fn test_single_vertex_spfa() {
        let adj: Vec<Vec<(usize, i64)>> = vec![vec![]];
        let (d, p) = spfa(0, &adj).unwrap();
        assert_eq!(d, vec![Some(0)]);
        assert_eq!(p, vec![usize::MAX]);
    }

    #[test]
    fn test_or_distance() {
        #[derive(Clone, Copy, PartialEq, PartialOrd, Default, Debug)]
        struct W(u32);
        impl std::ops::Add for W {
            type Output = W;
            fn add(self, W(j): W) -> Self::Output {
                let W(i) = self;
                W(i | j)
            }
        }

        let adj = vec![
            vec![(1, W(1)), (2, W(4))],
            vec![(2, W(3)), (3, W(5))],
            vec![(3, W(4))],
            vec![],
        ];
        let (dist, _) = spfa(0, &adj).unwrap();
        assert_eq!(dist[3], Some(W(4)));
    }

    /// Simple 3-node line graph: 0→1 (5), 0→2 (10), 1→2 (3)
    fn linear_graph() -> Vec<Vec<(usize, i32)>> {
        vec![vec![(1, 5), (2, 10)], vec![(2, 3)], vec![]]
    }

    #[test]
    fn test_simple_line() {
        let adj = linear_graph();
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(5), Some(8)],
            "0→1 should be 5, 0→2 via 1 should be 8"
        );
    }

    #[test]
    fn test_unreachable() {
        // Two isolated nodes
        let adj: Vec<Vec<(usize, i32)>> = vec![vec![], vec![]];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), None],
            "Node 1 is unreachable and should remain at max"
        );
    }

    #[test]
    fn test_single_node() {
        let adj: Vec<Vec<(usize, i32)>> = vec![vec![]];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0)],
            "Single-node graph distance is zero to itself"
        );
    }

    #[test]
    fn test_target_early_exit() {
        let adj = linear_graph();
        // Asking for target=2 should break out early once distance to 2 is finalized
        let dist = dijkstra(0, Some(2), &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(5), Some(8)],
            "Early exit must still record correct distances"
        );
    }

    #[test]
    fn test_multiple_paths() {
        // Graph:
        // 0→1 (1), 0→2 (4)
        // 1→2 (1), 1→3 (5)
        // 2→3 (1)
        let adj = vec![
            vec![(1, 1), (2, 4)],
            vec![(2, 1), (3, 5)],
            vec![(3, 1)],
            vec![],
        ];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(1), Some(2), Some(3)],
            "Should pick the shortest paths 0→1→2→3"
        );
    }

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
    fn test_simple_positive_floyd_warshall() {
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
    fn test_unreachable_floyd_warshall() {
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
