use bit_vec::BitVec;
use std::ops::Add;

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

pub fn spfa<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> Result<(Vec<Option<T>>, Vec<usize>), (usize, Vec<Option<T>>, Vec<usize>)> {
    let n = adj.len();
    let mut p = vec![usize::MAX; n];
    let mut d = vec![None; n];
    d[v] = Some(T::default());
    let mut q = Vec::with_capacity(n);
    let mut in_q = BitVec::from_elem(n, false);
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

pub fn recover_negative_cycle<T>(v: usize, d: &[T], p: &[usize]) -> Vec<usize> {
    let n = d.len();
    let mut path = Vec::new();
    let start = v;
    let mut node = start;
    let mut visited = BitVec::from_elem(n, false);
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

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to unwrap Option<T> for test comparisons or panic
    fn unwrap_dist<T: std::fmt::Debug>(d: Option<T>) -> T {
        d.expect("Distance should be Some")
    }

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
}
