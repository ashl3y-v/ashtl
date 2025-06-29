use crate::ds::score::MaxScore;
use bit_vec::BitVec;
use std::collections::{BinaryHeap, HashMap, HashSet};

// DSatur coloring
// O((n + m) log n)
pub fn dsatur(adj: &[Vec<usize>]) -> (HashMap<usize, usize>, usize) {
    let n = adj.len();
    let mut deg = vec![0; n];
    let mut q = BinaryHeap::with_capacity(n);
    let mut cols = HashMap::with_capacity(n);
    let mut adj_cols = vec![HashSet::new(); n];
    let mut seen = BitVec::from_elem(n, false);
    let mut max_col = 0;
    for u in 0..n {
        let d = adj[u].len();
        q.push(MaxScore((0, d), u));
        deg[u] = d;
    }
    while let Some(MaxScore(_, u)) = q.pop() {
        if seen[u] {
            continue;
        }
        seen.set(u, true);
        let adj_col = &adj_cols[u];
        let mut col = 0;
        while adj_col.contains(&col) {
            col += 1;
        }
        cols.insert(u, col);
        max_col = max_col.max(col);
        for &v in &adj[u] {
            if let Some(adj_col) = adj_cols.get_mut(v) {
                adj_col.insert(col);
                q.push(MaxScore((adj_col.len(), deg[v]), v));
            }
        }
    }

    (cols, max_col + 1)
}

#[cfg(test)]
mod tests {
    use super::dsatur;
    use std::collections::HashMap;

    /// Helper: verify coloring uses k colors and no adjacent vertices share a color
    fn verify_coloring(adj: &[Vec<usize>], cols: &HashMap<usize, usize>, k: usize) {
        // check color count
        let used: std::collections::HashSet<_> = cols.values().cloned().collect();
        assert_eq!(used.len(), k);
        // check valid colors and adjacency
        for u in 0..adj.len() {
            let cu = cols.get(&u).expect("Missing color");
            assert!(*cu < k, "Color out of range");
            for &v in &adj[u] {
                let cv = cols.get(&v).expect("Missing color");
                assert_ne!(cu, cv, "Adjacent nodes {} and {} share color {}", u, v, cu);
            }
        }
    }

    #[test]
    fn test_bipartite_path() {
        // Path graph on 5 nodes
        let adj = vec![
            vec![1],    // 0
            vec![0, 2], // 1
            vec![1, 3], // 2
            vec![2, 4], // 3
            vec![3],    // 4
        ];
        let (cols, k) = dsatur(&adj);
        // Path is bipartite -> 2 colors
        verify_coloring(&adj, &cols, 2);
    }

    #[test]
    fn test_complete_graph() {
        // Complete graph K4 -> 4 colors
        let n = 4;
        let mut adj = vec![vec![]; n];
        for u in 0..n {
            for v in u + 1..n {
                adj[u].push(v);
                adj[v].push(u);
            }
        }
        let (cols, k) = dsatur(&adj);
        verify_coloring(&adj, &cols, 4);
    }

    #[test]
    fn test_cycle_even_odd() {
        // Cycle of length 6 (even)
        let n_even = 6;
        let mut adj_even = vec![vec![]; n_even];
        for u in 0..n_even {
            let v = (u + 1) % n_even;
            adj_even[u].push(v);
            adj_even[v].push(u);
        }
        let (cols_even, k_even) = dsatur(&adj_even);
        // Even cycle -> 2 colors
        verify_coloring(&adj_even, &cols_even, 2);

        // Cycle of length 5 (odd)
        let n_odd = 5;
        let mut adj_odd = vec![vec![]; n_odd];
        for u in 0..n_odd {
            let v = (u + 1) % n_odd;
            adj_odd[u].push(v);
            adj_odd[v].push(u);
        }
        let (cols_odd, k_odd) = dsatur(&adj_odd);
        // Odd cycle -> 3 colors
        verify_coloring(&adj_odd, &cols_odd, 3);
    }

    #[test]
    fn test_complete_bipartite() {
        // Complete bipartite K3,4 -> 2 colors
        let left = 3;
        let right = 4;
        let n = left + right;
        let mut adj = vec![vec![]; n];
        for u in 0..left {
            for v in left..n {
                adj[u].push(v);
                adj[v].push(u);
            }
        }
        let (cols, k) = dsatur(&adj);
        verify_coloring(&adj, &cols, 2);
    }

    #[test]
    fn test_wheel_graph() {
        // Wheel on 5 vertices: cycle of 4 + center -> 3 colors
        let cycle_n = 4;
        let n = cycle_n + 1;
        let mut adj = vec![vec![]; n];
        // cycle edges
        for u in 0..cycle_n {
            let v = (u + 1) % cycle_n;
            adj[u].push(v);
            adj[v].push(u);
        }
        // center
        let center = cycle_n;
        for u in 0..cycle_n {
            adj[u].push(center);
            adj[center].push(u);
        }
        let (cols, k) = dsatur(&adj);
        verify_coloring(&adj, &cols, 3);

        // Wheel on 6 vertices (odd cycle length =5) -> 4 colors
        let cycle_n2 = 5;
        let n2 = cycle_n2 + 1;
        let mut adj2 = vec![vec![]; n2];
        for u in 0..cycle_n2 {
            let v = (u + 1) % cycle_n2;
            adj2[u].push(v);
            adj2[v].push(u);
        }
        let center2 = cycle_n2;
        for u in 0..cycle_n2 {
            adj2[u].push(center2);
            adj2[center2].push(u);
        }
        let (cols2, k2) = dsatur(&adj2);
        verify_coloring(&adj2, &cols2, 4);
    }
}
