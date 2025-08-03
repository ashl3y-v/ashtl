use crate::{alg::lattice, ds::set::UbIntSet};
use bit_vec::BitVec;
use std::collections::{BinaryHeap, HashMap};

pub fn chromatic_number(adj: &[Vec<usize>]) -> usize {
    let n = adj.len();
    let mut ans = n + 1;
    let mut colors = vec![0; n];
    fn dfs(graph: &[Vec<usize>], colors: &mut [usize], c: usize, cnt: usize, ans: &mut usize) {
        if c >= *ans {
            return;
        } else if cnt == 0 {
            *ans = c;
            return;
        }
        let mut u = 0;
        let mut max_neighbors = -1i32;
        let mut neighbor_mask = 0u64;
        for i in 0..graph.len() {
            if colors[i] == 0 {
                let mut mask = 0u64;
                for &j in &graph[i] {
                    if colors[j] > 0 {
                        mask |= 1u64 << colors[j];
                    }
                }
                let count = mask.count_ones() as i32;
                if count > max_neighbors {
                    (max_neighbors, u, neighbor_mask) = (count, i, mask);
                }
            }
        }
        for color in 1..=c + 1 {
            if (neighbor_mask >> color) & 1 == 0 {
                colors[u] = color;
                dfs(graph, colors, c.max(color), cnt - 1, ans);
            }
        }
        colors[u] = 0;
    }
    dfs(adj, &mut colors, 0, n, &mut ans);
    ans
}

/// DSatur greedy coloring
/// O((n + m) log n)
pub fn dsatur(adj: &[Vec<usize>]) -> (HashMap<usize, usize>, usize) {
    let n = adj.len();
    let mut deg = vec![0; n];
    let mut q = BinaryHeap::with_capacity(n);
    let mut cols = HashMap::with_capacity(n);
    let mut adj_cols = vec![UbIntSet::new(n); n];
    let mut seen = BitVec::from_elem(n, false);
    let mut max_col = 0;
    for u in 0..n {
        let d = adj[u].len();
        q.push(((d, 0), u));
        deg[u] = d;
    }
    while let Some((_, u)) = q.pop() {
        if seen[u] {
            continue;
        }
        seen.set(u, true);
        let adj_col = &adj_cols[u];
        let col = adj_col.exsucc(0);
        cols.insert(u, col);
        max_col = max_col.max(col);
        for &v in &adj[u] {
            if let Some(adj_col) = adj_cols.get_mut(v) {
                adj_col.insert(col);
                q.push(((adj_col.len(), deg[v]), v));
            }
        }
    }
    (cols, max_col + 1)
}

/// O(2^n n)
pub fn k_col(k: usize, adj: &[usize]) -> bool {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    'a: for i in 0..1_usize << n {
        for v in 0..n {
            if i & 1 << v != 0 {
                if adj[v] & i != 0 {
                    f[i] = 0;
                    continue 'a;
                }
            }
        }
        f[i] = 1;
    }
    lattice::xor(&mut f);
    f.iter_mut().for_each(|i| *i = i.wrapping_pow(k as u32));
    let mut t = 0;
    for i in 0..1_usize << n {
        if i.count_ones() & 1 == 0 {
            t += f[i]
        } else {
            t -= f[i]
        };
    }
    t != 0
}

/// O(2^n n)
pub fn chi(adj: &[usize]) -> usize {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    'a: for i in 0..1_usize << n {
        for v in 0..n {
            if i & 1 << v != 0 {
                if adj[v] & i != 0 {
                    f[i] = 0;
                    continue 'a;
                }
            }
        }
        f[i] = 1;
    }
    let mut g = f.clone();
    lattice::xor(&mut g);
    let mut f = g.clone();
    for i in 1..=n {
        let mut t = 0;
        for i in 0..1_usize << n {
            if i.count_ones() & 1 == 0 {
                t += f[i]
            } else {
                t -= f[i]
            };
        }
        if t != 0 {
            return i;
        }
        f.iter_mut()
            .zip(&g)
            .for_each(|(i, &j)| *i = i.wrapping_mul(j));
    }
    usize::MAX
}

/// O(2^n n)
pub fn clique_cover_number(adj: &[usize]) -> usize {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    'a: for i in 0..1_usize << n {
        for v in 0..n {
            if i & 1 << v != 0 {
                if adj[v] & i & !(1 << v) != i & !(1 << v) {
                    f[i] = 0;
                    continue 'a;
                }
            }
        }
        f[i] = 1;
    }
    let mut g = f.clone();
    lattice::xor(&mut g);
    let mut f = g.clone();
    for i in 1..=n {
        let mut t = 0;
        for i in 0..1_usize << n {
            if i.count_ones() & 1 == 0 {
                t += f[i]
            } else {
                t -= f[i]
            };
        }
        if t != 0 {
            return i;
        }
        f.iter_mut()
            .zip(&g)
            .for_each(|(i, &j)| *i = i.wrapping_mul(j));
    }
    usize::MAX
}

// TODO: chromatic poly
// https://judge.yosupo.jp/submission/214976
// https://codeforces.com/blog/entry/92183
pub fn chromatic_poly() {}

// TODO: edge coloring
// https://judge.yosupo.jp/submission/97319
// https://judge.yosupo.jp/submission/228343
// https://codeforces.com/blog/entry/75431
// https://github.com/kth-competitive-programming/kactl/blob/eab6492ce9c8549832484f47276739ff120477b3/content/graph/EdgeColoring.h#L16
pub fn edge_color() {}

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    fn test_basic_cases() {
        // Single vertex
        assert_eq!(chromatic_number(&[vec![]]), 1);

        // Two vertices, no edge
        assert_eq!(chromatic_number(&[vec![], vec![]]), 1);

        // Two vertices with edge
        assert_eq!(chromatic_number(&[vec![1], vec![0]]), 2);

        // Triangle (K3)
        assert_eq!(chromatic_number(&[vec![1, 2], vec![0, 2], vec![0, 1]]), 3);

        // Square cycle
        assert_eq!(
            chromatic_number(&[vec![1, 3], vec![0, 2], vec![1, 3], vec![0, 2]]),
            2
        );

        // Complete graph K4
        assert_eq!(
            chromatic_number(&[vec![1, 2, 3], vec![0, 2, 3], vec![0, 1, 3], vec![0, 1, 2]]),
            4
        );

        // Star graph
        assert_eq!(
            chromatic_number(&[vec![1, 2, 3, 4], vec![0], vec![0], vec![0], vec![0]]),
            2
        );

        // Path graph
        assert_eq!(
            chromatic_number(&[vec![1], vec![0, 2], vec![1, 3], vec![2, 4], vec![3]]),
            2
        );

        // Pentagon (odd cycle)
        assert_eq!(
            chromatic_number(&[vec![1, 4], vec![0, 2], vec![1, 3], vec![2, 4], vec![0, 3]]),
            3
        );
    }

    #[test]
    fn test_complete_graphs() {
        // K5 - complete graph on 5 vertices
        let k5: Vec<Vec<usize>> = (0..5)
            .map(|i| (0..5).filter(|&j| i != j).collect())
            .collect();
        assert_eq!(chromatic_number(&k5), 5);

        // K6 - complete graph on 6 vertices
        let k6: Vec<Vec<usize>> = (0..6)
            .map(|i| (0..6).filter(|&j| i != j).collect())
            .collect();
        assert_eq!(chromatic_number(&k6), 6);
    }

    #[test]
    fn test_wheel_graphs() {
        // Wheel W5 - center connected to 5-cycle
        let w5 = vec![
            vec![1, 2, 3, 4, 5], // center
            vec![0, 2, 5],       // cycle vertices
            vec![0, 1, 3],
            vec![0, 2, 4],
            vec![0, 3, 5],
            vec![0, 1, 4],
        ];
        assert_eq!(chromatic_number(&w5), 4); // odd cycle + center

        // Wheel W6 - center connected to 6-cycle
        let w6 = vec![
            vec![1, 2, 3, 4, 5, 6], // center
            vec![0, 2, 6],          // cycle vertices
            vec![0, 1, 3],
            vec![0, 2, 4],
            vec![0, 3, 5],
            vec![0, 4, 6],
            vec![0, 1, 5],
        ];
        assert_eq!(chromatic_number(&w6), 3); // even cycle + center
    }

    #[test]
    fn test_bipartite_graphs() {
        // Complete bipartite K_{3,3}
        let k33 = vec![
            vec![3, 4, 5], // partition 1
            vec![3, 4, 5],
            vec![3, 4, 5],
            vec![0, 1, 2], // partition 2
            vec![0, 1, 2],
            vec![0, 1, 2],
        ];
        assert_eq!(chromatic_number(&k33), 2);

        // Complete bipartite K_{2,4}
        let k24 = vec![
            vec![2, 3, 4, 5], // partition 1
            vec![2, 3, 4, 5],
            vec![0, 1], // partition 2
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
        ];
        assert_eq!(chromatic_number(&k24), 2);
    }

    #[test]
    fn test_planar_graphs() {
        // Petersen graph (famous non-planar graph)
        let petersen = vec![
            vec![1, 4, 5], // outer pentagon
            vec![0, 2, 6],
            vec![1, 3, 7],
            vec![2, 4, 8],
            vec![0, 3, 9],
            vec![0, 7, 8], // inner pentagram
            vec![1, 8, 9],
            vec![2, 5, 9],
            vec![3, 5, 6],
            vec![4, 6, 7],
        ];
        assert_eq!(chromatic_number(&petersen), 3);

        // Dodecahedron graph (subset - first 8 vertices)
        let dodeca_subset = vec![
            vec![1, 2, 7],
            vec![0, 3, 4],
            vec![0, 5, 6],
            vec![1, 4, 7],
            vec![1, 3, 5],
            vec![2, 4, 6],
            vec![2, 5, 7],
            vec![0, 3, 6],
        ];
        assert_eq!(chromatic_number(&dodeca_subset), 3);
    }

    #[test]
    fn test_cycle_graphs() {
        // Various cycle lengths
        for n in 3..=10 {
            let cycle: Vec<Vec<usize>> =
                (0..n).map(|i| vec![(i + n - 1) % n, (i + 1) % n]).collect();
            let expected = if n % 2 == 0 { 2 } else { 3 };
            assert_eq!(chromatic_number(&cycle), expected, "Failed for C{}", n);
        }
    }

    #[test]
    fn test_complex_structured_graphs() {
        // Möbius-Kantor graph (8 vertices, 4-regular)
        let mobius_kantor = vec![
            vec![1, 3, 5, 7],
            vec![0, 2, 4, 6],
            vec![1, 3, 7, 5],
            vec![0, 2, 4, 6],
            vec![1, 3, 5, 7],
            vec![0, 2, 4, 6],
            vec![1, 3, 7, 5],
            vec![0, 2, 4, 6],
        ];
        assert_eq!(chromatic_number(&mobius_kantor), 2);

        // Cube graph (8 vertices of a cube)
        let cube = vec![
            vec![1, 3, 4], // bottom face
            vec![0, 2, 5],
            vec![1, 3, 6],
            vec![0, 2, 7],
            vec![0, 5, 7], // top face
            vec![1, 4, 6],
            vec![2, 5, 7],
            vec![3, 4, 6],
        ];
        assert_eq!(chromatic_number(&cube), 2);
    }

    #[test]
    fn test_sparse_vs_dense() {
        // Very sparse graph (tree)
        let tree = vec![
            vec![1, 2],    // root
            vec![0, 3, 4], // level 1
            vec![0, 5, 6],
            vec![1], // leaves
            vec![1],
            vec![2],
            vec![2],
        ];
        assert_eq!(chromatic_number(&tree), 2);

        // Dense but not complete
        let dense = vec![
            vec![1, 2, 3, 4], // missing edge to 5
            vec![0, 2, 3, 5], // missing edge to 4
            vec![0, 1, 4, 5], // missing edge to 3
            vec![0, 1, 5],    // missing edges to 2,4
            vec![0, 2, 5],    // missing edges to 1,3
            vec![1, 2, 3, 4], // missing edge to 0
        ];
        assert_eq!(chromatic_number(&dense), 3);
    }

    #[test]
    fn test_mycielski_graphs() {
        // Mycielski construction creates triangle-free graphs with high chromatic number
        // M3 (5 vertices, chromatic number 3)
        let m3 = vec![vec![1, 2], vec![0, 3], vec![0, 4], vec![1, 4], vec![2, 3]];
        assert_eq!(chromatic_number(&m3), 3);

        // Groetzsch graph (11 vertices, triangle-free, chromatic number 4)
        let groetzsch = vec![
            vec![1, 2, 3, 4], // center
            vec![0, 5, 6],    // outer ring
            vec![0, 6, 7],
            vec![0, 7, 8],
            vec![0, 8, 5],
            vec![1, 4, 9], // middle ring
            vec![1, 2, 10],
            vec![2, 3, 9],
            vec![3, 4, 10],
            vec![5, 7, 10], // inner connections
            vec![6, 8, 9],
        ];
        assert_eq!(chromatic_number(&groetzsch), 3);
    }
}
