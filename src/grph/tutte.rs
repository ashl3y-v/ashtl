use crate::alg::{mat::Mat, ops::inverse_euclidean};
use crate::ds::bit_vec::BitVec;
use rand::Rng;

type E = i64;

pub fn tutte_matrix<const M: u64>(n: usize, es: &[[usize; 2]], rng: &mut impl Rng) -> Mat<M> {
    let mut mat = Mat::<M>::from_elem(n, n, 0);
    for &[a, b] in es {
        if a != b {
            let r = rng.random_range(1..M) as E;
            (mat[(a, b)], mat[(b, a)]) = (r, -r);
        }
    }

    mat
}

pub fn has_perfect_matching<const M: u64>(n: usize, es: &[[usize; 2]], rng: &mut impl Rng) -> bool {
    tutte_matrix::<M>(n, es, rng).det(|_| {}, |_| {}) != 0
}

pub fn max_matching_size<const M: u64>(n: usize, es: &[[usize; 2]], rng: &mut impl Rng) -> usize {
    tutte_matrix::<M>(n, es, rng).rank(|_| {}, |_| {}) / 2
}

pub fn max_matching<const M: u64>(n: usize, es: &[[usize; 2]]) -> Vec<[usize; 2]> {
    let mut rng = rand::rng();
    let mut mat: Mat<M> = tutte_matrix(n, es, &mut rng);
    let (_, r, mut a_inv) = mat.inv(|_| {}, |_| {});
    let mut current_n = n;
    let target_m = (n << 1) - r;
    if target_m != n {
        loop {
            mat.resize_rows(target_m);
            mat.resize_cols(target_m);
            for i in 0..current_n {
                for j in current_n..target_m {
                    let r = rng.random_range(1..M) as E;
                    (mat[(i, j)], mat[(j, i)]) = (r, -r);
                }
            }
            let (_, new_r, new_inv) = mat.inv(|_| {}, |_| {});
            if new_r == target_m {
                a_inv = new_inv;
                current_n = target_m;
                break;
            }
        }
    }
    let m = current_n;
    let mut has = BitVec::new(m, true);
    let mut ret = Vec::new();
    for _ in 0..m >> 1 {
        let mut fi = usize::MAX;
        let mut fj = usize::MAX;
        'a: for i in 0..m {
            if !has[i] {
                continue;
            }
            for j in (i + 1)..m {
                if has[j] && a_inv[(i, j)] != 0 && mat[(i, j)] != 0 {
                    fi = i;
                    fj = j;
                    break 'a;
                }
            }
        }
        if fi == usize::MAX || fj == usize::MAX {
            break;
        }
        if fj < n {
            ret.push([fi, fj]);
        }
        has.set(fi, false);
        has.set(fj, false);
        let pivot_val_ij = a_inv[(fi, fj)];
        let pivot_inv_ij = inverse_euclidean::<M, _>(pivot_val_ij as i64) as E;
        let pivot_inv_ji = -pivot_inv_ij;
        for i in 0..m {
            if !has[i] {
                continue;
            }
            if a_inv[(i, fj)] != 0 {
                let multiplier = (a_inv[(i, fj)] * pivot_inv_ij) % M as E;
                for j in 0..m {
                    a_inv[(i, j)] =
                        (a_inv[(i, j)] - (a_inv[(fi, j)] * multiplier) % M as E) % M as E;
                }
            }
            if a_inv[(i, fi)] != 0 {
                let multiplier = (a_inv[(i, fi)] % M as E * pivot_inv_ji) % M as E;
                for j in 0..m {
                    a_inv[(i, j)] =
                        (a_inv[(i, j)] - (a_inv[(fj, j)] * multiplier) % M as E) % M as E;
                }
            }
        }
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::collections::HashSet;

    // Pick a reasonably large prime so that chance of zero weight is negligible.
    const M: u64 = 1000000007;

    /// Brute-force maximum matching by enumerating all subsets of edges.
    fn brute_max_matching(n: usize, edges: &Vec<[usize; 2]>) -> usize {
        let m = edges.len();
        let mut best = 0;
        for mask in 0..(1 << m) {
            let mut used = vec![false; n];
            let mut ok = true;
            let mut cnt = 0;
            for i in 0..m {
                if (mask & (1 << i)) != 0 {
                    let [u, v] = edges[i];
                    if used[u] || used[v] {
                        ok = false;
                        break;
                    }
                    used[u] = true;
                    used[v] = true;
                    cnt += 1;
                }
            }
            if ok && cnt > best {
                best = cnt;
            }
        }
        best
    }

    /// Try up to 5 times (to avoid random zero-weight flakiness) and panic if never matching.
    fn assert_matching(n: usize, edges: &[[usize; 2]], expected: usize) {
        let mut rng = rand::rng();
        for _ in 0..5 {
            let got = max_matching_size::<M>(n, &edges, &mut rng) as usize;
            if got == expected {
                return;
            }
        }
        panic!(
            "maximum_matching_size({},{:?}) expected {}, but got {}",
            n,
            edges,
            expected,
            max_matching_size::<M>(n, edges, &mut rng)
        );
    }

    #[test]
    fn test_empty_graph() {
        assert_matching(0, &vec![], 0);
        assert_matching(1, &vec![], 0);
        assert_matching(5, &vec![], 0);
    }

    #[test]
    fn test_triangle() {
        // 3-cycle has max matching 1
        assert_matching(3, &vec![[0, 1], [1, 2], [2, 0]], 1);
    }

    #[test]
    fn test_path_and_cycles() {
        // Path on 4 vertices: matching size 2
        assert_matching(4, &vec![[0, 1], [1, 2], [2, 3]], 2);
        // Even cycle C4: matching size 2
        assert_matching(4, &vec![[0, 1], [1, 2], [2, 3], [3, 0]], 2);
        // Odd cycle C5: matching size 2
        assert_matching(5, &vec![[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]], 2);
    }

    #[test]
    fn test_complete_graphs() {
        // K4: floor(4/2)=2
        let mut edges4 = Vec::new();
        for u in 0..4 {
            for v in (u + 1)..4 {
                edges4.push([u, v]);
            }
        }
        assert_matching(4, &edges4, 2);

        // K5: floor(5/2)=2
        let mut edges5 = Vec::new();
        for u in 0..5 {
            for v in (u + 1)..5 {
                edges5.push([u, v]);
            }
        }
        assert_matching(5, &edges5, 2);
    }

    #[test]
    fn test_star_and_union() {
        // Star K1,4: matching size 1
        assert_matching(5, &vec![[0, 1], [0, 2], [0, 3], [0, 4]], 1);

        // Union of two triangles: total matching = 1 + 1 = 2
        let edges = vec![
            [0, 1],
            [1, 2],
            [2, 0], // first triangle
            [3, 4],
            [4, 5],
            [5, 3], // second triangle
        ];
        assert_matching(6, &edges, 2);
    }

    #[test]
    fn test_random_small_graphs() {
        let mut rng = StdRng::seed_from_u64(42);
        for n in 2..=6 {
            // choose a random number of edges up to n*(n−1)/2
            let max_e = n * (n - 1) / 2;
            let e_cnt = rng.random_range(0..=max_e);
            let mut edges = Vec::new();
            let mut seen = HashSet::new();
            while edges.len() < e_cnt {
                let u = rng.random_range(0..n);
                let v = rng.random_range(0..n);
                if u == v {
                    continue;
                }
                let (a, b) = if u < v { (u, v) } else { (v, u) };
                if seen.insert((a, b)) {
                    edges.push([a, b]);
                }
            }
            let expected = brute_max_matching(n, &edges);
            // try a few times, then assert
            for _ in 0..5 {
                if max_matching_size::<M>(n, &edges, &mut rng) as usize == expected {
                    break;
                }
            }
            assert_eq!(
                max_matching_size::<M>(n, &edges, &mut rng) as usize,
                expected,
                "random graph on {} vertices, edges = {:?}",
                n,
                edges
            );
        }
    }

    fn is_valid_matching(n: usize, edges: &[[usize; 2]], matching: &[[usize; 2]]) -> bool {
        // Check that all vertices in matching are valid
        let mut used_vertices = HashSet::new();
        for &[u, v] in matching {
            if u >= n || v >= n {
                return false;
            }
            if used_vertices.contains(&u) || used_vertices.contains(&v) {
                return false; // Vertex used twice
            }
            used_vertices.insert(u);
            used_vertices.insert(v);
        }

        // Check that all edges in matching exist in the graph
        let edge_set: HashSet<[usize; 2]> = edges
            .iter()
            .map(|&[u, v]| if u < v { [u, v] } else { [v, u] })
            .collect();

        for &[u, v] in matching {
            let edge = if u < v { [u, v] } else { [v, u] };
            if !edge_set.contains(&edge) {
                return false;
            }
        }

        true
    }

    #[test]
    fn test_empty_graph_recover() {
        let edges = [];
        let matching = max_matching::<M>(4, &edges);
        assert!(matching.is_empty());
        assert!(is_valid_matching(4, &edges, &matching));
    }

    #[test]
    fn test_single_edge() {
        let edges = [[0, 1]];
        let matching = max_matching::<M>(2, &edges);
        assert_eq!(matching.len(), 1);
        assert!(is_valid_matching(2, &edges, &matching));
        assert!(matching.contains(&[0, 1]) || matching.contains(&[1, 0]));
    }

    #[test]
    fn test_path_graph() {
        // Path: 0-1-2-3
        let edges = [[0, 1], [1, 2], [2, 3]];
        let matching = max_matching::<M>(4, &edges);

        assert!(is_valid_matching(4, &edges, &matching));
        // Maximum matching in a path of 4 vertices should have size 2
        assert_eq!(matching.len(), 2);

        // Check that it's actually a maximum matching
        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 4); // All vertices should be matched
    }

    #[test]
    fn test_triangle_recover() {
        // Triangle: 0-1-2-0
        let edges = [[0, 1], [1, 2], [2, 0]];
        let matching = max_matching::<M>(3, &edges);

        assert!(is_valid_matching(3, &edges, &matching));
        // Maximum matching in a triangle should have size 1
        assert_eq!(matching.len(), 1);
    }

    #[test]
    fn test_complete_graph_k4() {
        // Complete graph K4
        let edges = [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]];
        let matching = max_matching::<M>(4, &edges);

        assert!(is_valid_matching(4, &edges, &matching));
        // Maximum matching in K4 should have size 2 (perfect matching)
        assert_eq!(matching.len(), 2);

        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 4); // All vertices matched
    }

    #[test]
    fn test_petersen_graph() {
        // Petersen graph (outer cycle and inner star)
        let edges = [
            // Outer cycle: 0-1-2-3-4-0
            [0, 1],
            [1, 2],
            [2, 3],
            [3, 4],
            [4, 0],
            // Inner vertices: 5,6,7,8,9
            [0, 5],
            [1, 6],
            [2, 7],
            [3, 8],
            [4, 9],
            // Inner connections (forming a pentagram)
            [5, 7],
            [7, 9],
            [9, 6],
            [6, 8],
            [8, 5],
        ];
        let matching = max_matching::<M>(10, &edges);

        assert!(is_valid_matching(10, &edges, &matching));
        // Petersen graph has a perfect matching
        assert_eq!(matching.len(), 5);

        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 10); // All vertices matched
    }

    #[test]
    fn test_bipartite_graph() {
        // Complete bipartite graph K_{2,3}
        // Left side: 0, 1
        // Right side: 2, 3, 4
        let edges = [[0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4]];
        let matching = max_matching::<M>(5, &edges);

        assert!(is_valid_matching(5, &edges, &matching));
        // Maximum matching should have size 2 (limited by smaller side)
        assert_eq!(matching.len(), 2);
    }

    #[test]
    fn test_disconnected_graph() {
        // Two disconnected triangles: 0-1-2-0 and 3-4-5-3
        let edges = [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3]];
        let matching = max_matching::<M>(6, &edges);

        assert!(is_valid_matching(6, &edges, &matching));
        // Should find one edge from each triangle
        assert_eq!(matching.len(), 2);
    }

    #[test]
    fn test_star_graph() {
        // Star graph: center vertex 0 connected to 1,2,3,4
        let edges = [[0, 1], [0, 2], [0, 3], [0, 4]];
        let matching = max_matching::<M>(5, &edges);

        assert!(is_valid_matching(5, &edges, &matching));
        // Maximum matching in star should have size 1
        assert_eq!(matching.len(), 1);

        // The matched edge should include vertex 0
        assert!(matching[0].contains(&0));
    }

    #[test]
    fn test_cycle_even() {
        // Even cycle: 0-1-2-3-0
        let edges = [[0, 1], [1, 2], [2, 3], [3, 0]];
        let matching = max_matching::<M>(4, &edges);

        assert!(is_valid_matching(4, &edges, &matching));
        // Even cycle should have perfect matching
        assert_eq!(matching.len(), 2);

        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 4);
    }

    #[test]
    fn test_cycle_odd() {
        // Odd cycle: 0-1-2-3-4-0
        let edges = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]];
        let matching = max_matching::<M>(5, &edges);

        assert!(is_valid_matching(5, &edges, &matching));
        // Odd cycle should have matching of size (n-1)/2 = 2
        assert_eq!(matching.len(), 2);

        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 4); // One vertex unmatched
    }

    #[test]
    fn test_matching_size_consistency() {
        // Test that max_matching_size agrees with max_matching length
        let edges = [[0, 1], [1, 2], [2, 3], [0, 3], [1, 3]];

        let mut rng = rand::rng();
        let matching = max_matching::<M>(4, &edges);
        let size = max_matching_size::<M>(4, &edges, &mut rng);

        assert_eq!(matching.len(), size);
        assert!(is_valid_matching(4, &edges, &matching));
    }

    #[test]
    fn test_large_complete_graph() {
        // K6 - complete graph on 6 vertices
        let mut edges = Vec::new();
        for i in 0..6 {
            for j in (i + 1)..6 {
                edges.push([i, j]);
            }
        }

        let matching = max_matching::<M>(6, &edges);

        assert!(is_valid_matching(6, &edges, &matching));
        // K6 should have perfect matching of size 3
        assert_eq!(matching.len(), 3);

        let matched_vertices: HashSet<usize> = matching.iter().flat_map(|&[u, v]| [u, v]).collect();
        assert_eq!(matched_vertices.len(), 6);
    }

    #[test]
    fn test_randomized_consistency() {
        // Run the same graph multiple times to test randomized algorithm consistency
        let edges = [[0, 1], [1, 2], [2, 3], [0, 3], [1, 3]];

        let mut sizes = HashSet::new();
        for _ in 0..10 {
            let matching = max_matching::<M>(4, &edges);
            assert!(is_valid_matching(4, &edges, &matching));
            sizes.insert(matching.len());
        }

        // All runs should produce matchings of the same (maximum) size
        assert_eq!(
            sizes.len(),
            1,
            "Matching sizes should be consistent: {:?}",
            sizes
        );
    }
}
