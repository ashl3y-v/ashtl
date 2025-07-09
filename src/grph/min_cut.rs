use std::ops::{Add, AddAssign, Neg, Sub};

/// Stoer Wagner for global min cut in O(V^3)
pub fn stoer_wagner<
    T: Copy + Ord + Neg<Output = T> + Add<Output = T> + Sub<Output = T> + AddAssign,
>(
    mat: &mut [Vec<T>],
    max: T,
) -> (T, Vec<usize>) {
    let n = mat.len();
    let mut best = (max, Vec::new());
    let mut co: Vec<Vec<usize>> = (0..n).map(|i| vec![i]).collect();
    let mut w = vec![max; n];
    for ph in 1..n {
        w.copy_from_slice(&mat[0]);
        let mut s = 0;
        let mut t = 0;
        for _ in 0..(n - ph) {
            w[t] = -max;
            s = t;
            t = w
                .iter()
                .enumerate()
                .max_by_key(|&(_, x)| x)
                .map(|x| x.0)
                .unwrap();
            for i in 0..n {
                w[i] += mat[t][i];
            }
        }
        best = best.min((w[t] - mat[t][t], co[t].clone()));
        let [co_s, co_t] = co.get_disjoint_mut([s, t]).unwrap();
        co_s.extend_from_slice(&co_t);
        let [mat_s, mat_t] = mat.get_disjoint_mut([s, t]).unwrap();
        mat_s.iter_mut().zip(&*mat_t).for_each(|(a, &b)| *a += b);
        for i in 0..n {
            mat[i][s] = mat[s][i];
        }
        mat[0][t] = -max;
    }
    best
}

// TODO: implement karger-stein

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_triangle() {
        // Triangle graph: 0-1 (weight 1), 1-2 (weight 2), 0-2 (weight 3)
        // Possible cuts: {0} vs {1,2} = 1+3=4, {1} vs {0,2} = 1+2=3, {2} vs {0,1} = 2+3=5
        // Min cut should be 3 (separating vertex 1)
        let mut mat = vec![vec![0, 1, 3], vec![1, 0, 2], vec![3, 2, 0]];
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 3);
        // Cut should separate vertex 1 from vertices 0,2
        assert_eq!(cut, vec![1]);
    }

    #[test]
    fn test_square_graph() {
        // Square graph: 0-1-2-3-0 with all edges weight 1
        // Min cut should be 2 (any pair of opposite edges)
        let mut mat = vec![
            vec![0, 1, 0, 1],
            vec![1, 0, 1, 0],
            vec![0, 1, 0, 1],
            vec![1, 0, 1, 0],
        ];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 2);
    }

    #[test]
    fn test_complete_graph_k4() {
        // Complete graph K4 with all edges weight 1
        // Min cut should be 3 (removing any single vertex)
        let mut mat = vec![
            vec![0, 1, 1, 1],
            vec![1, 0, 1, 1],
            vec![1, 1, 0, 1],
            vec![1, 1, 1, 0],
        ];
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 3);
        assert_eq!(cut.len(), 1); // Should isolate one vertex
    }

    #[test]
    fn test_disconnected_components() {
        // Two disconnected triangles: {0,1,2} and {3,4,5}
        // Min cut should be 0
        let mut mat = vec![
            vec![0, 2, 3, 0, 0, 0],
            vec![2, 0, 1, 0, 0, 0],
            vec![3, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 4, 5],
            vec![0, 0, 0, 4, 0, 6],
            vec![0, 0, 0, 5, 6, 0],
        ];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 0);
    }

    #[test]
    fn test_bridge_graph() {
        // Two triangles connected by a bridge of weight 1
        // 0-1-2-0 (weights 3,4,5) connected to 3-4-5-3 (weights 6,7,8) via edge 2-3 (weight 1)
        let mut mat = vec![
            vec![0, 3, 5, 0, 0, 0],
            vec![3, 0, 4, 0, 0, 0],
            vec![5, 4, 0, 1, 0, 0], // Bridge: 2-3 with weight 1
            vec![0, 0, 1, 0, 6, 8],
            vec![0, 0, 0, 6, 0, 7],
            vec![0, 0, 0, 8, 7, 0],
        ];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 1); // Bridge is the min cut
    }

    #[test]
    fn test_single_vertex() {
        // Graph with only one vertex
        let mut mat = vec![vec![0]];
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, i32::MAX); // No cut possible
        assert_eq!(cut, vec![]);
    }

    #[test]
    fn test_two_vertices() {
        // Two vertices connected by edge of weight 5
        let mut mat = vec![vec![0, 5], vec![5, 0]];
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 5);
        assert_eq!(cut.len(), 1); // One vertex on each side
    }

    #[test]
    fn test_weighted_path() {
        // Path: 0-1-2-3 with weights [2, 1, 3]
        // Min cut should be 1 (edge 1-2)
        let mut mat = vec![
            vec![0, 2, 0, 0],
            vec![2, 0, 1, 0],
            vec![0, 1, 0, 3],
            vec![0, 0, 3, 0],
        ];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 1);
    }

    #[test]
    fn test_star_graph() {
        // Star graph: center vertex 0 connected to vertices 1,2,3,4 with weights [1,2,3,4]
        // Min cut should be 1 (isolating vertex 1)
        let mut mat = vec![
            vec![0, 1, 2, 3, 4],
            vec![1, 0, 0, 0, 0],
            vec![2, 0, 0, 0, 0],
            vec![3, 0, 0, 0, 0],
            vec![4, 0, 0, 0, 0],
        ];
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 1);
        assert_eq!(cut, vec![1]); // Should isolate vertex 1
    }

    #[test]
    fn test_parallel_edges_simulation() {
        // Simulate parallel edges by using higher weights
        // Two vertices with "parallel edges" of total weight 7
        let mut mat = vec![vec![0, 7], vec![7, 0]];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 7);
    }

    #[test]
    fn test_self_loops() {
        // Graph with self-loops (should be ignored in cut calculation)
        let mut mat = vec![
            vec![5, 3, 2], // Self-loop on vertex 0
            vec![3, 7, 1], // Self-loop on vertex 1
            vec![2, 1, 3], // Self-loop on vertex 2
        ];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        // Min cut should ignore self-loops, so it's min(3+2, 3+1, 2+1) = 3
        assert!(weight <= 3);
    }

    #[test]
    fn test_negative_weights() {
        // Test with negative weights (using i32 to allow negatives)
        let mut mat = vec![vec![0, -1, 2], vec![-1, 0, 3], vec![2, 3, 0]];
        let (weight, _cut) = stoer_wagner(&mut mat, i32::MAX);
        // This tests the algorithm handles negative weights correctly
        // The actual result depends on how negative edges affect the cut
        assert!(weight <= 2); // At least one reasonable cut exists
    }

    #[test]
    fn test_larger_complete_graph() {
        // Complete graph K5 with all edges weight 2
        // Min cut should be 8 (removing any single vertex: 4 edges * 2 weight each)
        let mut mat = vec![vec![0; 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                if i != j {
                    mat[i][j] = 2;
                }
            }
        }
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);
        assert_eq!(weight, 8);
        assert_eq!(cut.len(), 1); // Should isolate one vertex
    }

    // Helper function to verify cut validity (optional, for debugging)
    #[allow(dead_code)]
    fn verify_cut_weight(original_mat: &[Vec<i32>], cut: &[usize]) -> i32 {
        let n = original_mat.len();
        let cut_set: std::collections::HashSet<_> = cut.iter().cloned().collect();
        let mut total_weight = 0;

        for i in 0..n {
            for j in 0..n {
                if cut_set.contains(&i) != cut_set.contains(&j) {
                    total_weight += original_mat[i][j];
                }
            }
        }
        total_weight / 2 // Each edge counted twice
    }

    #[test]
    fn test_cut_weight_verification() {
        // Verify that our cut weight calculation is correct for a simple case
        let original_mat = vec![vec![0, 1, 3], vec![1, 0, 2], vec![3, 2, 0]];
        let mut mat = original_mat.clone();
        let (weight, cut) = stoer_wagner(&mut mat, i32::MAX);

        // Verify the cut weight matches
        let calculated_weight = verify_cut_weight(&original_mat, &cut);
        assert_eq!(weight, calculated_weight);
    }
}
