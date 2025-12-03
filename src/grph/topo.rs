pub fn topo_sort(adj: &[Vec<usize>]) -> Vec<usize> {
    let n = adj.len();
    let mut q = Vec::with_capacity(n);
    let mut indeg = vec![0; n];
    adj.iter().flatten().for_each(|&x| indeg[x] += 1);
    (0..n).filter(|&i| indeg[i] == 0).for_each(|i| q.push(i));
    let mut j = 0;
    while j < q.len() {
        for &x in &adj[q[j]] {
            indeg[x] -= 1;
            if indeg[x] == 0 {
                q.push(x);
            }
        }
        j += 1;
    }
    q
}

// TODO: topological order with minimum inversions
// https://maspypy.github.io/library/graph/optimal_product_on_tree.hpp

#[cfg(test)]
mod tests {
    use super::topo_sort;

    #[test]
    fn empty_graph() {
        let adj: Vec<Vec<usize>> = vec![];
        let order = topo_sort(&adj);
        assert!(order.is_empty());
    }

    #[test]
    fn single_node() {
        let adj = vec![vec![]];
        let order = topo_sort(&adj);
        assert_eq!(order, vec![0]);
    }

    #[test]
    fn linear_chain() {
        // 0 → 1 → 2 → 3
        let adj = vec![vec![1], vec![2], vec![3], vec![]];
        let order = topo_sort(&adj);
        assert_eq!(order, vec![0, 1, 2, 3]);
    }

    #[test]
    fn diamond_shape() {
        //   0
        //  / \
        // v   v
        // 1   2
        //  \ /
        //   3
        let adj = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let order = topo_sort(&adj);
        // 0 must come before 1,2; 1 and 2 before 3
        let pos = |x| order.iter().position(|&y| y == x).unwrap();
        assert!(pos(0) < pos(1));
        assert!(pos(0) < pos(2));
        assert!(pos(1) < pos(3));
        assert!(pos(2) < pos(3));
        assert_eq!(order.len(), 4);
    }

    #[test]
    fn disconnected_components() {
        // Two chains 0→1 and 2→3, order within each preserved but interleaving allowed
        let adj = vec![
            vec![1], // 0
            vec![],  // 1
            vec![3], // 2
            vec![],  // 3
        ];
        let order = topo_sort(&adj);
        let pos = |x| order.iter().position(|&y| y == x).unwrap();
        assert!(pos(0) < pos(1));
        assert!(pos(2) < pos(3));
        assert_eq!(order.len(), 4);
    }

    #[test]
    fn cycle_detected_as_partial() {
        // 0→1→2→0 forms a cycle; our function doesn’t explicitly detect it,
        // but will return fewer than n nodes.
        let adj = vec![
            vec![1], // 0
            vec![2], // 1
            vec![0], // 2
        ];
        let order = topo_sort(&adj);
        assert!(order.len() < 3, "cycle should prevent sorting all nodes");
    }
}
