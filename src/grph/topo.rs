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
