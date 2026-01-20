use crate::alg::fps::E;
use crate::alg::mat::Mat;

/// O(n^3)
pub fn count_spanning_tree_dense<const M: u64>(adj: &[Vec<usize>], r: usize) -> usize {
    let n = adj.len();
    let mut a = Mat::<M>::from_elem(n, n, 0);
    for u in 0..n {
        for &v in &adj[u] {
            a[u][v] -= 1;
            a[v][v] += 1;
        }
    }
    for i in 0..n {
        (a[i][r], a[r][i]) = (0, 0);
    }
    a[r][r] = 1;
    a.det(|_| {}, |_| {}).rem_euclid(M as E) as usize
}

/// O(n (n + m))
pub fn count_spanning_tree_sparse<const M: u64>(adj: &[Vec<usize>], r: usize) -> usize {
    let n = adj.len();
    let mut indeg = vec![0; n];
    let mut a = Vec::new();
    for u in 0..n {
        for &v in &adj[u] {
            if u != r && v != r {
                a.push((u, v, -1));
            }
            indeg[v] += 1;
        }
    }
    for i in 0..n {
        if i != r {
            a.push((i, i, indeg[i] as E));
        } else {
            a.push((i, i, 1));
        }
    }
    Mat::<M>::det_bb(n, |v| {
        let mut w = vec![0; n];
        for &(i, j, x) in &a {
            w[j] = (w[j] + v[i] * x) % M as E;
        }
        w
    })
    .rem_euclid(M as E) as usize
}
