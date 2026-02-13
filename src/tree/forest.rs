use crate::alg::fps::E;
use crate::alg::mat::Mat;
use crate::grph::flow::PushRelabel;

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

/// O(n (n + m)^5/2)
pub fn k_disjoint_forest_partition(k: i64, n: usize, es: &[(usize, usize, i64)]) -> bool {
    let sm = es.iter().map(|&(_, _, c)| c).sum();
    if sm > k * (n as i64 - 1) {
        return false;
    }
    let m = es.len();
    let left = |v: usize| 1 + v;
    let right = |i: usize| 1 + n + i;
    let s = 0;
    let t = right(m);
    for r in 0..n {
        let mut g = PushRelabel::new(t + 1);
        for v in 0..n {
            if v != r {
                g.add_edge(s, left(v), k, 0);
            }
        }
        for (i, &(a, b, c)) in es.iter().enumerate() {
            g.add_edge(left(a), right(i), sm, 0);
            g.add_edge(left(b), right(i), sm, 0);
            g.add_edge(right(i), t, c, 0);
        }
        let flow = g.calc(s, t);
        if flow < sm {
            return false;
        }
    }
    true
}
