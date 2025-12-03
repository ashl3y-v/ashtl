use crate::alg::mat::Mat;
use crate::alg::poly::E;

pub fn count_eulerian_dense<const M: u64>(adj: &[Vec<usize>]) -> usize {
    let n = adj.len();
    let mut f = vec![1];
    let mut fact = |i| {
        while i >= f.len() {
            f.push(f.last().unwrap() * f.len() as E % M as E);
        }
        f[i]
    };
    let mut a = Mat::<M>::from_elem(n - 1, n - 1, 0);
    let (mut indeg, mut outdeg) = (vec![0; n], vec![0; n]);
    for u in 0..n {
        for &v in &adj[u] {
            if v < n - 1 {
                a[v][v] += 1;
                if u < n - 1 {
                    a[u][v] -= 1;
                }
            }
            outdeg[u] += 1;
            indeg[v] += 1;
        }
    }
    let mut s = 1;
    for i in 0..n {
        if indeg[i] != outdeg[i] {
            return 0;
        }
        if i != n - 1 && indeg[i] == 0 {
            a[i][i] = 1;
            continue;
        }
        if indeg[i] >= 3 {
            s = s * fact(indeg[i] - 1) % M as E;
        }
    }
    (a.det(|_| {}, |_| {}) * s).rem_euclid(M as E) as usize
}

pub fn count_eulerian_sparse<const M: u64>(adj: &[Vec<usize>]) -> usize {
    let n = adj.len();
    let mut f = vec![1];
    let mut fact = |i| {
        while i >= f.len() {
            f.push(f.last().unwrap() * f.len() as E % M as E);
        }
        f[i]
    };
    let (mut indeg, mut outdeg) = (vec![0; n], vec![0; n]);
    let mut a = Vec::new();
    for u in 0..n {
        for &v in &adj[u] {
            if u < n - 1 && v < n - 1 {
                a.push((u, v, -1));
            }
            outdeg[u] += 1;
            indeg[v] += 1;
        }
    }
    let mut s = 1;
    for i in 0..n {
        if indeg[i] != outdeg[i] {
            return 0;
        }
        if indeg[i] >= 3 {
            s = s * fact(indeg[i] - 1) % M as E;
        }
        if i == n - 1 {
            break;
        }
        if indeg[i] != 0 {
            a.push((i, i, indeg[i] as E));
        } else {
            a.push((i, i, 1));
        }
    }
    (Mat::<M>::det_bb(n - 1, |v| {
        let mut w = vec![0; n - 1];
        for &(i, j, x) in &a {
            w[j] = (w[j] + v[i] * x) % M as E;
        }
        w
    }) * s)
        .rem_euclid(M as E) as usize
}
