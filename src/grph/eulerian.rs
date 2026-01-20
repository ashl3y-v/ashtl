use crate::alg::fps::E;
use crate::alg::mat::Mat;
use crate::ds::bit_vec::BitVec;

pub fn eulerian_path(v: usize, m: usize, adj: &[Vec<usize>]) -> Vec<usize> {
    let n = adj.len();
    let mut stk = Vec::with_capacity(m + 1);
    let mut done = BitVec::new(n, false);
    let mut path = vec![0; m + 1];
    let mut idx = m + 1;
    stk.push(v);
    while let Some(&u) = stk.last() {
        if done[u] {
            idx -= 1;
            path[idx] = u;
            stk.pop();
        } else {
            for &w in &adj[u] {
                stk.push(w);
            }
            done.set(u, true);
        }
    }
    path
}

pub fn tree_euler_tour(n: usize, dfs: &[usize], pos: &[usize], ss: &[usize]) -> Vec<usize> {
    let mut et = Vec::with_capacity(n * 2);
    let mut stack = Vec::with_capacity(n);
    for &v in dfs {
        while let Some(&u) = stack.last() {
            if pos[v] >= pos[u] + ss[u] {
                et.push(u);
                stack.pop();
            } else {
                break;
            }
        }
        et.push(v);
        stack.push(v);
    }
    while let Some(u) = stack.pop() {
        et.push(u);
    }
    et
}

/// O(n^3)
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

/// O(n (n + m))
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
