use crate::alg::{
    fps::{E, Poly},
    ops::{self, inv},
};

/// O(a + b) = O(n)
pub fn conjugate(l: &[usize]) -> Vec<usize> {
    let k = l.len();
    let mut l_t = Vec::with_capacity(l[0]);
    if l.is_empty() {
        return vec![];
    }
    for _ in 0..l[k - 1] {
        l_t.push(k);
    }
    for i in (0..k - 1).rev() {
        for _ in 0..l[i] - l[i + 1] {
            l_t.push(i + 1);
        }
    }
    l_t
}

/// O(p(n) n)
pub fn partitions(n: usize, mut f: impl FnMut(&[u64])) {
    fn helper(n: usize, max: usize, prefix: &mut Vec<u64>, f: &mut impl FnMut(&[u64])) {
        if n == 0 {
            f(&prefix);
        } else {
            for i in (1..=n.min(max)).rev() {
                prefix.push(i as u64);
                helper(n - i, i, prefix, f);
                prefix.pop();
            }
        }
    }
    let mut prefix = Vec::new();
    helper(n, n, &mut prefix, &mut f);
}

/// O(p(n) n)
pub fn types(n: usize, mut f: impl FnMut(&[u64])) {
    fn helper(n: usize, max: usize, prefix: &mut [u64], f: &mut impl FnMut(&[u64])) {
        if n == 0 {
            f(prefix);
        } else {
            for i in (1..=n.min(max)).rev() {
                prefix[i - 1] += 1;
                helper(n - i, i, prefix, f);
                prefix[i - 1] -= 1;
            }
        }
    }
    let mut prefix = vec![0u64; n];
    helper(n, n, &mut prefix, &mut f);
}

/// O(n k log n)
pub fn robinson_schensted_partial(pi: &[usize], k: usize) -> Vec<Vec<usize>> {
    let mut p = vec![vec![]; k];
    for ind in 0..pi.len() {
        let mut cur = pi[ind];
        for i in 0..k {
            let j = p[i].partition_point(|&j| j <= cur);
            if j < p[i].len() {
                std::mem::swap(&mut p[i][j], &mut cur);
            } else {
                p[i].push(cur);
                break;
            }
        }
    }
    while p[p.len() - 1].is_empty() {
        p.pop();
    }
    p
}

/// O(n^3/2 log n)
pub fn robinson_schensted(mut pi: Vec<usize>) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let (n, mut k) = (pi.len(), pi.len().isqrt());
    if k * k != n {
        k += 1;
    }
    let mut inv_pi = vec![0; pi.len()];
    for i in 0..pi.len() {
        inv_pi[pi[i]] = i;
    }
    let (mut p, mut q) = (
        robinson_schensted_partial(&pi, k),
        robinson_schensted_partial(&inv_pi, k),
    );
    pi.reverse();
    inv_pi.reverse();
    let (p_cols, q_cols) = (
        robinson_schensted_partial(&pi, k),
        robinson_schensted_partial(&inv_pi, k),
    );
    p.resize(p_cols[0].len(), vec![]);
    q.resize(q_cols[0].len(), vec![]);
    for i in k..p.len() {
        let mut j = 0;
        while j < p_cols.len() && p_cols[j].len() > i {
            p[i].push(p_cols[j][i]);
            q[i].push(q_cols[j][i]);
            j += 1;
        }
    }
    (p, q)
}

/// O(n^3/2 log n)
pub fn robinson_schensted_p(mut pi: Vec<usize>) -> Vec<Vec<usize>> {
    let (n, mut k) = (pi.len(), pi.len().isqrt());
    if k * k != n {
        k += 1;
    }
    let mut inv_pi = vec![0; pi.len()];
    for i in 0..pi.len() {
        inv_pi[pi[i]] = i;
    }
    let mut p = robinson_schensted_partial(&pi, k);
    pi.reverse();
    let p_cols = robinson_schensted_partial(&pi, k);
    p.resize(p_cols[0].len(), vec![]);
    for i in k..p.len() {
        let mut j = 0;
        while j < p_cols.len() && p_cols[j].len() > i {
            p[i].push(p_cols[j][i]);
            j += 1;
        }
    }
    p
}

/// O(n^2 log n)
pub fn robinson_schensted_inv(mut p: Vec<Vec<usize>>, mut q: Vec<Vec<usize>>) -> Vec<usize> {
    let mut n = 0;
    for i in 0..p.len() {
        n += p[i].len();
    }
    let mut pi = vec![0; n];
    for ind in (0..n).rev() {
        let (mut i, mut j) = (0, 0);
        while i < q.len() {
            if let Ok(v) = q[i].binary_search(&ind) {
                j = v;
                break;
            }
            i += 1;
        }
        let mut cur = p[i][j];
        p[i].pop();
        q[i].pop();
        while i > 0 {
            i -= 1;
            j = p[i].partition_point(|&j| j <= cur);
            std::mem::swap(&mut p[i][j - 1], &mut cur);
        }
        pi[ind] = cur;
    }
    pi
}

// O(a + b + n)
pub fn hook_length<const M: u64>(l: &[usize]) -> usize {
    let mut n = 0;
    let l_t = conjugate(l);
    let mut d = 1;
    for i in 0..l.len() {
        n += l[i];
        for j in 0..l[i] {
            d = d * (l[i] - j + l_t[j] - i - 1) % M as usize;
        }
    }
    (ops::mod_fact::<M>(n as u64) as E * inv::<M>(d as E)).rem_euclid(M as E) as usize
}

// O(a + b + a log^3 a + √n)
// If a, b = O(√n), then O(√n log n)
pub fn hook_length_balanced<const M: u64>(l: &[usize]) -> usize {
    let a = l.len();
    let mut n = 0;
    let l = l
        .iter()
        .enumerate()
        .map(|(i, &j)| {
            n += j;
            (j + a - i - 1) as E
        })
        .collect::<Vec<_>>();
    let r = Poly::<M>::factorial(n) * Poly::<M>::vandermonde(&l) % M as E;
    let mut d = 1;
    let mut t = 1;
    let mut j = 1;
    for i in l.into_iter().rev() {
        while j < i {
            j += 1;
            t = (t * j) % M as E;
        }
        d = (d * t) % M as E;
    }
    (r * inv::<M>(d)).rem_euclid(M as E) as usize
}
