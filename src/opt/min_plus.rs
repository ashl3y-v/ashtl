use std::ops::Add;

use crate::opt::smawk::smawk;

/// O(n)
pub fn min_plus_cvx_cvx(a: &[i64], b: &[i64]) -> Vec<i64> {
    if a.is_empty() || b.is_empty() {
        return if a.is_empty() { b.to_vec() } else { a.to_vec() };
    }
    let (n0, n1) = (a.len(), b.len());
    let mut c = vec![0; n0 + n1 - 1];
    let (mut i0, mut i1) = (0, 0);
    c[0] = a[i0] + b[i1];
    for i in 1..n0 + n1 - 1 {
        if i1 == n1 - 1 || (i0 != n0 - 1 && a[i0 + 1] + b[i1] < a[i0] + b[i1 + 1]) {
            i0 += 1;
        } else {
            i1 += 1;
        }
        c[i] = a[i0] + b[i1];
    }
    c
}

/// O(n)
pub fn max_plus_cvx_cvx(a: &[i64], b: &[i64]) -> Vec<i64> {
    if a.is_empty() || b.is_empty() {
        return if a.is_empty() { b.to_vec() } else { a.to_vec() };
    }
    let (n0, n1) = (a.len(), b.len());
    let mut c = vec![0; n0 + n1 - 1];
    let (mut i0, mut i1) = (0, 0);
    c[0] = a[i0] + b[i1];
    for i in 1..n0 + n1 - 1 {
        if i1 == n1 - 1 || (i0 != n0 - 1 && a[i0 + 1] + b[i1] >= a[i0] + b[i1 + 1]) {
            i0 += 1;
        } else {
            i1 += 1;
        }
        c[i] = a[i0] + b[i1];
    }
    c
}

/// O(n)
pub fn min_plus_cvx<T: Copy + PartialOrd + Add<Output = T>>(a: &[T], b: &[T]) -> Vec<T> {
    let (n, m) = (a.len(), b.len());
    let get = |i, j| a[j] + b[i - j];
    let select = |i, j, k| {
        if i < k {
            false
        } else if i - j >= m {
            true
        } else {
            get(i, j) >= get(i, k)
        }
    };
    smawk(n + m - 1, n, select)
        .into_iter()
        .enumerate()
        .map(|(i, amax)| get(i, amax))
        .collect()
}

/// O(n)
pub fn max_plus_cvx<T: Copy + PartialOrd + Add<Output = T>>(a: &[T], b: &[T]) -> Vec<T> {
    let (n, m) = (a.len(), b.len());
    let get = |i, j| a[j] + b[i - j];
    let select = |i, j, k| {
        if i < k {
            false
        } else if i - j >= m {
            true
        } else {
            get(i, j) <= get(i, k)
        }
    };
    smawk(n + m - 1, n, select)
        .into_iter()
        .enumerate()
        .map(|(i, amax)| get(i, amax))
        .collect()
}

/// O(n^2)
pub fn min_plus(a: &[i64], b: &[i64]) -> Vec<i64> {
    let (n, m) = (a.len(), b.len());
    let mut c = vec![i64::MAX; n + m - 1];
    for i in 0..n {
        for j in 0..m {
            c[i + j] = c[i + j].min(a[i] + b[j]);
        }
    }
    c
}

/// O(n^2)
pub fn max_plus(a: &[i64], b: &[i64]) -> Vec<i64> {
    let (n, m) = (a.len(), b.len());
    let mut c = vec![i64::MIN; n + m - 1];
    for i in 0..n {
        for j in 0..m {
            c[i + j] = c[i + j].max(a[i] + b[j]);
        }
    }
    c
}
