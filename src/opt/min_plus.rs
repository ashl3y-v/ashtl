use std::{mem::MaybeUninit, ops::Add};

use crate::opt::smawk::smawk;
use crate::tree::li_chao::{LiChao, LiChaoFunc, NoLazy};

/// O(n + m)
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

/// O(n + m)
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

/// O(m log (n + m))
pub fn min_plus_cvx<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + PartialOrd + Add<Output = T>,
{
    min_plus_cvx_dc(a, b, |new_val, best_val| new_val < best_val)
}

/// O(m log (n + m))
pub fn max_plus_ccv<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + PartialOrd + Add<Output = T>,
{
    min_plus_cvx_dc(a, b, |new_val, best_val| new_val > best_val)
}

fn min_plus_cvx_dc<T, F>(a: &[T], b: &[T], is_better: F) -> Vec<T>
where
    T: Copy + Add<Output = T>,
    F: Fn(T, T) -> bool,
{
    let (n, m) = (a.len(), b.len());
    if n == 0 || m == 0 {
        return vec![];
    }
    let z = n + m - 1;
    let mut res: Vec<MaybeUninit<T>> = Vec::with_capacity(z);
    unsafe {
        res.set_len(z);
    }
    let mut pos = vec![0; z + 1];
    res[0].write(a[0] + b[0]);
    pos[0] = 0;
    pos[z] = m - 1;
    let mut d = 1;
    while d < z {
        d <<= 1;
    }
    let mut len = d >> 1;
    while len > 0 {
        let mut i = len;
        while i < z {
            let l = i - len;
            let r = z.min(i + len);
            let k_min = pos[l].max(if i >= n { i - n + 1 } else { 0 });
            let k_max = pos[r].min(i).min(m - 1);
            let mut best_k = k_min;
            let mut best_v = b[best_k] + a[i - best_k];
            for k in k_min + 1..=k_max {
                let val = b[k] + a[i - k];
                if is_better(val, best_v) {
                    best_v = val;
                    best_k = k;
                }
            }
            res[i].write(best_v);
            pos[i] = best_k;
            i += len << 1;
        }
        len >>= 1;
    }
    unsafe { std::mem::transmute(res) }
}

/// O(m log n + n)
pub fn min_plus_ccv(a: &[i64], b: &[i64]) -> Vec<i64> {
    const INF: i64 = i64::MAX / 2;

    #[derive(Clone, Debug)]
    struct FuncFwd<'a> {
        idx: usize,
        a: &'a [i64],
        b: &'a [i64],
        s: usize,
        is_max: bool,
    }

    impl<'a> LiChaoFunc for FuncFwd<'a> {
        fn eval(&self, i: i64) -> i64 {
            if self.is_max {
                return INF;
            }
            let i = i as usize;
            if i < self.idx {
                -INF - self.idx as i64
            } else {
                if i - self.idx >= self.a.len() {
                    INF
                } else {
                    self.a[i - self.idx] + self.b[self.s + self.idx]
                }
            }
        }
        fn max() -> Self {
            Self {
                idx: 0,
                a: &[],
                b: &[],
                s: 0,
                is_max: true,
            }
        }
    }

    #[derive(Clone, Debug)]
    struct FuncRev<'a> {
        idx: usize,
        a: &'a [i64],
        b: &'a [i64],
        s: usize,
        n: usize,
        is_max: bool,
    }

    impl<'a> LiChaoFunc for FuncRev<'a> {
        fn eval(&self, i: i64) -> i64 {
            if self.is_max {
                return INF;
            }
            let i = i as usize;
            if self.idx < i {
                -INF + self.idx as i64
            } else {
                let a_idx = (self.n as i64 - 1) - (self.idx as i64 - i as i64);
                if a_idx < 0 || a_idx >= self.a.len() as i64 {
                    INF
                } else {
                    self.a[a_idx as usize] + self.b[self.s + self.idx]
                }
            }
        }
        fn max() -> Self {
            Self {
                idx: 0,
                a: &[],
                b: &[],
                s: 0,
                n: 0,
                is_max: true,
            }
        }
    }

    let n = a.len();
    let m = b.len();
    let mut c = vec![INF; n + m - 1];
    let mut s = 0;
    while s < m {
        let n_chunk = if m - s <= n { m - s } else { n + 1 };
        let mut ds1 = LiChao::<FuncFwd, NoLazy>::with_capacity(0, n as i64, 2 * n);
        for i in 0..n {
            if s + i < m {
                ds1.add(FuncFwd {
                    idx: i,
                    a: &a,
                    b: &b,
                    s,
                    is_max: false,
                });
            }
            let best_idx = ds1.query(i as i64).1;
            let best_func = &ds1.ns[best_idx].x;
            let k = if best_func.is_max {
                usize::MAX
            } else {
                best_func.idx
            };
            let val = if i < k {
                INF
            } else {
                if i - k >= a.len() {
                    INF
                } else {
                    a[i - k] + b[s + k]
                }
            };
            if s + i < c.len() && val < c[s + i] {
                c[s + i] = val;
            }
        }
        let mut ds2 = LiChao::<FuncRev, NoLazy>::with_capacity(1, n as i64, 2 * n);
        for i in (1..n_chunk).rev() {
            ds2.add(FuncRev {
                idx: i,
                a: &a,
                b: &b,
                s,
                n,
                is_max: false,
            });
            let best_idx = ds2.query(i as i64).1;
            let best_func = &ds2.ns[best_idx].x;
            let k = if best_func.is_max {
                usize::MAX
            } else {
                best_func.idx
            };
            let p = s + (n - 1) + i;
            let val = if i > k {
                INF
            } else {
                let a_idx = (n as i64 - 1) - (k as i64 - i as i64);
                if a_idx < 0 || a_idx >= a.len() as i64 {
                    INF
                } else {
                    a[a_idx as usize] + b[s + k]
                }
            };
            if p < c.len() && val < c[p] {
                c[p] = val;
            }
        }
        s += n + 1;
    }
    c
}

/// O(m log n + n)
pub fn max_plus_cvx(a: &[i64], b: &[i64]) -> Vec<i64> {
    let (mut a, mut b) = (a.to_vec(), b.to_vec());
    for i in 0..a.len().min(b.len()) {
        a[i] = -a[i];
        b[i] = -b[i];
    }
    for i in a.len().min(b.len())..a.len() {
        a[i] = -a[i];
    }
    for i in a.len().min(b.len())..b.len() {
        b[i] = -b[i];
    }
    let mut c = min_plus_ccv(&a, &b);
    for i in 0..c.len() {
        c[i] = -c[i];
    }
    c
}

/// O(n + m)
pub fn min_plus_cvx_smawk<T: Copy + PartialOrd + Add<Output = T>>(a: &[T], b: &[T]) -> Vec<T> {
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

/// O(n + m)
pub fn max_plus_ccv_smawk<T: Copy + PartialOrd + Add<Output = T>>(a: &[T], b: &[T]) -> Vec<T> {
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

/// O(n m)
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

/// O(n m)
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
