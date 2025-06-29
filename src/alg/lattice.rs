use std::ops::{Add, AddAssign, Mul, MulAssign, SubAssign};

/// O(n 2^n)
pub fn subset_zeta<T: Clone + AddAssign>(a: &mut [T]) {
    let n = a.len();
    let mut j = 1;
    while j < n {
        for i in 0..n {
            if i & j != 0 {
                let b = a[i ^ j].clone();
                a[i] += b;
            }
        }
        j <<= 1;
    }
}

/// O(n 2^n)
pub fn subset_mobius<T: Clone + SubAssign>(a: &mut [T]) {
    let n = a.len();
    let mut j = 1;
    while j < n {
        for i in 0..n {
            if i & j != 0 {
                let b = a[i ^ j].clone();
                a[i] -= b;
            }
        }
        j <<= 1;
    }
}

/// O(n 2^n)
pub fn superset_zeta<T: Clone + AddAssign>(a: &mut [T]) {
    let n = a.len();
    let mut j = 1;
    while j < n {
        for i in 0..n {
            if i & j != 0 {
                let b = a[i].clone();
                a[i ^ j] += b;
            }
        }
        j <<= 1;
    }
}

/// O(n 2^n)
pub fn superset_mobius<T: Clone + SubAssign>(a: &mut [T]) {
    let n = a.len();
    let mut j = 1;
    while j < n {
        for i in 0..n {
            if i & j != 0 {
                let b = a[i].clone();
                a[i ^ j] -= b;
            }
        }
        j <<= 1;
    }
}

/// O(n log log n)
pub fn divisor_zeta<T: Clone + AddAssign>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for &p in primes {
        let mut i = 1;
        let mut j = p;
        while j <= n {
            let b = a[i].clone();
            a[j] += b;
            i += 1;
            j += p;
        }
    }
}

/// O(n log log n)
pub fn divisor_mobius<T: Clone + SubAssign>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for p in primes {
        let mut i = n / p;
        let mut j = i * p;
        while i != 0 {
            let b = a[i].clone();
            a[j] -= b;
            i -= 1;
            j -= p;
        }
    }
}

/// O(n log log n)
pub fn multiple_zeta<T: Clone + AddAssign>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for p in primes {
        let mut i = n / p;
        let mut j = i * p;
        while i != 0 {
            let b = a[j].clone();
            a[i] += b;
            i -= 1;
            j -= p;
        }
    }
}

/// O(n log log n)
pub fn multiple_mobius<T: Clone + SubAssign>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for &p in primes {
        let mut i = 1;
        let mut j = p;
        while j <= n {
            let b = a[j].clone();
            a[i] -= b;
            i += 1;
            j += p;
        }
    }
}

pub fn gcd_convolution<T: Clone + AddAssign + SubAssign + MulAssign>(
    a: &mut [T],
    b: &mut [T],
    primes: &[usize],
) {
    multiple_zeta(a, &primes);
    multiple_zeta(b, &primes);
    for i in 0..a.len() {
        a[i] *= b[i].clone();
    }
    multiple_mobius(a, &primes);
}

pub fn lcm_convolution<T: Clone + AddAssign + SubAssign + MulAssign>(
    a: &mut [T],
    b: &mut [T],
    primes: &[usize],
) {
    divisor_zeta(a, &primes);
    divisor_zeta(b, &primes);
    for i in 0..a.len() {
        a[i] *= b[i].clone();
    }
    divisor_mobius(a, &primes);
}

pub fn subset_convolution<
    T: Clone
        + Default
        + AddAssign<T>
        + for<'a> AddAssign<&'a T>
        + for<'a> SubAssign<&'a T>
        + for<'a> Mul<&'a T, Output = T>,
>(
    n: usize,
    f: &[T],
    g: &[T],
) -> Vec<T> {
    let mut fhat = vec![vec![T::default(); 1 << n]; n + 1];
    let mut ghat = vec![vec![T::default(); 1 << n]; n + 1];
    for m in 0_usize..1 << n {
        fhat[m.count_ones() as usize][m] = f[m].clone();
        ghat[m.count_ones() as usize][m] = g[m].clone();
    }
    for i in 0..=n {
        for j in 0..=n {
            for m in 0..1 << n {
                if m & (1 << j) != 0 {
                    let [fhat_m, fhat_mxor] = fhat[i].get_disjoint_mut([m, m ^ (1 << j)]).unwrap();
                    *fhat_m += &*fhat_mxor;
                    let [ghat_m, ghat_mxor] = ghat[i].get_disjoint_mut([m, m ^ (1 << j)]).unwrap();
                    *ghat_m += &*ghat_mxor;
                }
            }
        }
    }
    let mut h = vec![vec![T::default(); 1 << n]; n + 1];
    for m in 0..1 << n {
        for i in 0..=n {
            for j in 0..=i {
                h[i][m] += fhat[j][m].clone() * &ghat[i - j][m];
            }
        }
    }
    for i in 0..=n {
        for j in 0..n {
            for m in 0..1 << n {
                if m & (1 << j) != 0 {
                    let [h_m, h_mxor] = h[i].get_disjoint_mut([m, m ^ (1 << j)]).unwrap();
                    *h_m -= &*h_mxor;
                }
            }
        }
    }
    let mut fog = vec![T::default(); 1 << n];
    for m in 0..1 << n {
        fog[m] = h[m.count_ones() as usize][m].clone();
    }
    fog
}
