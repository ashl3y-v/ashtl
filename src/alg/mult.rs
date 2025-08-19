use super::{
    ops::{mod_pow, mod_pow_non_const},
    prime,
};
use bit_vec::BitVec;
use std::{
    collections::HashMap,
    ops::{AddAssign, Div, Mul, Sub},
};

pub fn eratosthenes_sieve(n: usize) -> BitVec {
    let mut is_composite = BitVec::from_elem(n, false);
    for i in 2..n.isqrt() + 1 {
        let mut j = i * 2;
        while j < n {
            is_composite.set(j, true);
            j += i;
        }
    }
    is_composite
}

pub fn sieve_primes(n: usize) -> (Vec<usize>, BitVec) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
        }
        for &p in &primes {
            if i * p >= n {
                break;
            }
            is_composite.set(i * p, true);
            if i.is_multiple_of(p) {
                break;
            }
        }
    }
    (primes, is_composite)
}

/// O(n + n F + n / log n G) if on_cop_pk costs F and on_pk costs G
pub fn sieve<T: Clone>(
    n: usize,
    id: T,
    mut on_cop_pk: impl FnMut(&T, &T) -> T,
    mut on_pk: impl FnMut(usize, u32, &[T]) -> T,
) -> (Vec<T>, BitVec, Vec<usize>, Vec<u32>) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n as usize);
    let mut known = Vec::with_capacity(n as usize);
    let mut cnt = vec![0; n];
    let mut f = vec![id.clone(); n];
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
            known.push(1);
            f[i] = on_pk(i, 1, &f);
            cnt[i] = 1;
        }
        for j in 0..primes.len() {
            let p = primes[j];
            if i * p >= n {
                break;
            }
            is_composite.set(i * p, true);
            if i.is_multiple_of(p) {
                let p_cnt = p.pow(cnt[i]);
                let f_p_cntip1 = if cnt[i] + 1 <= known[j] {
                    &f[p_cnt * p]
                } else {
                    known[j] = cnt[i] + 1;
                    &on_pk(p, cnt[i] + 1, &f)
                };
                f[i * p] = on_cop_pk(&f[i / p_cnt], f_p_cntip1);
                cnt[i * p] = cnt[i] + 1;
                break;
            } else {
                f[i * p] = on_cop_pk(&f[i], &f[p]);
                cnt[i * p] = 1;
            }
        }
    }
    (f, is_composite, primes, cnt)
}

/// O(n + n F + n / log n G) if on_coprime costs F and on_prime costs G
pub fn sieve_complete<T: Clone>(
    n: usize,
    id: T,
    mut on_mul: impl FnMut(&T, &T) -> T,
    mut on_p: impl FnMut(usize, &[T]) -> T,
) -> (Vec<T>, BitVec, Vec<usize>) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    let mut f = vec![id.clone(); n];
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
            f[i] = on_p(i, &f);
        }
        for &p in &primes {
            if i * p >= n {
                break;
            }
            is_composite.set(i * p, true);
            f[i * p] = on_mul(&f[i], &f[p]);
            if i.is_multiple_of(p) {
                break;
            }
        }
    }
    (f, is_composite, primes)
}

/// O(√n) if p_f and p_g are O(1)
pub fn mul_pref<
    T: Copy + Default + AddAssign + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
>(
    n: usize,
    k: usize,
    l: usize,
    mut p_f: impl FnMut(usize) -> T,
    mut p_g: impl FnMut(usize) -> T,
) -> T {
    let mut ans = T::default();
    let mut i = 1;
    while i <= k {
        let la = n / (n / i);
        ans += (p_f(la) - p_f(i - 1)) * p_g(n / i);
        i = la + 1;
    }
    let mut i = 1;
    while i <= l {
        let la = n / (n / i);
        ans += (p_g(la) - p_g(i - 1)) * p_f(n / i);
        i = la + 1;
    }
    ans - p_f(k) * p_g(l)
}

/// O(n^2/3) if p_g and p_c are O(1)
/// p_f should contain n^2/3 elements
pub fn pref_from_mul_pref<
    T: Copy + Default + AddAssign + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
>(
    n: usize,
    p_f: &[T],
    mut p_g: impl FnMut(usize) -> T,
    mut p_c: impl FnMut(usize) -> T,
    mut mem: HashMap<usize, T>,
) -> (T, HashMap<usize, T>) {
    fn calc<T: Copy + Default + AddAssign + Sub<Output = T> + Mul<Output = T> + Div<Output = T>>(
        x: usize,
        p_f: &[T],
        p_g: &mut impl FnMut(usize) -> T,
        p_c: &mut impl FnMut(usize) -> T,
        mem: &mut HashMap<usize, T>,
        inv: &T,
    ) -> T {
        if x < p_f.len() {
            return p_f[x];
        }
        if let Some(&d) = mem.get(&x) {
            return d;
        }
        let mut ans = T::default();
        let mut i = 2;
        while i <= x {
            let la = x / (x / i);
            ans += (p_g(la) - p_g(i - 1)) * calc(x / i, p_f, p_g, p_c, mem, inv);
            i = la + 1;
        }
        ans = (p_c(x) - ans) / inv.clone();
        mem.insert(x, ans);
        ans
    }
    let inv = p_g(1).clone();
    (calc(n, p_f, &mut p_g, &mut p_c, &mut mem, &inv), mem)
}

pub fn liouville(n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    sieve_complete(n, 1, |a, b| a * b, |_, _| -1)
}

pub fn j_k(k: u32, n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    if k == 1 {
        sieve(n, 1, |a, b| a * b, |p, i, _| p.pow(i - 1) * (p - 1))
    } else {
        sieve(
            n,
            1,
            |a, b| a * b,
            |p, i, _| p.pow((i - 1) * k) * (p.pow(k) - 1),
        )
    }
}

pub fn mobius(n: usize) -> (Vec<i8>, BitVec, Vec<usize>, Vec<u32>) {
    let mut s = sieve(n, 1, |a, b| a * b, |_, i, _| if i == 1 { -1 } else { 0 });
    s.0[0] = 0;
    s
}

pub fn gcd_k(k: usize, n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    let fs = prime::factor_mult(k);
    sieve(
        n,
        1,
        |a, b| a * b,
        |p, k, _| {
            if let Ok(i) = fs.binary_search_by_key(&p, |&(p, _)| p) {
                p.pow(k.min(fs[i].1))
            } else {
                1
            }
        },
    )
}

pub fn sigma_k(k: u32, n: usize) -> (Vec<u64>, BitVec, Vec<usize>, Vec<u32>) {
    let mut s = if k == 0 {
        sieve(n, 1, |a, b| a * b, |_, i, _| 1 + i as u64)
    } else if k == 1 {
        sieve(
            n,
            1,
            |a, b| a * b,
            |p, i, _| ((p as u64).pow(i + 1) - 1) / (p as u64 - 1),
        )
    } else {
        sieve(
            n,
            1,
            |a, b| a * b,
            |p, i, _| ((p as u64).pow((i + 1) * k) - 1) / ((p as u64).pow(k) - 1),
        )
    };
    s.0[0] = 0;
    s
}

pub fn gamma(n: usize) -> (Vec<i8>, BitVec, Vec<usize>, Vec<u32>) {
    sieve(n, 1, |a, b| a * b, |_, _, _| -1)
}

pub fn little_omega(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    sieve(n, 0, |a, b| a + b, |_, _, _| 1)
}

pub fn big_omega(n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    sieve_complete(n, 0, |a, b| a + b, |_, _| 1)
}

pub fn psi(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    sieve(n, 1, |a, b| a * b, |p, i, _| p.pow(i - 1) * (p + 1))
}

pub fn chi_0_a(a: usize, n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    let fs = prime::factor_dedup(a);
    sieve_complete(
        n,
        1,
        |a, b| a * b,
        |p, _| {
            if fs.binary_search(&p).is_ok() { 0 } else { 1 }
        },
    )
}

pub fn jacobi(a: usize, n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    sieve_complete(
        n,
        1,
        |a, b| a * b,
        |p, _| {
            if p == 2 {
                return match a & 7 {
                    1 => 1,
                    7 => 1,
                    3 => -1,
                    5 => -1,
                    _ => 0,
                };
            }
            let v = mod_pow_non_const(a as u64, p as u64 >> 1, p as u64);
            let v = if v == p as u64 - 1 { -1 } else { v as i8 };
            if a & p & 3 == 3 { -v } else { v }
        },
    )
}

pub fn jacobi_denom(a: usize, n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    if a == 2 {
        sieve_complete(
            n,
            1,
            |a, b| a * b,
            |p, _| match p & 7 {
                1 => 1,
                7 => 1,
                3 => -1,
                5 => -1,
                _ => 0,
            },
        )
    } else {
        sieve_complete(
            n,
            1,
            |a, b| a * b,
            |p, _| {
                let v = mod_pow_non_const(a as u64, p as u64 >> 1, p as u64);
                if v == p as u64 - 1 { -1 } else { v as i8 }
            },
        )
    }
}

pub fn val_p(p: usize, n: usize) -> (Vec<u32>, BitVec, Vec<usize>) {
    sieve_complete(n, 0, |a, b| a + b, |q, _| if q == p { 1 } else { 0 })
}

pub fn a0(n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    sieve_complete(n, 0, |a, b| a + b, |p, _| p)
}

pub fn a1(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    sieve(n, 0, |a, b| a + b, |p, _, _| p)
}

pub fn mod_pow_k<const M: u64>(k: usize, n: usize) -> (Vec<u64>, BitVec, Vec<usize>) {
    let mut s = sieve_complete(
        n,
        1,
        |a, b| a * b % M,
        |p, _| mod_pow::<M>(p as u64, k as u64),
    );
    s.0[0] = 0;
    s
}

pub fn factor(n: usize) -> (Vec<Vec<usize>>, BitVec, Vec<usize>) {
    let mut s = sieve_complete(
        n,
        vec![],
        |a, b| {
            let mut c = a.clone();
            c.extend_from_slice(&b);
            c
        },
        |p, _| vec![p],
    );
    s.0[0] = vec![0];
    s.0[1] = vec![1];
    s
}

pub fn factor_mult(n: usize) -> (Vec<Vec<(usize, u32)>>, BitVec, Vec<usize>, Vec<u32>) {
    let mut s = sieve(
        n,
        vec![],
        |a, b| {
            let mut c = a.clone();
            c.extend_from_slice(&b);
            c
        },
        |p, k, _| vec![(p, k)],
    );
    s.0[0] = vec![(0, 1)];
    s.0[1] = vec![(1, 1)];
    s
}

pub fn divisors(n: usize) -> (Vec<Vec<usize>>, BitVec, Vec<usize>, Vec<u32>) {
    let mut s = sieve(
        n,
        vec![1],
        |a, b| {
            let mut c = a.clone();
            for v in &b[1..] {
                for w in a {
                    c.push(v * w);
                }
            }
            c
        },
        |p, k, _| {
            let mut d = Vec::with_capacity(k as usize);
            let mut pi = 1;
            for _ in 0..=k {
                d.push(pi);
                pi *= p;
            }
            d
        },
    );
    s.0[0] = vec![0];
    s
}
