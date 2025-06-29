use super::{
    ops::{mod_pow, mod_pow_non_const},
    prime::{factor_dedup, factor_mult},
};
use bit_vec::BitVec;

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

pub fn linear_sieve_primes(n: usize) -> (BitVec, Vec<usize>) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
        }
        for j in 0..primes.len() {
            if i * primes[j] >= n {
                break;
            }
            is_composite.set(i * primes[j], true);
            if i.is_multiple_of(primes[j]) {
                break;
            }
        }
    }
    (is_composite, primes)
}

/// O(n + n F + n / log n G) if on_coprime costs F and on_prime_pow costs G
pub fn linear_sieve<T: Clone>(
    n: usize,
    id: T,
    mut on_coprime: impl FnMut(&T, &T) -> T,
    mut on_prime_pow: impl FnMut(usize, u32, &[T]) -> T,
) -> (Vec<T>, BitVec, Vec<usize>, Vec<u32>) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    let mut known = Vec::with_capacity(n / n.ilog2() as usize);
    let mut cnt = vec![0; n];
    let mut f = vec![id.clone(); n];
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
            known.push(1);
            f[i] = on_prime_pow(i, 1, &f);
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
                let p_cntip1 = if cnt[i] + 1 <= known[j] {
                    &f[p_cnt * p]
                } else {
                    known[j] = cnt[i] + 1;
                    &on_prime_pow(p, cnt[i] + 1, &f)
                };
                f[i * p] = on_coprime(&f[i / p_cnt], p_cntip1);
                cnt[i * p] = cnt[i] + 1;
                break;
            } else {
                f[i * p] = on_coprime(&f[i], &f[p]);
                cnt[i * p] = 1;
            }
        }
    }
    (f, is_composite, primes, cnt)
}

/// O(n + n F + n / log n G) if on_coprime costs F and on_prime costs G
pub fn linear_sieve_complete<T: Clone>(
    n: usize,
    id: T,
    mut on_coprime: impl FnMut(&T, &T) -> T,
    mut on_prime: impl FnMut(usize, &[T]) -> T,
) -> (Vec<T>, BitVec, Vec<usize>) {
    let mut is_composite = BitVec::from_elem(n, false);
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    let mut f = vec![id.clone(); n];
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
            f[i] = on_prime(i, &f);
        }
        for &p in &primes {
            if i * p >= n {
                break;
            }
            is_composite.set(i * p, true);
            f[i * p] = on_coprime(&f[i], &f[p]);
            if i.is_multiple_of(p) {
                break;
            }
        }
    }
    (f, is_composite, primes)
}

pub fn liouville(n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    linear_sieve_complete(n, 1, |a, b| a * b, |_, _| -1)
}

pub fn j_k(k: u32, n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    if k == 1 {
        linear_sieve(n, 1, |a, b| a * b, |p, i, _| p.pow(i - 1) * (p - 1))
    } else {
        linear_sieve(
            n,
            1,
            |a, b| a * b,
            |p, i, _| p.pow((i - 1) * k) * (p.pow(k) - 1),
        )
    }
}

pub fn mobius(n: usize) -> (Vec<i8>, BitVec, Vec<usize>, Vec<u32>) {
    linear_sieve(n, 1, |a, b| a * b, |_, i, _| if i == 1 { -1 } else { 0 })
}

pub fn gcd_k(k: usize, n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    let fs = factor_mult(k);
    linear_sieve(
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
        linear_sieve(n, 1, |a, b| a * b, |_, i, _| 1 + i as u64)
    } else if k == 1 {
        linear_sieve(
            n,
            1,
            |a, b| a * b,
            |p, i, _| ((p as u64).pow(i + 1) - 1) / (p as u64 - 1),
        )
    } else {
        linear_sieve(
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
    linear_sieve(n, 1, |a, b| a * b, |_, _, _| -1)
}

pub fn little_omega(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    linear_sieve(n, 0, |a, b| a + b, |_, _, _| 1)
}

pub fn big_omega(n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    linear_sieve_complete(n, 0, |a, b| a + b, |_, _| 1)
}

pub fn psi(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    linear_sieve(n, 1, |a, b| a * b, |p, i, _| p.pow(i - 1) * (p + 1))
}

pub fn chi_0_a(a: usize, n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    let fs = factor_dedup(a);
    linear_sieve_complete(
        n,
        1,
        |a, b| a * b,
        |p, _| {
            if fs.binary_search(&p).is_ok() { 0 } else { 1 }
        },
    )
}

pub fn jacobi(a: usize, n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    linear_sieve_complete(
        n,
        1,
        |a, b| a * b,
        |p, _| {
            if p == 2 {
                return if a & 1 == 0 {
                    0
                } else if ((a * a - 1) >> 3) & 1 == 0 {
                    1
                } else {
                    -1
                };
            }
            let v = mod_pow_non_const(a as u64, p as u64 >> 1, p as u64);
            let v = if v == p as u64 - 1 { -1 } else { v as i8 };
            if a & 3 == 3 && p & 3 == 3 { -v } else { v }
        },
    )
}

pub fn jacobi_denom(a: usize, n: usize) -> (Vec<i8>, BitVec, Vec<usize>) {
    if a == 2 {
        linear_sieve_complete(
            n,
            1,
            |a, b| a * b,
            |p, _| {
                if p & 1 == 0 {
                    0
                } else if ((p * p - 1) >> 3) & 1 == 0 {
                    1
                } else {
                    -1
                }
            },
        )
    } else {
        linear_sieve_complete(
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
    linear_sieve_complete(n, 0, |a, b| a + b, |q, _| if q == p { 1 } else { 0 })
}

pub fn a0(n: usize) -> (Vec<usize>, BitVec, Vec<usize>) {
    linear_sieve_complete(n, 0, |a, b| a + b, |p, _| p)
}

pub fn a1(n: usize) -> (Vec<usize>, BitVec, Vec<usize>, Vec<u32>) {
    linear_sieve(n, 0, |a, b| a + b, |p, _, _| p)
}

pub fn mod_pow_k<const M: u64>(k: usize, n: usize) -> (Vec<u64>, BitVec, Vec<usize>) {
    let mut s = linear_sieve_complete(
        n,
        1,
        |a, b| a * b % M,
        |p, _| mod_pow::<M>(p as u64, k as u64),
    );
    s.0[0] = 0;
    s
}
