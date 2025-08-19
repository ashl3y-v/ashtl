use super::{gcd::euclidean, poly::Affine, primitive};
use std::{
    collections::HashMap,
    ops::{Div, Mul, Neg, Rem, Sub},
};

pub fn mod_fact<const M: u64>(n: u64) -> u64 {
    (1..=n).fold(1, |acc, x| acc * x % M)
}

pub fn mod_rfact<const M: u64>(n: u64) -> i64 {
    inv::<M>(mod_fact::<M>(n) as i64)
}

pub fn mod_rfact_u<const M: u64>(n: u64) -> u64 {
    inv::<M>(mod_fact::<M>(n) as i64).rem_euclid(M as i64) as u64
}

pub fn fact(n: u64) -> u64 {
    (1..=n).product()
}

pub fn mod_fact_alt<const M: u64>(mut n: u64) -> u64 {
    let mut f = vec![0; M as usize];
    f[0] = 1;
    for i in 1..M as usize {
        f[i] = f[i - 1] * i as u64 % M;
    }
    let mut res = 1;
    while n > 1 {
        if (n / M) & 1 != 0 {
            res = M - res
        }
        res *= f[(n % M) as usize] % M;
        n /= M;
    }
    res
}

pub fn fact_mult(mut n: u64, p: u64) -> u64 {
    let mut c = 0;
    loop {
        n /= p;
        c += n;
        if n == 0 {
            break;
        }
    }
    c
}

/// O(sum_{i=1}^{log_M n} min(k_i, n_i - k_i))
pub fn mod_binom<const M: u64>(mut n: u64, mut k: u64) -> u64 {
    if k > n {
        return 0;
    }
    let mut r = 1;
    let mut a;
    let mut b;
    while k != 0 {
        (n, a, k, b) = (n / M, n % M, k / M, k % M);
        if b > a {
            return 0;
        } else if b < a >> 1 {
            b = a - b;
        }
        r = r * mod_rfact_u::<M>(a - b) % M * (b + 1..=a).fold(1, |acc, x| acc * x % M) % M;
    }
    r
}

pub const fn mod_pow<const M: u64>(mut a: u64, mut b: u64) -> u64 {
    a %= M;
    let mut ab = 1;
    while b != 0 {
        if b & 1 != 0 {
            ab *= a;
            ab %= M;
        }
        a *= a;
        a %= M;
        b >>= 1;
    }

    ab
}

pub const fn mod_pow_signed<const M: u64>(mut a: i64, mut b: u64) -> i64 {
    a %= M as i64;
    let mut ab = 1;
    while b != 0 {
        if b & 1 != 0 {
            ab *= a;
            ab %= M as i64;
        }
        a *= a;
        a %= M as i64;
        b >>= 1;
    }

    ab
}

pub const fn mod_pow_pow_two<const M: u64>(mut a: u64, b: u64) -> u64 {
    let mut i = 0;
    while i < b {
        a *= a;
        a %= M;
        i += 1;
    }
    a
}

pub const fn mod_pow_pow_two_signed<const M: u64>(mut a: i64, b: u64) -> i64 {
    let mut i = 0;
    while i < b {
        a *= a;
        a %= M as i64;
        i += 1;
    }
    a
}

pub const fn mod_pow_non_const(mut a: u64, mut b: u64, m: u64) -> u64 {
    let mut ab = 1;
    while b != 0 {
        if b & 1 != 0 {
            ab *= a;
            ab %= m;
        }
        a *= a;
        a %= m;
        b >>= 1;
    }

    ab
}

#[inline]
pub const fn inverse_pow<const M: u64>(a: u64) -> u64 {
    mod_pow::<M>(a, M - 2)
}

#[inline]
pub const fn inverse_div<const M: u64>(a: u64) -> u64 {
    if a <= 1 {
        return a;
    }
    M - M / a * inverse_div::<M>(M % a) % M
}

#[inline]
pub fn inverses_n_div<const M: u64>(n: usize) -> Vec<u64> {
    let mut inv = vec![0_u64; n];
    if n <= 1 {
        return inv;
    }
    inv[1] = 1;
    for a in 2..n.min(M as usize) {
        inv[a] = M - M / a as u64 * inv[M as usize % a] % M;
    }
    for a in n.min(M as usize)..n {
        inv[a] = inv[a % M as usize];
    }
    inv
}

#[inline]
pub fn inverses<const M: u64, T>(a: &[T]) -> Vec<T>
where
    T: Copy
        + Default
        + PartialOrd
        + Neg<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>,
    i64: Into<T>,
{
    let n = a.len();
    let mut b = Vec::with_capacity(n);
    let mut p = 1.into();
    for i in 0..n {
        b.push(p);
        p = p * a[i] % (M as i64).into();
    }
    let mut x = inverse_euclidean::<M, _>(p);
    for i in (0..n).rev() {
        b[i] = b[i] * x % (M as i64).into();
        x = x * a[i] % (M as i64).into();
    }
    b
}

#[inline]
pub fn inverse_euclidean<const M: u64, T>(a: T) -> T
where
    T: Copy
        + Default
        + PartialOrd
        + Neg<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>,
    i64: Into<T>,
{
    let (mut t, mut nt, mut r, mut nr) = (
        T::default(),
        1.into(),
        (M as i64).into(),
        if a < T::default() { -a } else { a },
    );
    while nr != T::default() {
        let q = r / nr;
        (t, nt) = (nt, t - q * nt);
        (r, nr) = (nr, r - q * nr);
    }
    if r != 1.into() {
        return T::default();
    }
    if a >= T::default() { t } else { -t }
}

#[inline]
pub const fn inv<const M: u64>(a: i64) -> i64 {
    let (mut t, mut nt, mut r, mut nr) = (0, 1, M as i64, a.abs());
    while nr != 0 {
        let q = r / nr;
        (t, nt) = (nt, t - q * nt);
        (r, nr) = (nr, r - q * nr);
    }
    if r != 1 {
        return 0;
    }
    if a >= 0 { t } else { -t }
}

#[inline]
pub const fn inverse_euclidean_non_gen(a: u64, m: u64) -> u64 {
    let (mut t, mut nt, mut r, mut nr) = (0_i64, 1, m as i64, a as i64);
    while nr != 0 {
        let q = r / nr;
        (t, nt) = (nt, t - q * nt);
        (r, nr) = (nr, r - q * nr);
    }
    if r > 1 {
        return 0;
    }
    if t < 0 {
        t += m as i64;
    }
    return t as u64;
}

// O(√M)
pub fn discrete_log<const M: u64>(a: u64, b: u64) -> Option<usize> {
    if M == 1 {
        return Some(0);
    } else if a % M == 0 {
        return if b % M == 0 { Some(1) } else { None };
    } else if b % M == 1 {
        return Some(0);
    }
    let m = M.isqrt();
    let m = (m + if m * m == M { 0 } else { 1 }).max(1) as usize;
    let mut baby_steps = HashMap::with_capacity(m);
    let a_inv = inverse_euclidean::<M, _>(a as i64).rem_euclid(M as i64) as u64;
    let mut gamma = 1u64;
    for j in 0..m {
        baby_steps.insert((gamma * b) % M, j);
        gamma = (gamma * a_inv) % M;
    }
    let mut giant_step = 1u64;
    let a_m = mod_pow::<M>(a, m as u64);
    for i in 0..m {
        if let Some(&j) = baby_steps.get(&giant_step) {
            return Some((i * m + j) as usize);
        }
        giant_step = (giant_step * a_m) % M;
    }
    None
}

#[inline]
pub fn mod_sqrt<const M: u64>(b: u64) -> Option<u64> {
    if b == 0 {
        return Some(0);
    } else if b == 1 {
        return Some(1);
    }
    let exp = (M - 1) / 2;
    if mod_pow::<M>(b, exp) != 1 {
        return None;
    }
    let mut z = 1;
    loop {
        z = (z * z + 1) % M;
        if z * z == b {
            if z < M - z {
                return Some(z);
            } else {
                return Some(M - z);
            }
        }
        let x = Affine::<M>::new(z, 1, b);
        let result = x.pow(exp);
        if result.b != 0 {
            let inv = inverse_euclidean::<M, _>(result.b as i64).rem_euclid(M as i64) as u64;
            if inv != 0 {
                if inv < M - inv {
                    return Some(inv);
                } else {
                    return Some(M - inv);
                }
            }
        }
    }
}

#[inline]
pub const fn mod_sqrt_n1<const M: u64>() -> u64 {
    let d = const { mod_pow::<M>(primitive::find_primitive_root::<M>(), (M - 1) >> 2) };
    if d > M >> 1 { M - d } else { d }
}

/// if odd part of k is coprime with M-1 then O(polylog M) else O(√M)
#[inline]
pub fn mod_k_rt<const M: u64>(mut a: u64, mut k: usize) -> Option<u64> {
    a %= M;
    if a == 0 {
        return Some(0);
    } else if a == 1 {
        return Some(1);
    } else if k == 1 || (k == 0 && a == 0) {
        return Some(a);
    }
    const fn phi<const M: u64>() -> u64 {
        M - 1
    }
    while k & 1 == 0 {
        a = mod_sqrt::<M>(a)?;
        k >>= 1;
    }
    let phi = phi::<M>();
    let (gcd, x, _) = euclidean(k as i128, phi as i128);
    if gcd == 1 {
        let k_inv = inverse_euclidean_non_gen(k as u64, phi);
        return Some(mod_pow::<M>(a, k_inv));
    }
    let g = primitive::find_primitive_root::<M>();
    let alpha = discrete_log::<M>(g, a)?;
    let (gcd, x) = (
        gcd.rem_euclid(M as i128) as usize,
        x.rem_euclid(M as i128) as usize,
    );
    if alpha % gcd != 0 {
        return None;
    }
    let (alpha_r, phi_r) = (alpha / gcd, phi as usize / gcd);
    let beta = (alpha_r * x).rem_euclid(phi_r);
    Some(mod_pow::<M>(g, beta as u64))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_discrete_log() {
        // Test case: 2^x ≡ 8 (mod 13)
        // Answer should be 3 since 2^3 = 8
        assert_eq!(discrete_log::<13>(2, 8), Some(3));

        // Test case: 3^x ≡ 1 (mod 7)
        // Answer should be 0 since 3^0 = 1
        assert_eq!(discrete_log::<7>(3, 1), Some(0));

        // Test case: 5^x ≡ 6 (mod 11)
        // 5^1 = 5, 5^2 = 25 ≡ 3, 5^3 = 15 ≡ 4, 5^4 = 20 ≡ 9, 5^5 = 45 ≡ 1
        // 5^6 = 5, 5^7 = 25 ≡ 3, 5^8 = 15 ≡ 4, 5^9 = 20 ≡ 9, 5^10 = 45 ≡ 1
        // So 5^? ≡ 6 has no solution in this range
        assert_eq!(discrete_log::<11>(5, 6), None);

        // Test case: 2^x ≡ 4 (mod 5)
        // 2^1 = 2, 2^2 = 4, so answer is 2
        assert_eq!(discrete_log::<5>(2, 4), Some(2));
    }
}
