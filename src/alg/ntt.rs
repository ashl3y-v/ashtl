use super::{
    ops::{inverse_euclidean, mod_pow_pow_two, mod_pow_pow_two_signed},
    prime::miller_rabin,
    primitive::find_ntt_root,
    sieve,
};

pub fn find_ntt_prime(n: u64, b: u64) -> u64 {
    for k in (0..(b - 1) / n).rev() {
        if miller_rabin(k * n + 1) {
            return k;
        }
    }
    0
}

pub fn find_ntt_prime_min_big_omega(n: u64, b: u64) -> (u64, u64) {
    let (mut cur_big_omega, mut cur_k) = (usize::MAX, 0);
    let big_omega = sieve::big_omega(((b - 1) / n) as usize).0;
    for k in (0..(b - 1) / n).rev() {
        if miller_rabin(k * n + 1) {
            if big_omega[k as usize] < cur_big_omega
                || (big_omega[k as usize] == cur_big_omega && k > cur_k)
            {
                (cur_big_omega, cur_k) = (big_omega[k as usize], k);
            }
        }
    }
    return (cur_big_omega as u64, cur_k);
}

// TODO: improve NTT performance
// https://codeforces.com/blog/entry/142063

pub fn ntt<const M: u64>(a: &mut [i64]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let mut rt = vec![0; n];
    rt[0..2].fill(1);
    let mut k = 2;
    let mut s = 2;
    while k < n {
        let x =
            mod_pow_pow_two::<M>(find_ntt_root::<M>(), (M - 1).trailing_zeros() as u64 - s) as i64;
        for i in (k..k << 1).step_by(2) {
            rt[i] = rt[i >> 1];
            rt[i + 1] = rt[i >> 1] * x % M as i64;
        }
        k <<= 1;
        s += 1;
    }
    let mut k = n >> 1;
    while k > 0 {
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let (ij, ijk) = (i + j, i + j + k);
                let a_ij = a[ij];
                a[ij] = (a_ij + a[ijk]) % M as i64;
                a[ijk] = rt[j + k] * (a_ij - a[ijk]) % M as i64;
            }
            i += k << 1;
        }
        k >>= 1;
    }
}

pub fn intt<const M: u64>(a: &mut [i64]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let mut rt = vec![0; n];
    rt[0..2].fill(1);
    let mut k = 2;
    let mut s = 2;
    while k < n {
        let x = mod_pow_pow_two_signed::<M>(
            inverse_euclidean::<M, _>(find_ntt_root::<M>() as i64),
            (M - 1).trailing_zeros() as u64 - s,
        ) as i64;
        for i in (k..k << 1).step_by(2) {
            rt[i] = rt[i >> 1];
            rt[i + 1] = rt[i >> 1] * x % M as i64;
        }
        k <<= 1;
        s += 1;
    }
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let (ij, ijk) = (i + j, i + j + k);
                let z = rt[j + k] * a[ijk];
                a[ijk] = (a[ij] - z) % M as i64;
                a[ij] = (a[ij] + z) % M as i64;
            }
            i += k << 1;
        }
        k <<= 1;
    }
    let n_inv = inverse_euclidean::<M, _>(n as i64);
    a.iter_mut().for_each(|i| {
        *i *= n_inv as i64;
    });
}

pub fn ntt_conv<const M: u64>(a: &mut Vec<i64>, b: &mut Vec<i64>) {
    let deg = |a: &[i64]| a.iter().rposition(|&i| i % M as i64 != 0);
    let d0 = deg(a);
    let d1 = deg(b);
    if let Some(d0) = d0
        && let Some(d1) = d1
    {
        let n = (d0 + d1 + 1).next_power_of_two();
        a.resize(n, 0);
        b.resize(n, 0);
        ntt::<M>(a);
        ntt::<M>(b);
        a.iter_mut().zip(b).for_each(|(i, j)| *i *= *j);
        intt::<M>(a);
    } else {
        a.clear();
    }
}

pub fn ntt_conv_self<const M: u64>(a: &mut Vec<i64>) {
    let d = a.iter().rposition(|&i| i % M as i64 != 0);
    if let Some(d) = d {
        let n = ((d << 1) + 1).next_power_of_two();
        a.resize(n, 0);
        ntt::<M>(a);
        a.iter_mut().for_each(|i| *i *= *i);
        intt::<M>(a);
    }
}
