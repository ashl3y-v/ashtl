use super::{mult, prime::miller_rabin, primitive::find_ntt_root};
use crate::alg::ops::inv;

pub fn find_ntt_prime(n: u64, b: u64) -> u64 {
    for k in (0..(b - 1) / n).rev() {
        if miller_rabin(k * n + 1) {
            return k;
        }
    }
    0
}

// pub fn find_ntt_prime_min_big_omega(n: u64, b: u64) -> (u64, u64) {
//     let (mut cur_big_omega, mut cur_k) = (usize::MAX, 0);
//     let big_omega = mult::big_omega(((b - 1) / n) as usize).0;
//     for k in (0..(b - 1) / n).rev() {
//         if miller_rabin(k * n + 1) {
//             if big_omega[k as usize] < cur_big_omega
//                 || (big_omega[k as usize] == cur_big_omega && k > cur_k)
//             {
//                 (cur_big_omega, cur_k) = (big_omega[k as usize], k);
//             }
//         }
//     }
//     return (cur_big_omega as u64, cur_k);
// }

pub const fn root_pows<const M: u64>() -> [u64; 32] {
    let mut x = const { find_ntt_root::<M>() };
    let mut xs = [0; 32];
    let mut i = 0;
    while i < 32 {
        xs[i] = x;
        x = (x * x) % M;
        i += 1;
    }
    xs
}

pub const fn root_inv_pows<const M: u64>() -> [u64; 32] {
    let mut x = const { inv::<M>(find_ntt_root::<M>() as i64).rem_euclid(M as i64) as u64 };
    let mut xs = [0; 32];
    let mut i = 0;
    while i < 32 {
        xs[i] = x;
        x = (x * x) % M;
        i += 1;
    }
    xs
}

// TODO: improve NTT performance
// https://codeforces.com/blog/entry/142063

pub fn ntt<const M: u64>(a: &mut [i64]) {
    let root_pows = const { root_pows::<M>() };
    let n = a.len();
    if n <= 1 {
        return;
    }
    let mut rt = vec![0; n];
    rt[0..2].fill(1);
    let mut k = 2;
    let mut s = 2;
    while k < n {
        let x = root_pows[(M - 1).trailing_zeros() as usize - s as usize] as i64;
        let mut i = k;
        while i < k << 1 {
            rt[i] = rt[i >> 1];
            rt[i + 1] = rt[i >> 1] * x % M as i64;
            i += 2;
        }
        k <<= 1;
        s += 1;
    }
    let mut k = if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let (ij, ijk) = (i + j, i + j + k);
                let v = a[ij];
                a[ij] = (v + a[ijk]) % M as i64;
                a[ijk] = rt[j + k] * (v - a[ijk]) % M as i64;
            }
            i += k << 1;
        }
        n >> 3
    } else {
        n >> 2
    };
    while k > 0 {
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let [a_0, a_1, a_2, a_3] = unsafe {
                    a.get_disjoint_unchecked_mut([i + j, i + j + k, i + j + 2 * k, i + j + 3 * k])
                };
                let v0 = *a_0;
                *a_0 = (v0 + *a_2) % M as i64;
                *a_2 = rt[j + 2 * k] * (v0 - *a_2) % M as i64;
                let v1 = *a_1;
                *a_1 = (v1 + *a_3) % M as i64;
                *a_3 = rt[j + 3 * k] * (v1 - *a_3) % M as i64;
                let v2 = *a_0;
                *a_0 = (v2 + *a_1) % M as i64;
                *a_1 = rt[j + k] * (v2 - *a_1) % M as i64;
                let v3 = *a_2;
                *a_2 = (v3 + *a_3) % M as i64;
                *a_3 = rt[j + k] * (v3 - *a_3) % M as i64;
            }
            i += k << 2;
        }
        k >>= 2;
    }
}

pub fn intt<const M: u64>(a: &mut [i64]) {
    let root_inv_pows = const { root_inv_pows::<M>() };
    let n = a.len();
    if n <= 1 {
        return;
    }
    let mut rt = vec![0; n];
    rt[0..2].fill(1);
    let mut k = 2;
    let mut s = 2;
    while k < n {
        let x = root_inv_pows[(M - 1).trailing_zeros() as usize - s as usize] as i64;
        let mut i = k;
        while i < k << 1 {
            rt[i] = rt[i >> 1];
            rt[i + 1] = rt[i >> 1] * x % M as i64;
            i += 2;
        }
        k <<= 1;
        s += 1;
    }
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let [a_0, a_1, a_2, a_3] = unsafe {
                    a.get_disjoint_unchecked_mut([i + j, i + j + k, i + j + 2 * k, i + j + 3 * k])
                };
                let z0 = rt[j + k] * *a_1;
                let z1 = rt[j + k] * *a_3;
                let z2 = rt[j + 2 * k] * ((*a_2 + z1) % M as i64);
                let z3 = rt[j + 3 * k] * ((*a_2 - z1) % M as i64);
                *a_1 = *a_0 - z0;
                *a_0 += z0;
                *a_2 = (*a_0 - z2) % M as i64;
                *a_0 = (*a_0 + z2) % M as i64;
                *a_3 = (*a_1 - z3) % M as i64;
                *a_1 = (*a_1 + z3) % M as i64;
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
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
    }
    let n_inv = inv::<M>(n as i64);
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
