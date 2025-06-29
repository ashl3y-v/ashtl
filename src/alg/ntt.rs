use super::{
    miller_rabin::miller_rabin,
    ops::{inverse_euclidean, mod_pow_pow_two},
    primitive_root::find_ntt_root,
};

pub fn find_ntt_prime(n: u64, b: u64) -> u64 {
    for k in (0..(b - 1) / n).rev() {
        if miller_rabin(k * n + 1) {
            return k;
        }
    }
    0
}

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
        for i in k..2 * k {
            rt[i] = if i & 1 != 0 {
                rt[i >> 1] * x % M as i64
            } else {
                rt[i >> 1]
            };
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
                a[ij] += a[ijk];
                a[ijk] = a_ij - a[ijk];
                a[ijk] *= rt[j + k];
                a[ij] %= M as i64;
                a[ijk] %= M as i64;
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
        let x = mod_pow_pow_two::<M>(
            inverse_euclidean::<M>(find_ntt_root::<M>()),
            (M - 1).trailing_zeros() as u64 - s,
        ) as i64;
        for i in k..2 * k {
            rt[i] = if i & 1 != 0 {
                rt[i >> 1] * x % M as i64
            } else {
                rt[i >> 1]
            };
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
                a[ijk] = a[ij] - z;
                a[ij] += z;
                a[ij] %= M as i64;
                a[ijk] %= M as i64;
            }
            i += k << 1;
        }
        k <<= 1;
    }
    let n_inv = inverse_euclidean::<M>(n as u64);
    a.iter_mut().for_each(|i| {
        *i *= n_inv as i64;
    });
}

pub fn ntt_conv<const M: u64>(a: &mut Vec<i64>, b: &mut Vec<i64>) {
    let deg = |a: &[i64]| {
        a.iter().rposition(|&i| i != 0).or_else(|| {
            a.first()
                .map_or(None, |&v| if v != 0 { Some(a.len()) } else { None })
        })
    };
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
    let d = a.iter().rposition(|&v| v != 0);
    if let Some(d) = d {
        let n = ((d << 1) + 1).next_power_of_two();
        a.resize(n, 0);
        ntt::<M>(a);
        a.iter_mut().for_each(|i| *i *= *i);
        intt::<M>(a);
    }
}
