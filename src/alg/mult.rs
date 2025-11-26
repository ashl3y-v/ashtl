use crate::ds::bit_vec::BitVec;
use std::{
    collections::HashMap,
    ops::{AddAssign, Div, Mul, Sub},
};

pub fn sieve_primes(n: usize) -> (Vec<usize>, BitVec) {
    let mut is_composite = BitVec::new(n, false);
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
    let mut is_composite = BitVec::new(n, false);
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
    let mut is_composite = BitVec::new(n, false);
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
