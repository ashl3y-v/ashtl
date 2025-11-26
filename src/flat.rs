// SECTION: ops

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
pub fn gcd<T>(mut a: T, mut b: T) -> T
where
    T: Copy + Default + PartialEq + Rem<Output = T>,
{
    while b != T::default() {
        (a, b) = (b, a % b);
    }
    a
}

pub const fn euclidean(a: i128, b: i128) -> (i128, i128, i128) {
    let (mut r0, mut r1) = (a.abs(), b.abs());
    let (mut s0, mut s1) = (1, 0);
    let (mut t0, mut t1) = (0, 1);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    let (s0, t0) = match (a < 0, b < 0) {
        (true, true) => (-s0, -t0),
        (true, false) => (-s0, t0),
        (false, true) => (s0, -t0),
        (false, false) => (s0, t0),
    };
    (r0, s0, t0)
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

pub fn mod_fact<const M: u64>(n: u64) -> u64 {
    if n <= 1 << 19 {
        (1..=n).fold(1, |acc, x| acc * x % M)
    } else {
        Poly::<M>::factorial(n as usize).rem_euclid(M as E) as u64
    }
}

pub fn mod_rfact<const M: u64>(n: u64) -> i64 {
    inv::<M>(mod_fact::<M>(n) as i64)
}

#[derive(Clone)]
pub struct Affine<const M: u64> {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

impl<const M: u64> Affine<M> {
    pub fn new(a: u64, b: u64, c: u64) -> Self {
        Affine {
            a: a % M,
            b: b % M,
            c: c % M,
        }
    }

    pub fn pow(&self, mut n: u64) -> Self {
        let mut an = Affine::new(1, 0, self.c);
        let mut a = self.clone();
        while n != 0 {
            if n & 1 != 0 {
                an *= &a;
            }
            a *= &a.clone();
            n >>= 1;
        }
        an
    }
}

impl<const M: u64> MulAssign<&Self> for Affine<M> {
    fn mul_assign(&mut self, rhs: &Self) {
        (self.a, self.b) = (
            self.a * rhs.a % M + self.b * rhs.b % M * self.c % M,
            self.a * rhs.b % M + self.b * rhs.a % M,
        );
        self.a %= M;
        self.b %= M;
    }
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
    let d = const { mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) };
    if d > M >> 1 { M - d } else { d }
}

// SECTION: mult

pub fn sieve_primes(n: usize) -> (Vec<usize>, Vec<bool>) {
    let mut is_composite = vec![false; n];
    let mut primes = Vec::with_capacity(n / n.ilog2() as usize);
    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
        }
        for &p in &primes {
            if i * p >= n {
                break;
            }
            is_composite[i * p] = true;
            if i % p == 0 {
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
) -> (Vec<T>, Vec<bool>, Vec<usize>, Vec<u32>) {
    let mut is_composite = vec![false; n];
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
            is_composite[i * p] = true;
            if i % p == 0 {
                let p_cnt = p.pow(cnt[i]);
                if cnt[i] + 1 <= known[j] {
                    f[i * p] = on_cop_pk(&f[i / p_cnt], &f[p_cnt * p]);
                } else {
                    known[j] = cnt[i] + 1;
                    let v = on_pk(p, cnt[i] + 1, &f);
                    f[i * p] = on_cop_pk(&f[i / p_cnt], &v);
                };
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
) -> (Vec<T>, Vec<bool>, Vec<usize>) {
    let mut is_composite = vec![false; n];
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
            is_composite[i * p] = true;
            f[i * p] = on_mul(&f[i], &f[p]);
            if i % p == 0 {
                break;
            }
        }
    }
    (f, is_composite, primes)
}

pub const fn find_primitive_root<const M: u64>() -> u64 {
    if M <= 1 {
        return 0;
    }
    if M == 2 {
        return 1;
    }
    if M == 3 {
        return 2;
    }
    let phi = M - 1;
    let mut factors = [0u64; 16];
    let mut factor_count = 0;
    let mut remaining = phi;
    if remaining % 2 == 0 {
        factors[factor_count] = 2;
        factor_count += 1;
        while remaining % 2 == 0 {
            remaining /= 2;
        }
    }
    let mut factor = 3;
    while factor * factor <= remaining && factor_count < 16 {
        if remaining % factor == 0 {
            factors[factor_count] = factor;
            factor_count += 1;
            while remaining % factor == 0 {
                remaining /= factor;
            }
        }
        factor += 2;
    }
    if remaining > 1 && factor_count < 16 {
        factors[factor_count] = remaining;
        factor_count += 1;
    }
    let mut candidate = 2;
    while candidate < M {
        let mut is_primitive = true;
        let mut i = 0;
        while i < factor_count {
            let exp = phi / factors[i];
            if mod_pow::<M>(candidate, exp) == 1 {
                is_primitive = false;
                break;
            }
            i += 1;
        }
        if is_primitive {
            return candidate;
        }
        candidate += 1;
    }
    0
}

/// O(log^3 n)
/// Works up to 7 * 10^18
pub fn miller_rabin(n: u64) -> bool {
    if n < 2 || n % 6 % 4 != 1 {
        return (n | 1) == 3;
    }
    let witnesses = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
    let s = (n - 1).trailing_zeros() as u64;
    let d = n >> s;
    for a in witnesses {
        let mut p = mod_pow_non_const(a % n, d, n);
        let mut i = s;
        while p != 1 && p != n - 1 && a % n != 0 && i > 0 {
            p = p * p % n;
            i -= 1;
        }
        if p != n - 1 && i != s {
            return false;
        }
    }
    true
}

/// O(n^1/4) expected
fn pollard(n: usize) -> usize {
    let mut x = 0usize;
    let mut y = 0usize;
    let mut t = 30usize;
    let mut prd = 2usize;
    let mut i = 1usize;
    loop {
        if t % 40 != 0 || gcd(prd, n) == 1 {
            if x == y {
                i += 1;
                x = i;
                y = (x * x % n + i) % n;
            }
            let diff = if x > y { x - y } else { y - x };
            let q = prd * diff % n;
            if q != 0 {
                prd = q;
            }
            x = (x * x % n + i) % n;
            y = (((y * y % n + i) % n) * ((y * y % n + i) % n) % n + i) % n;
            t += 1;
        } else {
            break;
        }
    }
    gcd(prd, n)
}

/// O(n^1/4 log^2 n)
pub fn factor(n: usize) -> Vec<usize> {
    if n == 1 {
        return Vec::new();
    }
    if miller_rabin(n as u64) {
        return vec![n];
    }
    let x = pollard(n);
    let mut left = factor(x);
    let right = factor(n / x);
    left.extend(right);
    left
}

/// O(n^1/4 log^2 n)
pub fn factor_mult(n: usize) -> Vec<(usize, u32)> {
    let mut fs = factor(n);
    counting_sort(&mut fs, n + 1);
    let mut f = vec![(fs[0], 1)];
    let mut f_len = 1;
    let mut cp = fs[0];
    for i in 1..fs.len() {
        if fs[i] == cp {
            f[f_len - 1].1 += 1;
        } else {
            cp = fs[i];
            f.push((fs[i], 1));
            f_len += 1;
        }
    }
    f
}

/// O(n^1/4 log^2 n)
pub fn factor_dedup(n: usize) -> Vec<usize> {
    let mut fs = factor(n);
    counting_sort_dedup(&mut fs, n + 1);
    fs
}

/// O(n^1/4 log^2 n)
pub fn divisors(n: usize) -> (Vec<usize>, Vec<(usize, u32)>) {
    if n == 0 {
        return (Vec::new(), Vec::new());
    } else if n == 1 {
        return (vec![1], vec![(1, 1)]);
    }
    let prime_factors = factor_mult(n);
    let mut result = vec![1];
    for &(prime, power) in &prime_factors {
        let current_len = result.len();
        let mut prime_power = prime;
        for _ in 1..=power {
            for i in 0..current_len {
                result.push(result[i] * prime_power);
            }
            prime_power *= prime;
        }
    }
    result.sort_unstable();
    (result, prime_factors)
}

// SECTION: lattice

/// O(n log log n)
pub fn divisor<T: for<'a> AddAssign<&'a T>>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for &p in primes {
        let mut i = 1;
        let mut j = p;
        while j <= n {
            let [a_j, a_i] = unsafe { a.get_disjoint_unchecked_mut([j, i]) };
            *a_j += &*a_i;
            i += 1;
            j += p;
        }
    }
}

/// O(n log log n)
pub fn divisor_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for p in primes {
        let mut i = n / p;
        let mut j = i * p;
        while i != 0 {
            let [a_j, a_i] = unsafe { a.get_disjoint_unchecked_mut([j, i]) };
            *a_j -= &*a_i;
            i -= 1;
            j -= p;
        }
    }
}

/// O(n log n)
pub fn lcm_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
    primes: &[usize],
) {
    divisor(a, &primes);
    divisor(&mut b, &primes);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    divisor_inv(a, &primes);
}

/// O(n log log n)
pub fn multiple<T: for<'a> AddAssign<&'a T>>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for p in primes {
        let mut i = n / p;
        let mut j = i * p;
        while i != 0 {
            let [a_i, a_j] = unsafe { a.get_disjoint_unchecked_mut([i, j]) };
            *a_i += &*a_j;
            i -= 1;
            j -= p;
        }
    }
}

/// O(n log log n)
pub fn multiple_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for &p in primes {
        let mut i = 1;
        let mut j = p;
        while j <= n {
            let [a_i, a_j] = unsafe { a.get_disjoint_unchecked_mut([i, j]) };
            *a_i -= &*a_j;
            i += 1;
            j += p;
        }
    }
}

/// O(n log log n)
pub fn gcd_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
    primes: &[usize],
) {
    multiple(a, &primes);
    multiple(&mut b, &primes);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    multiple_inv(a, &primes);
}

/// O(2^n n)
pub fn subset<T: for<'a> AddAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut butter4 = |i0, i1, i2, i3| {
        let [a_0, a_1, a_2, a_3] = unsafe { a.get_disjoint_unchecked_mut([i0, i1, i2, i3]) };
        *a_1 += &*a_0;
        *a_3 += &*a_2;
        *a_2 += &*a_0;
        *a_3 += &*a_1;
    };
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                butter4(j, j + k, j + 2 * k, j + 3 * k);
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < i + k {
                let [a_0, a_1] = unsafe { a.get_disjoint_unchecked_mut([j, j + k]) };
                *a_1 += &*a_0;
                j += 1;
            }
            i += k << 1;
        }
    }
}

/// O(2^n n)
pub fn subset_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut butter4 = |i0, i1, i2, i3| {
        let [a_0, a_1, a_2, a_3] = unsafe { a.get_disjoint_unchecked_mut([i0, i1, i2, i3]) };
        *a_1 -= &*a_0;
        *a_3 -= &*a_2;
        *a_2 -= &*a_0;
        *a_3 -= &*a_1;
    };
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                butter4(j, j + k, j + 2 * k, j + 3 * k);
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < i + k {
                let [a_0, a_1] = unsafe { a.get_disjoint_unchecked_mut([j, j + k]) };
                *a_1 -= &*a_0;
                j += 1;
            }
            i += k << 1;
        }
    }
}

/// O(2^n n)
pub fn or_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
) {
    subset(a);
    subset(&mut b);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    subset_inv(a);
}

/// O(2^n n)
pub fn superset<T: for<'a> AddAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut butter4 = |i0, i1, i2, i3| {
        let [a_0, a_1, a_2, a_3] = unsafe { a.get_disjoint_unchecked_mut([i0, i1, i2, i3]) };
        *a_0 += &*a_1;
        *a_2 += &*a_3;
        *a_0 += &*a_2;
        *a_1 += &*a_3;
    };
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                butter4(j, j + k, j + 2 * k, j + 3 * k);
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < i + k {
                let [a_0, a_1] = unsafe { a.get_disjoint_unchecked_mut([j, j + k]) };
                *a_0 += &*a_1;
                j += 1;
            }
            i += k << 1;
        }
    }
}

/// O(2^n n)
pub fn superset_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut butter4 = |i0, i1, i2, i3| {
        let [a_0, a_1, a_2, a_3] = unsafe { a.get_disjoint_unchecked_mut([i0, i1, i2, i3]) };
        *a_0 -= &*a_1;
        *a_2 -= &*a_3;
        *a_0 -= &*a_2;
        *a_1 -= &*a_3;
    };
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                butter4(j, j + k, j + 2 * k, j + 3 * k);
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < i + k {
                let [a_0, a_1] = unsafe { a.get_disjoint_unchecked_mut([j, j + k]) };
                *a_0 -= &*a_1;
                j += 1;
            }
            i += k << 1;
        }
    }
}

/// O(2^n n)
pub fn and_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
) {
    superset(a);
    superset(&mut b);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    superset(a);
}

/// O(2^n n^2)
pub fn subset_conv<T>(a: &mut [T], b: &mut [T])
where
    T: Clone
        + Default
        + AddAssign<T>
        + for<'a> AddAssign<&'a T>
        + for<'a> SubAssign<&'a T>
        + for<'a> Mul<&'a T, Output = T>,
{
    let n = a.len().ilog2() as usize;
    let mut fhat = vec![vec![T::default(); 1 << n]; n + 1];
    let mut ghat = vec![vec![T::default(); 1 << n]; n + 1];
    for m in 0_usize..1 << n {
        fhat[m.count_ones() as usize][m] = a[m].clone();
        ghat[m.count_ones() as usize][m] = b[m].clone();
    }
    for i in 0..=n {
        subset(&mut fhat[i]);
        subset(&mut ghat[i]);
    }
    let mut h = vec![vec![T::default(); 1 << n]; n + 1];
    for i in 0..=n {
        for j in 0..=i {
            h[i].iter_mut()
                .zip(&fhat[j])
                .zip(&ghat[i - j])
                .for_each(|((a, b), c)| *a += b.clone() * c);
        }
    }
    for i in 0..=n {
        subset_inv(&mut h[i]);
    }
    for m in 0..1 << n {
        a[m] = h[m.count_ones() as usize][m].clone();
    }
}

/// O(2^n n)
pub fn xor<T>(a: &mut [T])
where
    T: Clone + for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T>,
{
    let n = a.len();
    let op = |a: &mut T, b: &mut T| {
        let v = b.clone();
        *b = a.clone();
        *b -= &v;
        *a += &v;
    };
    let mut butter4 = |i0, i1, i2, i3| {
        let [a_0, a_1, a_2, a_3]: [&mut T; 4] =
            unsafe { a.get_disjoint_unchecked_mut([i0, i1, i2, i3]) };
        op(a_0, a_1);
        op(a_2, a_3);
        op(a_0, a_2);
        op(a_1, a_3);
    };
    let mut k = 1;
    while k < n >> 1 {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                butter4(j, j + k, j + 2 * k, j + 3 * k);
            }
            i += k << 2;
        }
        k <<= 2;
    }
    if n.trailing_zeros() & 1 != 0 {
        let k = n >> 1;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < i + k {
                let [a_0, a_1] = unsafe { a.get_disjoint_unchecked_mut([j, j + k]) };
                op(a_0, a_1);
                j += 1;
            }
            i += k << 1;
        }
    }
}

/// O(2^n n)
pub fn xor_inv<T>(a: &mut [T])
where
    T: Clone + for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + DivAssign,
    i32: Into<T>,
{
    let n = a.len();
    xor(a);
    for x in a {
        *x /= (n as i32).into();
    }
}

/// O(2^n n)
pub fn xor_conv<T>(a: &mut [T], mut b: Vec<T>)
where
    T: Clone + for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign + DivAssign,
    i32: Into<T>,
{
    xor(a);
    xor(&mut b);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    xor_inv(a);
}

// SECTION: primitive

#[inline]
pub const fn find_ntt_root<const M: u64>() -> u64 {
    let root = find_primitive_root::<M>();
    mod_pow::<M>(root, M >> (M - 1).trailing_zeros())
}

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

// SECTION: ntt

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

// SECTION: poly

pub type E = i64;

#[derive(Clone, Default)]
pub struct Poly<const M: u64> {
    pub coeff: Vec<E>,
}

impl<const M: u64> Poly<M> {
    #[inline]
    pub fn new(coeff: Vec<E>) -> Self {
        Self { coeff }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.coeff.len()
    }

    #[inline]
    pub fn deg_or_0(&self) -> usize {
        self.coeff
            .iter()
            .rposition(|&i| i % M as E != 0)
            .unwrap_or(0)
    }

    #[inline]
    pub fn deg(&self) -> Option<usize> {
        self.coeff.iter().rposition(|&i| i % M as E != 0)
    }

    #[inline]
    pub fn resize(mut self, n: usize) -> Self {
        self.coeff.resize(n, 0);
        self
    }

    #[inline]
    pub fn push(mut self, v: E) -> Self {
        self.coeff.push(v);
        self
    }

    #[inline]
    pub fn copy(mut self, rhs: &Self) -> Self {
        self.coeff.copy_from_slice(&rhs.coeff);
        self
    }

    #[inline]
    pub fn truncate_deg(self) -> (Self, Option<usize>) {
        let d = self.deg();
        (self.mod_xn(d.map(|i| i + 1).unwrap_or(0)), d)
    }

    #[inline]
    pub fn truncate_deg_or_0(self) -> (Self, usize) {
        let d = self.deg_or_0();
        (self.mod_xn(d + 1), d)
    }

    #[inline]
    pub fn normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i %= M as E;
        });
        self
    }

    #[inline]
    pub fn pos_normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i = i.rem_euclid(M as E);
        });
        self
    }

    #[inline]
    pub fn neg_normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i = i.rem_euclid(M as E);
            if (M as E) >> 1 < *i {
                *i -= M as E;
            }
        });
        self
    }

    #[inline]
    pub fn dot(mut self, rhs: &Self) -> Self {
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .for_each(|(i, j)| *i *= j);
        self
    }

    #[inline]
    pub fn dot_n(mut self, n: usize, rhs: &Self) -> Self {
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .take(n)
            .for_each(|(i, j)| *i *= j);
        self
    }

    #[inline]
    pub fn mod_xn(mut self, n: usize) -> Self {
        self.coeff.truncate(n);
        self
    }

    #[inline]
    pub fn clone_mod_xn(&self, n: usize) -> Self {
        Self::new(self.coeff[0..n.min(self.len())].to_vec())
    }

    #[inline]
    pub fn clone_resize(&self, n: usize) -> Self {
        self.clone_mod_xn(n).resize(n)
    }

    #[inline]
    pub fn reverse(mut self) -> Self {
        self.coeff.reverse();
        self
    }

    #[inline]
    pub fn truncate_reverse(mut self) -> (Self, usize) {
        let d;
        (self, d) = self.truncate_deg_or_0();
        self.coeff.reverse();
        (self, d)
    }

    #[inline]
    pub fn reverse_n(mut self, n: usize) -> Self {
        let d = self.deg_or_0();
        for i in 0..n.min(d + 1 >> 1) {
            self.coeff.swap(i, d - i);
        }
        self.mod_xn(n)
    }

    #[inline]
    pub fn reverse_k(self, k: usize) -> Self {
        self.permute(|i| k - i, k + 1)
    }

    #[inline]
    pub fn permute(mut self, mut f: impl FnMut(usize) -> usize, n: usize) -> Self {
        let d = self.deg_or_0();
        self = self.resize(n);
        for i in 0..=d.min(n.saturating_sub(1)) {
            let f_i = f(i);
            if i < f_i {
                self.coeff.swap(i, f_i);
            }
        }
        self
    }

    #[inline]
    pub fn erase_range(mut self, range: impl RangeBounds<usize>) -> Self {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.len(),
        };
        self.coeff
            .iter_mut()
            .skip(l)
            .take(r - l)
            .for_each(|v| *v = 0);
        self
    }

    #[inline]
    pub fn fill(mut self, v: E) -> Self {
        self.coeff.fill(v);
        self
    }

    #[inline]
    pub fn ntt(mut self) -> Self {
        ntt::<M>(&mut self.coeff);
        self
    }

    #[inline]
    pub fn intt(mut self) -> Self {
        intt::<M>(&mut self.coeff);
        self
    }

    #[inline]
    pub fn ntt_t(mut self) -> Self {
        self = self.intt();
        self.coeff[1..].reverse();
        let n = self.len();
        self * n as E
    }

    #[inline]
    pub fn intt_t(mut self) -> Self {
        self.coeff[1..].reverse();
        self = self.ntt();
        let n = self.len();
        self / n as E
    }

    /// O(n log n)
    #[inline]
    pub fn mul_t(mut self, mut rhs: Self) -> Self {
        let (m, k) = (self.len(), rhs.len());
        let n = m.next_power_of_two();
        (self, rhs) = (self.resize(n).intt_t().normalize(), rhs.resize(n).ntt());
        self.dot(&rhs).ntt_t().resize(m - k + 1).normalize()
    }

    #[inline]
    pub fn mul_t_ntt(mut self, rhs: &Self) -> Self {
        let n = self.len().next_power_of_two();
        self = self.resize(n).intt_t().normalize();
        self.dot(rhs).ntt_t().normalize()
    }

    /// O(n log n)
    #[inline]
    pub fn extend_ntt(mut self, a: Self) -> Self {
        let root_pows = const { root_pows::<M>() };
        let x = root_pows
            [(M - 1).trailing_zeros() as usize - (self.coeff.len().trailing_zeros() + 1) as usize]
            as E;
        self.coeff
            .extend(a.mulx(x).resize(self.coeff.len()).ntt().coeff);
        self
    }

    /// O(n log n)
    #[inline]
    pub fn double_ntt(self) -> Self {
        let a = self.clone().intt().normalize();
        self.extend_ntt(a)
    }

    /// O(n log n)
    #[inline]
    pub fn ntt_double(self) -> Self {
        let a = self.clone();
        self.ntt().extend_ntt(a)
    }

    /// O(n log n)
    #[inline]
    pub fn bisect_ntt(&self) -> (Self, Self) {
        let n = self.len() >> 1;
        let mut p0 = Vec::with_capacity(n);
        let mut p1 = Vec::with_capacity(n);
        let half = inv::<M>(2);
        self.coeff.chunks_exact(2).for_each(|chunk| {
            let [a, b] = chunk else {
                panic!("irrefutable pattern not matched")
            };
            p0.push((a + b) * half % M as E);
            p1.push((a - b) as E * half % M as E);
        });
        p0.resize(n, 0);
        p1.resize(n, 0);
        let mut z = 1;
        let root_inv_pows = const { root_inv_pows::<M>() };
        let dz = root_inv_pows[(M - 1).trailing_zeros() as usize - n.trailing_zeros() as usize - 1];
        let mut btr = vec![0; n];
        let log = n.ilog2();
        for i in 0..n {
            let j = (btr[i >> 1] >> 1) + ((i & 1) << (log - 1));
            btr[i] = j;
            p1[j] = (p1[j] * z as E) % M as E;
            z = (z * dz) % M;
        }
        (Self::new(p0), Self::new(p1))
    }

    /// O(n)
    pub fn root_inv_pows_bit_reverse(n: usize) -> Self {
        if n == 0 {
            return Self::new(vec![]);
        } else if n == 1 {
            return Self::new(vec![1]);
        }
        let mut v = vec![0; n];
        let mut z = 1;
        let root_inv_pows = const { root_inv_pows::<M>() };
        let dz = root_inv_pows[(M - 1).trailing_zeros() as usize - n.trailing_zeros() as usize - 1];
        let mut btr = vec![0; n];
        let log = n.ilog2();
        for i in 0..n {
            let j = (btr[i >> 1] >> 1) + ((i & 1) << (log - 1));
            btr[i] = j;
            v[j] = z as E;
            z = (z * dz) % M;
        }
        Self::new(v)
    }

    #[inline]
    pub fn sub_xk(mut self, k: usize) -> Self {
        if k == 1 {
            return self;
        }
        let d = self.deg_or_0();
        self.coeff.resize(k * (d + 1), 0);
        for i in (1..=d).rev() {
            self.coeff[k * i] = self.coeff[i];
            for j in k * (i - 1) + 1..k * i {
                self.coeff[j] = 0;
            }
        }
        self
    }

    #[inline]
    pub fn sub_xk_n(mut self, k: usize, n: usize) -> Self {
        if k == 1 {
            return self.mod_xn(n);
        }
        let d = self.deg_or_0();
        self.coeff.resize(n, 0);
        for i in (1..=d.min((n - 1) / k)).rev() {
            self.coeff[k * i] = self.coeff[i];
            for j in k * (i - 1) + 1..k * i {
                self.coeff[j] = 0;
            }
        }
        self
    }

    /// O(n log n)
    pub fn inv(&self, n: usize) -> Option<Self> {
        let a0 = self.coeff.get(0).copied().unwrap_or(0);
        if a0 == 0 {
            return None;
        } else if n <= 1 << 9 {
            return Some(self.clone_mod_xn(n).inv_pow(1, n)?);
        }
        let a0_inv = inv::<M>(a0);
        let mut r = Self::new(vec![-a0_inv as E]).resize(n.next_power_of_two());
        let mut k = 1;
        while k < n {
            let g = r.clone_resize(k).ntt_double();
            let f = (self.clone_resize(k << 1).ntt().dot(&g).intt() >> k)
                .normalize()
                .ntt_double()
                .dot(&g)
                .intt()
                .resize(k);
            r.coeff[k..k << 1]
                .iter_mut()
                .zip(f.coeff)
                .for_each(|(i, j)| *i = j % M as E);
            k <<= 1;
        }
        Some(-r)
    }

    /// O(n log n)
    pub fn inv_semicorr(mut self, n: usize) -> Option<Self> {
        let d;
        (self, d) = self.truncate_reverse();
        Some(self.inv(n)? << d)
    }

    /// O(n log n)
    pub fn dir_inv(&self, n: usize) -> Option<Self> {
        if self.coeff[1] % M as E == 0 {
            return None;
        }
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let f1 = self.coeff[1];
        let f1_inv = inv::<M>(f1);
        let mut p = vec![0; n];
        p[1] = inv::<M>(f1);
        for i in 2..n.min(m) {
            p[i] = -p[1] * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            p[i] = p[i] * f1_inv % M as E * big_omega_invs[i - 2] % M as E;
            let v = p[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * (big_omega[j / i] * -p[i] % M as E - v) % M as E;
            }
        }
        Some(Self::new(p))
    }

    #[inline]
    pub fn eval(&self, x: E) -> E {
        let mut res = 0;
        for i in (0..=self.deg_or_0()).rev() {
            res *= x;
            res += self.coeff[i];
            res %= M as E;
        }
        res
    }

    #[inline]
    pub fn eval_fall(&self, x: E) -> E {
        let mut res = 0;
        for i in (0..=self.deg_or_0()).rev() {
            res *= x - i as E;
            res += self.coeff[i];
            res %= M as E;
        }
        res
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        !self.coeff.iter().any(|&i| i % M as E != 0)
    }

    #[inline]
    pub fn diff_x(mut self) -> Self {
        self.coeff
            .iter_mut()
            .enumerate()
            .for_each(|(i, v)| *v = (*v * i as E) % M as E);
        self
    }

    /// O(n)
    #[inline]
    pub fn dir_diff(mut self) -> Self {
        let n = self.len();
        self.coeff
            .iter_mut()
            .zip(sieve_complete(n, 0, |a, b| a + b, |_, _| 1).0)
            .for_each(|(i, j)| *i = (*i * j as E) % M as E);
        self
    }

    #[inline]
    pub fn integr_divx(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        self.coeff
            .iter_mut()
            .zip(inverses_n_div::<M>(d + 1))
            .for_each(|(v, inv)| *v = (*v * inv as E) % M as E);
        self
    }

    /// O(n)
    #[inline]
    pub fn dir_integr(mut self) -> Self {
        let n = self.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        (self.coeff[0], self.coeff[1]) = (0, 0);
        self.coeff
            .iter_mut()
            .skip(2)
            .zip(inverses::<M, _>(&big_omega[2..]))
            .for_each(|(i, j)| *i = (*i * j as E) % M as E);
        self
    }

    #[inline]
    pub fn trailing_xk_or_0(&self) -> usize {
        self.coeff
            .iter()
            .position(|&i| i % M as E != 0)
            .unwrap_or(0)
    }

    /// O(n log n)
    #[inline]
    pub fn log(mut self, n: usize) -> Option<Self> {
        self.coeff[0] = self.coeff[0].rem_euclid(M as E);
        let v = self.inv(n)?;
        Some(
            (self.mod_xn(n).diff_x() * v.normalize())
                .mod_xn(n)
                .integr_divx(),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn dir_log(mut self, n: usize) -> Option<Self> {
        if self.coeff[1] % M as E == 0 {
            return None;
        }
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let f1 = self.coeff[1];
        self = (self / f1).normalize();
        let mut p = vec![0; n];
        p[1] = 0;
        for i in 2..n.min(m) {
            p[i] = (self.coeff[i] - p[i] * big_omega_invs[i - 2] % M as E) % M as E;
            let v = p[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * v % M as E;
            }
        }
        for i in n.min(m)..n {
            p[i] = -p[i] * big_omega_invs[i - 2] % M as E;
            let v = p[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * v % M as E;
            }
        }
        Some(Self::new(p))
    }

    /// O(n log n)
    pub fn exp(&self, n: usize) -> Option<Self> {
        if self.coeff.get(0).copied().unwrap_or(0) % M as E != 0 {
            return None;
        } else if self.len() <= 1 {
            return Some(Self::new(vec![1]));
        } else if self.deg_or_0().min(n) <= 1 << 7 {
            let m = self.len();
            let invs = inverses_n_div::<M>(n);
            let mut e = Self::new(vec![1]);
            for i in 1..n {
                let mut s = 0;
                for j in 1..=i.min(m - 1).min(n - 1) {
                    s += j as E * self.coeff[j] % M as E * e[i - j] % M as E;
                }
                e.coeff.push(s % M as E * invs[i] as E % M as E);
            }
            return Some(e);
        }
        let n = n.next_power_of_two();
        let mut e_k = Self::new(Vec::with_capacity(n)).push(1).push(self.coeff[1]);
        let mut e_k_inv = Self::new(Vec::with_capacity(n)).push(1);
        let mut e_k_ntt = Self::new(Vec::with_capacity(n)).resize(2);
        let mut e_k_inv_ntt = Self::new(Vec::with_capacity(n)).push(1).push(1);
        let mut i = 1;
        while i < n >> 1 {
            e_k_ntt = e_k_ntt.copy(&e_k).ntt_double();
            let eps = e_k_inv_ntt
                .clone()
                .dot_n(i << 1, &e_k_ntt)
                .intt()
                .erase_range(0..i)
                .normalize()
                .ntt()
                .dot(&e_k_inv_ntt)
                .intt();
            e_k_inv = e_k_inv.resize(i << 1);
            for i in i..i << 1 {
                e_k_inv[i] = -eps[i] % M as E;
            }
            e_k_inv_ntt = e_k_inv_ntt.resize(i << 1).copy(&e_k_inv).ntt_double();
            let mut e_d = ((self
                .clone_resize(i << 1)
                .diff_x()
                .ntt_double()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1))
                .ntt_double()
                .dot(&e_k_inv_ntt)
                .intt()
                .normalize()
                << (i << 1))
                .resize(i << 2)
                .integr_divx()
                .resize(i << 2);
            for i in i << 1..(i << 2).min(self.len()) {
                e_d[i] += self.coeff[i];
            }
            e_d = (e_d >> (i << 1))
                .normalize()
                .ntt_double()
                .dot(&e_k_ntt)
                .intt();
            e_k = e_k.resize(i << 2);
            let e_k_upd = &mut e_k.coeff[i << 1..];
            for j in 0..i << 1 {
                e_k_upd[j] = e_d[j] % M as E;
            }
            i <<= 1;
        }
        Some(e_k)
    }

    /// O(n log n)
    pub fn exp_and_inv(&self, n: usize) -> Option<(Self, Self)> {
        if self.coeff.get(0).copied().unwrap_or(0) % M as E != 0 {
            return None;
        } else if self.len() <= 1 {
            return Some((Self::new(vec![1]), Self::new(vec![1])));
        } else if self.deg_or_0().min(n) <= 1 << 6 {
            let m = self.len();
            let invs = inverses_n_div::<M>(n);
            let mut e = Self::new(vec![1]);
            for i in 1..n {
                let mut s0 = 0;
                for j in 1..=i.min(m - 1) {
                    s0 += j as E * self.coeff[j] % M as E * e[i - j] % M as E;
                }
                e.coeff.push(s0 % M as E * invs[i] as E % M as E);
            }
            let e_inv = e.inv(n)?;
            return Some((e, e_inv));
        }
        let n = n.next_power_of_two();
        let mut e_k = Self::new(Vec::with_capacity(n)).push(1).push(self.coeff[1]);
        let mut e_k_inv = Self::new(Vec::with_capacity(n)).push(1);
        let mut e_k_ntt = Self::new(Vec::with_capacity(n)).resize(2);
        let mut e_k_inv_ntt = Self::new(Vec::with_capacity(n)).push(1).push(1);
        let mut i = 1;
        loop {
            e_k_ntt = e_k_ntt.copy(&e_k).ntt_double();
            let eps = e_k_inv_ntt
                .clone()
                .dot_n(i << 1, &e_k_ntt)
                .intt()
                .erase_range(0..i)
                .normalize()
                .ntt()
                .dot(&e_k_inv_ntt)
                .intt();
            e_k_inv = e_k_inv.resize(i << 1);
            for i in i..i << 1 {
                e_k_inv[i] = -eps[i] % M as E;
            }
            if i >= n >> 1 {
                break Some((e_k, e_k_inv));
            }
            e_k_inv_ntt = e_k_inv_ntt.copy(&e_k_inv).ntt_double();
            let mut e_d = ((self
                .clone_resize(i << 1)
                .diff_x()
                .ntt_double()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1))
                .ntt_double()
                .dot(&e_k_inv_ntt)
                .intt()
                .normalize()
                << (i << 1))
                .resize(i << 2)
                .integr_divx()
                .resize(i << 2);
            for i in i << 1..(i << 2).min(self.len()) {
                e_d[i] += self.coeff[i];
            }
            e_d = (e_d >> (i << 1))
                .normalize()
                .ntt_double()
                .dot(&e_k_ntt)
                .intt();
            e_k = e_k.resize(i << 2);
            let e_k_upd = &mut e_k.coeff[i << 1..];
            for j in 0..i << 1 {
                e_k_upd[j] = e_d[j] % M as E;
            }
            i <<= 1;
        }
    }

    /// O(n log n)
    pub fn dir_exp(&self, n: usize) -> Option<Self> {
        let m = self.coeff.len();
        if self.coeff[1] % M as E != 0 {
            return None;
        }
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let mut p = vec![0; n];
        p[1] = 1;
        for i in 2..n.min(m) {
            p[i] = p[1] * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            p[i] = p[i] * big_omega_invs[i - 2] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += p[i] * self.coeff[j / i] % M as E * big_omega[j / i] % M as E;
            }
        }
        Some(Self::new(p))
    }

    /// O(n log n)
    #[inline]
    pub fn sinh(&self, n: usize) -> Option<Self> {
        let (e0, e1) = self.exp_and_inv(n)?;
        Some((e0 - e1) / 2)
    }

    /// O(n log n)
    #[inline]
    pub fn asinh(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        ((p.clone().square() + 1).sqrt(n)? + p).log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn cosh(&self, n: usize) -> Option<Self> {
        let (e0, e1) = self.exp_and_inv(n)?;
        Some((e0 + e1) / 2)
    }

    /// O(n log n)
    #[inline]
    pub fn acosh(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        ((self.clone_mod_xn(n).square() - 1).sqrt(n)? + p).log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn tanh(&self, n: usize) -> Option<Self> {
        let e = (self.clone_mod_xn(n) * 2).exp(n)? + 1;
        let ep1_inv = e.inv(n)?.normalize();
        Some((e - 2) * ep1_inv)
    }

    /// O(n log n)
    #[inline]
    pub fn atanh(&self, n: usize) -> Option<Self> {
        let p = -self.clone_mod_xn(n) + 1;
        let np_p1_inv = p.inv(n)?;
        Some(((-p + 2) * np_p1_inv).log(n)?.normalize() / 2)
    }

    /// O(n log n)
    #[inline]
    pub fn csch_x(&self, n: usize) -> Option<Self> {
        let (e0, e1) = self.exp_and_inv(n)?;
        Some(((e0 - e1) >> 1).inv(n)? * 2)
    }

    /// O(n log n)
    #[inline]
    pub fn acsch_divx(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        let q = p.inv(n)?.normalize();
        p = p.square();
        p.coeff[2] += 1;
        p = -p.sqrt(n)?;
        p.coeff[1] += 1;
        (p.normalize() * q).log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn sech(&self, n: usize) -> Option<Self> {
        let (e0, e1) = self.exp_and_inv(n)?;
        Some((e0 + e1).inv(n)? * 2)
    }

    /// O(n log n)
    #[inline]
    pub fn asech(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        let q = p.inv(n)?;
        (((-p.square() + 1).sqrt(n)? + 1).normalize() * q).log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn coth_x(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n) * 2;
        let e = p.exp(n)?;
        Some((p.resize(e.len()).copy(&e) + 1) * ((e - 1) >> 1).inv(n)?.normalize())
    }

    /// O(n log n)
    #[inline]
    pub fn acoth_divx(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        p.coeff[1] -= 1;
        let q = p.inv(n)?.normalize();
        p.coeff[1] += 2;
        (-(p * q).sqrt(n)?).log(n)
    }

    /// O(n log n)
    pub fn sin(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let (e0, e1) = (self.clone_mod_xn(n) * d).exp_and_inv(n)?;
        Some((e0 - e1) / (2 * d))
    }

    /// O(n log n)
    #[inline]
    pub fn asin(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let p = self.clone_mod_xn(n);
        Some(
            ((-p.clone().square() + 1).sqrt(n)? + p * d)
                .normalize()
                .log(n)?
                .normalize()
                * -d,
        )
    }

    /// O(n log n)
    pub fn cos(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        (self.clone_mod_xn(n) * d).cosh(n)
    }

    /// O(n log n)
    #[inline]
    pub fn acos(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let p = self.clone_mod_xn(n);
        Some(
            (p.clone() - (p.square() - 1).sqrt(n)?)
                .normalize()
                .log(n)?
                .normalize()
                * -d,
        )
    }

    /// O(n log n)
    pub fn sin_cos(&self, n: usize) -> Option<(Self, Self)> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let (e0, e1) = (self.clone_mod_xn(n) * d).exp_and_inv(n)?;
        Some(((e0.clone() - e1.clone()) / (2 * d), (e0 + e1) / 2))
    }

    /// O(n log n)
    pub fn tan(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let e = (self.clone_mod_xn(n) * (2 * d % M as E)).exp(n)? + 1;
        let ep1_inv = e.inv(n)?;
        Some(((e - 2) * ep1_inv.normalize()) / d)
    }

    /// O(n log n)
    #[inline]
    pub fn atan(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        Some(
            ((p.clone().square() + 1).inv(n)? * p.diff_x())
                .mod_xn(n)
                .integr_divx(),
        )
    }

    /// O(n log n)
    pub fn csc_x(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let (e0, e1) = (self.clone_mod_xn(n) * d).exp_and_inv(n)?;
        Some((((e0 - e1) >> 1).inv(n)? * 2).normalize() * d)
    }

    /// O(n log n)
    #[inline]
    pub fn acsc_divx(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let mut p = (self.clone_mod_xn(n) * -d).normalize();
        let q = p.inv(n)?.normalize();
        p = p.square();
        p.coeff[2] += 1;
        p = -p.sqrt(n)?;
        p.coeff[1] += 1;
        Some((p.normalize() * q).log(n)?.normalize() * d)
    }

    /// O(n log n)
    #[inline]
    pub fn sec(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let (e0, e1) = (self.clone_mod_xn(n) * d).normalize().exp_and_inv(n)?;
        Some((e0 + e1).inv(n)? * 2)
    }

    /// O(n log n)
    #[inline]
    pub fn asec(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let p = self.clone_mod_xn(n);
        let q = p.inv(n)?;
        Some(
            (((-p.square() + 1).sqrt(n)? + 1).normalize() * q)
                .log(n)?
                .normalize()
                * d,
        )
    }

    /// O(n log n)
    #[inline]
    pub fn cot_x(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let p = (self.clone_mod_xn(n) * (2 * d)).normalize();
        let e = p.exp(n)?.normalize();
        Some((p.resize(e.len()).copy(&e) + 1) * ((e - 1) >> 1).inv(n)?.normalize() * d)
    }

    /// O(n log n)
    #[inline]
    pub fn acot_divx(&self, n: usize) -> Option<Self> {
        let d = const { mod_sqrt_n1::<M>() as E };
        let mut p = (self.clone_mod_xn(n) * -d).normalize();
        p.coeff[1] -= 1;
        let q = p.inv(n)?.normalize();
        p.coeff[1] += 2;
        Some((-(p * q).sqrt(n)?).log(n)?.normalize() * -d)
    }

    /// O(n log n)
    #[inline]
    pub fn square(mut self) -> Self {
        ntt_conv_self::<M>(&mut self.coeff);
        self.normalize()
    }

    /// O(n log n)
    #[inline]
    pub fn inv_square_n(&self, n: usize) -> Option<Self> {
        if n < 1 << 8 {
            self.clone_mod_xn(n).inv_pow(2, n)
        } else {
            self.inv(n).map(|p| p.normalize().square().mod_xn(n))
        }
    }

    #[inline]
    pub fn dot_self(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| *i *= *i);
        self
    }

    /// O(n)
    #[inline]
    pub fn ntt_mul_neg_self_even(&self) -> Self {
        Self::new(
            self.coeff
                .chunks_exact(2)
                .map(|chunk| {
                    let [a, b] = chunk else {
                        panic!("irrefutable pattern not matched")
                    };
                    *a * *b
                })
                .collect::<Vec<_>>(),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn mul_even(mut self, mut rhs: Self) -> Self {
        let (d0, d1);
        (self, d0) = self.truncate_deg_or_0();
        (rhs, d1) = rhs.truncate_deg_or_0();
        let n = (d0 + d1 + 1).next_power_of_two();
        self.resize(n)
            .ntt()
            .ntt_mul_even(&rhs.resize(n).ntt())
            .intt()
            .normalize()
    }

    /// O(n)
    #[inline]
    pub fn ntt_mul_even(&self, rhs: &Self) -> Self {
        let half = inv::<M>(2);
        Self::new(
            self.coeff
                .chunks_exact(2)
                .zip(rhs.coeff.chunks_exact(2))
                .map(|chunk| {
                    let ([a, b], [c, d]) = chunk else {
                        panic!("irrefutable pattern not matched")
                    };
                    (a * c % M as E + b * d % M as E) * half % M as E
                })
                .collect::<Vec<_>>(),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn mul_odd(self, rhs: Self) -> Self {
        if self.len() <= rhs.len() {
            (self << 1).mul_even(rhs) >> 1
        } else {
            self.mul_even(rhs << 1) >> 1
        }
    }

    /// O(n)
    #[inline]
    pub fn ntt_mul_odd(&self, rhs: &Self) -> Self {
        let half = inv::<M>(2);
        Self::new(
            self.coeff
                .chunks_exact(2)
                .zip(rhs.coeff.chunks_exact(2))
                .zip(Self::root_inv_pows_bit_reverse(self.coeff.len() >> 1).coeff)
                .map(|chunk| {
                    let (([a, b], [c, d]), v) = chunk else {
                        panic!("irrefutable pattern not matched")
                    };
                    (a * c % M as E - b * d % M as E) * v % M as E * half % M as E
                })
                .collect::<Vec<_>>(),
        )
    }

    /// O(n log n)
    pub fn pow(mut self, mut k: usize, n: usize) -> Self {
        let i = self.trailing_xk_or_0();
        if i != 0 {
            return if k >= (n + i - 1) / i {
                Self::new(vec![])
            } else {
                let mut s = self.clone();
                s >>= i;
                let mut p = s.pow(k, n - i * k);
                p <<= i * k;
                p
            };
        }
        let l = self.deg_or_0().min(n);
        if k <= 1 << 9 && l >= 1 << 9 {
            let mut d = ((self.deg_or_0() << 1) + 1)
                .min((n << 1) + 1)
                .next_power_of_two();
            let mut ak = Self::new(vec![1]);
            while k != 0 {
                self = self.resize(d).ntt();
                if k & 1 != 0 {
                    ak = ak.resize(d).ntt().dot(&self).intt().mod_xn(n).normalize();
                }
                self = self.dot_self().intt().mod_xn(n).normalize();
                d = ((d << 1).min((n << 1) - 1)).next_power_of_two();
                k >>= 1;
            }
            ak
        } else if l <= 1 << 9 {
            let mut q = Self::new(vec![mod_pow_signed::<M>(self.coeff[0], k as u64)]);
            let d = self.deg_or_0();
            let mut k = k as E;
            if (M as E) >> 1 < k as E {
                k -= M as E;
            }
            let a0_inv = inv::<M>(self.coeff[0]);
            let invs = inverses_n_div::<M>(n);
            for i in 1..n {
                let mut s = 0;
                for j in 1..=d.min(i) {
                    s += (self.coeff[j] % M as E * (q[i - j] % M as E)) % M as E
                        * (k * j as E % M as E - (i - j) as E)
                        % M as E;
                }
                q.coeff
                    .push(s % M as E * invs[i] as E % M as E * a0_inv as E % M as E);
            }
            q
        } else {
            let mut k = k as E;
            let mut a0k = mod_pow_signed::<M>(self.coeff[i], k as u64);
            if (M as E) >> 1 < k {
                k -= M as E;
            }
            if (M as E) >> 1 < a0k {
                a0k -= M as E;
            }
            (self.log(n).unwrap().normalize() * k)
                .normalize()
                .exp(n)
                .unwrap()
                .mod_xn(n)
                * a0k
        }
    }

    /// O(n log n) if self.coeff\[1\] != 0
    /// O(n log n log k) = O(n log n log log n) else
    pub fn dir_pow(&self, mut k: usize, n: usize) -> Self {
        let f1 = self.coeff[1] % M as E;
        if f1 != 0 {
            let m = self.coeff.len();
            let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
            let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
            let f1_inv = inv::<M>(f1);
            let mut p = vec![0; n];
            p[1] = mod_pow_signed::<M>(f1, k as u64);
            let mut k = (k as E).rem_euclid(M as E);
            if (M as E) >> 1 < k {
                k -= M as E;
            }
            let v = k * p[1] % M as E;
            for i in 2..n.min(m) {
                p[i] = v * self.coeff[i] % M as E * big_omega[i] % M as E;
            }
            for i in 2..n {
                p[i] = p[i] * f1_inv % M as E * big_omega_invs[i - 2] % M as E;
                let v = p[i] * big_omega[i] % M as E;
                let w = k * p[i] % M as E;
                for j in (i << 1..n.min(i * m)).step_by(i) {
                    p[j] += self.coeff[j / i] * (big_omega[j / i] * w % M as E - v) % M as E;
                }
            }
            Self::new(p)
        } else {
            if k > (n - 1).ilog2() as usize {
                return Self::new(vec![0; 2]);
            }
            let mut s = self.clone_mod_xn(n);
            let mut ak = Self::new(vec![0, 1]);
            while k != 0 {
                if k & 1 != 0 {
                    ak = ak.dir_mul(&s, n);
                }
                s = s.dir_mul(&s, n);
                k >>= 1;
            }
            ak
        }
    }

    /// O(n log n)
    pub fn inv_pow(self, k: usize, n: usize) -> Option<Self> {
        let k = k % M as usize;
        let a0 = self.coeff.get(0).copied().unwrap_or(0);
        if a0 == 0 {
            return None;
        }
        let a0_inv = inv::<M>(a0);
        Some(
            (self * a0_inv).pow(M as usize - k, n).normalize()
                * mod_pow_signed::<M>(a0_inv, k as u64),
        )
    }

    /// O(n log n)
    pub fn sqrt(&self, n: usize) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::new(vec![]));
        }
        let i = self.trailing_xk_or_0();
        if i != 0 && i & 1 != 0 {
            return None;
        } else if i != 0 {
            let ans = (self.clone_mod_xn(n + (i >> 1)) >> i).sqrt(n - (i >> 1));
            return if let Some(mut ans) = ans {
                ans <<= i >> 1;
                Some(ans)
            } else {
                ans
            };
        }
        let st = mod_sqrt::<M>(self.coeff[0].rem_euclid(M as E) as u64)? as E;
        if self.deg_or_0().min(n) <= 1 << 9 {
            return Some(
                (self.clone() / self.coeff[0])
                    .normalize()
                    .pow(inv::<M>(2).rem_euclid(M as E) as usize, n)
                    .normalize()
                    * st,
            );
        }
        let half = inv::<M>(2);
        let st_inv = inv::<M>(st);
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::new(vec![st as E]),
            Self::new(vec![st_inv as E]),
            Self::new(vec![st as E]),
            Self::new(Vec::new()),
            Self::new(Vec::new()),
        );
        let mut k = 1;
        let freq = |i| {
            if i < self.coeff.len() {
                self.coeff[i]
            } else {
                0
            }
        };
        while k < n {
            z = z.dot_self().intt();
            delta = delta.fill(0).resize(k << 1);
            for i in 0..k {
                delta[k + i] = (z[i] - freq(i) - freq(k + i)) % M as E;
            }
            delta = delta.ntt();
            gbuf = gbuf.fill(0).resize(k);
            for i in 0..k {
                gbuf[i] = g[i];
            }
            gbuf = gbuf.ntt_double();
            delta
                .coeff
                .iter_mut()
                .zip(&gbuf.coeff)
                .for_each(|(i, j)| *i *= j);
            delta = delta.intt().normalize();
            f = f.resize(k << 1);
            for i in k..k << 1 {
                f[i] = (-half * delta[i]) % M as E;
            }
            if k << 1 >= n {
                break;
            }
            z = f.clone().ntt();
            let eps = (gbuf.clone().dot(&z).intt() >> k)
                .normalize()
                .ntt_double()
                .dot(&gbuf)
                .intt();
            g = g.resize(k << 1);
            g.coeff[k..k << 1]
                .iter_mut()
                .zip(eps.coeff)
                .for_each(|(i, j)| *i = -j % M as E);
            k <<= 1;
        }
        Some(f)
    }

    /// O(n log n)
    pub fn inv_sqrt(&self, n: usize) -> Option<Self> {
        if *self.coeff.get(0).unwrap_or(&0) == 0 {
            return None;
        }
        let st = inv::<M>(mod_sqrt::<M>(self.coeff[0].rem_euclid(M as E) as u64)? as E);
        if self.deg_or_0().min(n) <= 1 << 9 {
            return Some(
                (self.clone() / self.coeff[0])
                    .normalize()
                    .pow(M as usize - inv::<M>(2).rem_euclid(M as E) as usize, n)
                    .normalize()
                    * st,
            );
        }
        let half = inv::<M>(2);
        let mut g = Self::new(vec![st as E]);
        let mut k = 1;
        while k < n {
            let g_ntt = g.clone().ntt_double();
            let mut f = g_ntt.clone().dot_self().intt().normalize();
            f = (f.mod_xn(k << 1) * self.clone_mod_xn(k << 1)).mod_xn(k << 1);
            f >>= k;
            f = f.ntt_double().dot(&g_ntt).intt();
            g = g.resize(k << 1);
            g.coeff[k..k << 1]
                .iter_mut()
                .zip(f.coeff)
                .for_each(|(i, j)| *i = -j % M as E * half % M as E);
            k <<= 1;
        }
        Some(g)
    }

    /// O(n log n)
    pub fn sqrt_and_inv(&self, n: usize) -> Option<(Self, Option<Self>)> {
        if self.is_zero() {
            return Some((Self::new(vec![]), None));
        }
        let i = self.trailing_xk_or_0();
        if i != 0 && i & 1 == 0 {
            return None;
        } else if i != 0 {
            let ans = (self.clone_mod_xn(n + (i >> 1)) >> i).sqrt(n - (i >> 1));
            return if let Some(mut ans) = ans {
                ans <<= i >> 1;
                Some((ans, None))
            } else {
                None
            };
        }
        let half = inv::<M>(2);
        let st = mod_sqrt::<M>(self.coeff[0].rem_euclid(M as E) as u64)?;
        let st_inv = inv::<M>(st as E);
        if self.deg_or_0().min(n) <= 1 << 9 {
            let s = (self.clone() / self.coeff[0]).normalize();
            return Some((
                s.clone()
                    .pow(inv::<M>(2).rem_euclid(M as E) as usize, n)
                    .normalize()
                    * st as E,
                Some(
                    s.pow(M as usize - inv::<M>(2).rem_euclid(M as E) as usize, n)
                        .normalize()
                        * st_inv as E,
                ),
            ));
        }
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::new(vec![st as E]),
            Self::new(vec![st_inv as E]),
            Self::new(vec![st as E]),
            Self::new(Vec::new()),
            Self::new(Vec::new()),
        );
        let mut k = 1;
        let freq = |i| {
            if i < self.coeff.len() {
                self.coeff[i]
            } else {
                0
            }
        };
        while k < n {
            for i in 0..k {
                z[i] *= z[i];
            }
            z = z.intt();
            delta = delta.fill(0).resize(k << 1);
            for i in 0..k {
                delta[k + i] = (z[i] - freq(i) - freq(k + i)) % M as E;
            }
            delta = delta.ntt();
            gbuf = gbuf.fill(0).resize(k << 1);
            for i in 0..k {
                gbuf[i] = g[i];
            }
            gbuf = gbuf.ntt();
            delta
                .coeff
                .iter_mut()
                .zip(&gbuf.coeff)
                .for_each(|(i, j)| *i *= j);
            delta = delta.intt().normalize();
            f = f.resize(k << 1);
            for i in k..k << 1 {
                f[i] = (-half * delta[i]) % M as E;
            }
            z = f.clone().ntt();
            let eps = (gbuf.clone().dot(&z).intt() >> k)
                .normalize()
                .ntt_double()
                .dot(&gbuf)
                .intt();
            g = g.resize(k << 1);
            g.coeff[k..k << 1]
                .iter_mut()
                .zip(eps.coeff)
                .for_each(|(i, j)| *i = -j % M as E);
            k <<= 1;
        }
        Some((f, Some(g)))
    }

    // constant term must be 1
    /// O(n log n)
    pub fn dir_k_rt(&self, k: usize, n: usize) -> Option<Self> {
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let mut f = vec![0; n];
        let g1 = self.coeff[1];
        let g1_inv = inv::<M>(g1);
        let k_inv = inv::<M>(k as E);
        f[1] = 1;
        let v = k_inv as E * f[1] % M as E;
        for i in 2..n.min(m) {
            f[i] = v * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            f[i] = f[i] * g1_inv % M as E * big_omega_invs[i - 2] % M as E;
            let v = f[i] * big_omega[i] % M as E;
            let w = f[i] * k_inv as E % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                f[j] += self.coeff[j / i] * (w * big_omega[j / i] % M as E - v) % M as E;
            }
        }
        Some(Self::new(f))
    }

    /// O(n log n)
    pub fn div_mod_ri(&self, q: &Self, qri: &Self) -> (Self, Self) {
        const MAGIC: E = 1 << 9;
        let q_d = q.deg_or_0();
        let d = self.deg_or_0() as E - q_d as E;
        if d.min(q_d as E) <= MAGIC {
            return self.div_mod_small(q);
        }
        let mut quotient = Self::new(vec![0]);
        if d >= 0 {
            let d_usize = d as usize;
            let product = (self.clone().reverse_n(d_usize + 1).mod_xn(d_usize + 1)
                * qri.clone_mod_xn(d_usize + 1))
            .mod_xn(d_usize + 1);
            quotient = product.reverse_n(d_usize + 1);
        }
        let remainder = -quotient.clone() * q + self;
        (quotient, remainder)
    }

    /// O(n log n)
    pub fn div_mod(&self, q: &Self) -> (Self, Self) {
        let d = self.deg_or_0() as i32 - q.deg_or_0() as i32;
        if d.min(q.deg_or_0() as i32) <= 1 << 9 {
            return self.div_mod_small(q);
        } else {
            let q_rev = q.clone().truncate_reverse().0;
            let qri = q_rev
                .inv(d as usize + 1)
                .expect("nverse should exist for non-zero polynomial");
            self.div_mod_ri(q, &qri)
        }
    }

    /// O(n^2)
    pub fn div_mod_small(&self, q: &Self) -> (Self, Self) {
        let mut r = self.clone();
        let mut d = Self::new(vec![]);
        let q_lead_inv = inv::<M>(q.coeff[q.deg_or_0()]);
        while r.deg_or_0() >= q.deg_or_0() {
            let coeff = (r.coeff[r.deg_or_0()] * q_lead_inv).rem_euclid(M as E);
            d.coeff.push(coeff);
            if coeff != 0 {
                let deg_diff = r.deg_or_0() - q.deg_or_0();
                for i in 0..=q.deg_or_0() {
                    if deg_diff + i < r.coeff.len() {
                        r.coeff[deg_diff + i] =
                            (r.coeff[deg_diff + i] - coeff * q.coeff[i]).rem_euclid(M as E);
                    }
                }
            }
            r.coeff.pop();
        }
        d.coeff.reverse();
        if d.coeff.is_empty() {
            d.coeff.push(0);
        }
        (d, r)
    }

    #[inline]
    pub fn mod_xnm1(mut self, n: usize) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        for i in (n..=d).rev() {
            self.coeff[i - n] += self.coeff[i];
        }
        self.mod_xn(n)
    }

    #[inline]
    pub fn shl_mod_xnm1(mut self, mut rhs: usize, n: usize) -> Self {
        rhs %= n;
        if rhs == 0 {
            return self;
        }
        let l = self.coeff.len();
        let mut res = vec![0; n];
        for i in 0..l {
            res[(i + rhs) % n] += self.coeff[i];
        }
        self.coeff.resize(n, 0);
        self.coeff.copy_from_slice(&res);
        self
    }

    #[inline]
    pub fn shr_mod_xnm1(self, rhs: usize, n: usize) -> Self {
        self.shl_mod_xnm1(n - rhs, n)
    }

    #[inline]
    pub fn mul_mod_xnm1(mut self, rhs: Self, n: usize) -> Self {
        self = self.mod_xnm1(n);
        self *= rhs;
        self.mod_xnm1(n).normalize()
    }

    #[inline]
    pub fn square_mod_xnm1(self, n: usize) -> Self {
        self.mod_xnm1(n).square().mod_xnm1(n).normalize()
    }

    /// O(n log n log k)
    #[inline]
    pub fn pow_bin_mod_xnm1(mut self, mut k: usize, n: usize) -> Self {
        self = self.mod_xnm1(n);
        let mut ak = Self::new(vec![1]);
        while k != 0 {
            if k & 1 != 0 {
                ak = ak.mul_mod_xnm1(self.clone(), n);
            }
            self = self.square_mod_xnm1(n);
            k >>= 1;
        }
        ak
    }

    /// O(m log m log k)
    #[inline]
    pub fn pow_mod_ri(mut self, mut k: usize, md: &Self, mdri: &Self) -> Self {
        let mut ak = Self::new(vec![1]);
        while k != 0 {
            if k & 1 != 0 {
                ak = (ak * &self).div_mod_ri(md, mdri).1.normalize();
            }
            self = self.square().div_mod_ri(md, mdri).1.normalize();
            k >>= 1;
        }
        ak
    }

    /// O(m log m log k)
    #[inline]
    pub fn pow_mod(self, k: usize, md: Self) -> Self {
        let d = md.deg_or_0();
        if md == Self::txnpz(1, 0, d) {
            self.pow(k, d)
        } else if md == Self::txnpz(1, 0, d) - 1 {
            self.pow_bin_mod_xnm1(k, d)
        } else {
            self.pow_mod_ri(
                k,
                &md,
                &md.clone().reverse_n(d + 1).inv(d + 1).unwrap().normalize(),
            )
        }
    }

    /// O(n log n)
    pub fn comp_inv_pows_xi(self, i: usize, n: usize) -> Self {
        let n = n.min(i);
        let a1_inv = inv::<M>(self.coeff[1]);
        let mut p = ((self >> 1) * a1_inv)
            .inv_pow(i, n)
            .unwrap()
            .reverse_k(i)
            .normalize()
            * mod_pow_signed::<M>(a1_inv, i as u64);
        let i_inv = inv::<M>(i as E) as E;
        let l = p.len();
        for j in 0..l {
            p.coeff[j] %= M as E;
            p.coeff[j] *= j as E % M as E * i_inv % M as E;
        }
        p
    }

    /// O(n log n log i)
    #[inline]
    pub fn quo_xi(mut self, mut rhs: Self, mut i: usize) -> E {
        let tz = rhs.trailing_xk_or_0();
        if tz != 0 {
            i += tz;
            rhs >>= tz;
        }
        while i > 1 << 9 {
            let (d0, d1);
            (self, d0) = self.mod_xn(i << 1).truncate_deg_or_0();
            (rhs, d1) = rhs.mod_xn(i << 1).truncate_deg_or_0();
            rhs = rhs.n1pkmi(0);
            let n0 = (d0 + d1 + 1).next_power_of_two();
            let n1 = ((d1 << 1) + 1).next_power_of_two();
            if n0 == n1 {
                rhs = rhs.resize(n0).ntt();
                self = self.resize(n0).ntt();
                if i & 1 == 0 {
                    self = self.ntt_mul_even(&rhs);
                } else {
                    self = self.ntt_mul_odd(&rhs);
                }
                self = self.intt().normalize();
                rhs = rhs.ntt_mul_neg_self_even().intt().normalize();
            } else {
                let (q0, q1);
                if n0 <= n1 {
                    q1 = rhs.resize(n1).ntt();
                    q0 = q1.clone_mod_xn(n0);
                } else {
                    q0 = rhs.resize(n0).ntt();
                    q1 = q0.clone_mod_xn(n1);
                }
                self = self.resize(n0).ntt();
                if i & 1 == 0 {
                    self = self.ntt_mul_even(&q0);
                } else {
                    self = self.ntt_mul_odd(&q0);
                }
                self = self.intt().normalize();
                rhs = q1.ntt_mul_neg_self_even().intt().normalize();
            }
            i >>= 1;
        }
        (self.mod_xn(i + 1).truncate_deg().0 * rhs.inv(i + 1).unwrap().truncate_deg().0.normalize())
            .coeff[i]
            % M as E
    }

    /// O(d log d log i)
    pub fn inv_xi(self, i: usize) -> E {
        Self::new(vec![1]).quo_xi(self, i)
    }

    /// O(d log d log i)
    pub fn log_xi(self, i: usize) -> E {
        self.clone().diff_x().quo_xi(self, i) * inv::<M>(i as E) % M as E
    }

    /// O(n log n log i)
    pub fn quo_xi_t_rev(mut self, i: usize) -> Self {
        let d;
        (self, d) = self.mod_xn(i + 1).truncate_deg_or_0();
        fn rec<const M: u64>(i: usize, mut q: Poly<M>, d: usize) -> Poly<M> {
            if i == 0 {
                return Poly::<M>::txnpz(inv::<M>(q.coeff[0]), 0, d - 1);
            }
            let n = (q.len() << 1).next_power_of_two();
            q = q.resize(n).ntt();
            let mut p = rec(
                i >> 1,
                q.clone().ntt_mul_neg_self_even().intt().normalize(),
                d,
            );
            let n = (p.len() << 1).min(d << 1);
            p = p.resize(n);
            if i & 1 == 0 {
                for i in (1..n >> 1).rev() {
                    p[i << 1 | 1] = p[i];
                    for j in ((i - 1) << 1 | 1) + 1..i << 1 | 1 {
                        p[j] = 0;
                    }
                }
                p[1] = p[0];
                p[0] = 0;
            } else {
                for i in (1..n >> 1).rev() {
                    p[i << 1] = p[i];
                    for j in ((i - 1) << 1) + 1..i << 1 {
                        p[j] = 0;
                    }
                }
            }
            p = p.mod_xn(d << 1);
            p = p.resize(n).ntt().normalize();
            for i in 0..n {
                p[i] = p[i] * q[i ^ 1];
            }
            p = p.intt().normalize();
            (p >> d).mod_xn(d)
        }
        rec(i, self, d)
    }

    /// O(n log n log i)
    pub fn xi_mod(self, i: usize) -> Self {
        if i < self.len() - 1 {
            return Self::txnpz(1, 0, i);
        }
        let (q, d) = self.truncate_reverse();
        if i < d {
            return Self::txnpz(1, 0, i);
        }
        let a = q.clone().quo_xi_t_rev(i);
        (a * q).mod_xn(d).reverse_k(d - 1)
    }

    #[inline]
    pub fn mulx(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let mut cur = 1;
        for i in 0..=d {
            self.coeff[i] = (self.coeff[i] * cur) % M as E;
            cur *= a;
            cur %= M as E;
        }
        self
    }

    #[inline]
    pub fn mulx_aic2_ti(mut self, a: E, t: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let (mut cur, mut total, mut ti) = (1, 1, 1);
        for i in 0..=d {
            self.coeff[i] *= (total * ti) % M as E;
            self.coeff[i] %= M as E;
            total *= cur;
            total %= M as E;
            cur *= a;
            cur %= M as E;
            ti *= t;
            ti %= M as E;
        }
        self
    }

    /// O(n log n)
    pub fn chirpz(mut self, z: E, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_deg();
        let mut z = z.rem_euclid(M as E);
        if (z - M as E).abs() < z {
            z = z - M as E;
        }
        if d.is_none() {
            Self::new(vec![0; k])
        } else if z == 0 {
            let mut ans = vec![self.coeff[0]; k];
            if k > 0 {
                ans[0] = self.coeff.iter().sum();
            }
            Self::new(ans)
        } else {
            let mut z_inv = inv::<M>(z);
            if (z_inv - M as E).abs() < z_inv {
                z_inv = z_inv - M as E;
            }
            Self::new(vec![1; k + d.unwrap_or(0)])
                .mulx_aic2_ti(z, 1)
                .mul_t(self.mulx_aic2_ti(z_inv, 1))
                .mod_xn(k)
                .mulx_aic2_ti(z_inv, 1)
        }
    }

    /// O(n)
    /// ∏_{1 <= j <= i} 1/(1 - z^j)
    #[inline]
    pub fn pref_prod_1o1mzi(z: E, n: usize) -> Self {
        let mut p = vec![1; n];
        let mut zk = vec![0; n];
        zk[0] = 1;
        for i in 1..n {
            zk[i] = (zk[i - 1] * z) % M as E;
            p[i] = (p[i - 1] * (1 - zk[i])) % M as E;
        }
        if let Some(l) = p.last_mut() {
            *l = inv::<M>(*l);
        }
        for i in (0..n - 1).rev() {
            p[i] = ((1 - zk[i + 1]) * p[i + 1]) % M as E;
        }
        Self::new(p)
    }

    /// O(n log n)
    /// log ∏_{i=0}^{n-1} f(z^i x)
    #[inline]
    pub fn log_prod_mulx_zi(mut self, q: E, k: usize, n: usize) -> Self {
        let n = n.next_power_of_two();
        let mut qim1s = Vec::with_capacity(n);
        let mut qi = q;
        for _ in 0..n {
            qim1s.push(qi - 1);
            qi = (qi * q) % M as E;
        }
        let qim1is = inverses::<M, _>(&qim1s);
        self = self.log(n).unwrap();
        let qk = mod_pow_signed::<M>(q, k as u64);
        let mut qkm = qk;
        for i in 1..n {
            self.coeff[i] = self.coeff[i] * (qkm - 1) % M as E * qim1is[i - 1] % M as E;
            qkm = (qkm * qk) % M as E;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn chirpz_inv(&self, z: E, k: usize) -> Self {
        let d = if let Some(d) = self.deg() {
            d
        } else {
            return Self::new(vec![]);
        };
        if d == 0 && self.coeff[0] == 0 {
            if k == 1 {
                return self.clone();
            } else {
                return Self::new(vec![self.coeff[1], self.coeff[0] - self.coeff[1]]);
            }
        }
        let mut y = self.clone_mod_xn(k);
        let prods_pos = Self::pref_prod_1o1mzi(z, k);
        let prods_neg = Self::pref_prod_1o1mzi(inv::<M>(z), k);
        let zk = inv::<M>(mod_pow_signed::<M>(z, k as u64 - 1));
        let mut zki = 1;
        for i in 0..k {
            y[i] *= ((zki * prods_neg[i]) % M as E * prods_pos[(k - 1) - i]) % M as E;
            y[i] %= M as E;
            zki = (zki * zk) % M as E;
        }
        let p_over_q = y.chirpz(z, k);
        let q = Self::new(vec![1; k]).kqci(k, z).mulx_aic2_ti(z, -1);
        (p_over_q * q).mod_xn(k).reverse_n(k)
    }

    /// O(n log^2 n)
    pub fn build_prod_tree(tree: &mut [Self], x: &[E], v: usize, l: usize, r: usize) {
        if r - l == 1 {
            tree[v] = Self::new(vec![-x[l], 1]);
        } else {
            let m = l + (r - l >> 1);
            Self::build_prod_tree(tree, x, v << 1, l, m);
            Self::build_prod_tree(tree, x, v << 1 | 1, m, r);
            tree[v] = (tree[v << 1].clone() * tree[v << 1 | 1].clone())
                .truncate_deg()
                .0;
        }
    }

    /// O(n log^2 n)
    pub fn build_prod_tree_ntt(tree: &mut [(Self, Self)], x: &[E], v: usize, l: usize, r: usize) {
        if r - l == 1 {
            tree[v].0 = Self::new(vec![-x[l], 1]);
            tree[v].1 = tree[v].0.clone().ntt();
        } else {
            let m = l + (r - l >> 1);
            Self::build_prod_tree_ntt(tree, x, v << 1, l, m);
            Self::build_prod_tree_ntt(tree, x, v << 1 | 1, m, r);
            tree[v << 1].1 = std::mem::take(&mut tree[v << 1].1).extend_ntt(tree[v << 1].0.clone());
            tree[v << 1 | 1].1 =
                std::mem::take(&mut tree[v << 1 | 1].1).extend_ntt(tree[v << 1 | 1].0.clone());
            let z1 = tree[v << 1].1.clone().dot(&tree[v << 1 | 1].1).normalize();
            tree[v].1 = z1.clone();
            tree[v].0 = z1.intt().normalize().truncate_deg().0;
        }
    }

    /// O(n log^2 n)
    pub fn evals_rec(self, tree: &[(Self, Self)], y: &mut [E], v: usize, l: usize, r: usize) {
        if r - l == 1 {
            y[l] = self.coeff[1];
        } else {
            let m = l + (r - l >> 1);
            let n = self.len();
            let mut p = self
                .clone()
                .mul_t_ntt(&tree[v << 1 | 1].1)
                .resize(n - tree[v << 1 | 1].0.len() + 1)
                .mod_xn(r - l);
            p[0] = 0;
            p.evals_rec(tree, y, v << 1, l, m);
            let mut q = self
                .mul_t_ntt(&tree[v << 1].1)
                .resize(n - tree[v << 1].0.len() + 1)
                .mod_xn(r - l);
            q[0] = 0;
            q.evals_rec(tree, y, v << 1 | 1, m, r);
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn evals(self, x: &[E]) -> Self {
        let n = x.len();
        if self.is_zero() {
            return Self::new(vec![0; n]);
        }
        let mut tree = vec![(Self::new(vec![]), Self::new(vec![])); n.next_power_of_two() << 1];
        Self::build_prod_tree_ntt(&mut tree, x, 1, 0, n);
        let d;
        (tree[1].0, d) = std::mem::take(&mut tree[1].0).truncate_reverse();
        let mut p = (tree[1].0.inv(self.len()).unwrap() << d)
            .mul_t(self)
            .mod_xn(n + 1);
        p[0] = 0;
        let mut y = Self::new(vec![0; n]);
        p.evals_rec(&tree, &mut y.coeff, 1, 0, n);
        y
    }

    /// O(n log^2 n)
    pub fn interp_rec(self, tree: &[(Self, Self)], y: &[E], v: usize, l: usize, r: usize) -> Self {
        if r - l == 1 {
            Self::new(vec![(y[l] * inv::<M>(self.coeff[1])) % M as E])
        } else {
            let m = l + (r - l >> 1);
            let n = self.len();
            let mut p = self
                .clone()
                .mul_t_ntt(&tree[v << 1 | 1].1)
                .resize(n - tree[v << 1 | 1].0.len() + 1)
                .mod_xn(r - l);
            p[0] = 0;
            let a = p.interp_rec(tree, y, v << 1, l, m);
            let mut q = self
                .mul_t_ntt(&tree[v << 1].1)
                .resize(n - tree[v << 1].0.len() + 1)
                .mod_xn(r - l);
            q[0] = 0;
            let b = q.interp_rec(tree, y, v << 1 | 1, m, r);
            if r - l <= 200 {
                a * tree[v << 1 | 1].0.clone() + b * tree[v << 1].0.clone()
            } else {
                (a.resize(tree[v << 1 | 1].1.len())
                    .ntt()
                    .dot(&tree[v << 1 | 1].1)
                    .intt()
                    + b.resize(tree[v << 1].1.len())
                        .ntt()
                        .dot(&tree[v << 1].1)
                        .intt())
                .normalize()
            }
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn interp(&self, x: &[E]) -> Self {
        let n = self.len();
        let mut tree = vec![(Self::new(vec![]), Self::new(vec![])); n.next_power_of_two() << 1];
        Self::build_prod_tree_ntt(&mut tree, x, 1, 0, n);
        let q = tree[1].0.clone().diff_x() >> 1;
        let d;
        (tree[1].0, d) = std::mem::take(&mut tree[1].0).truncate_reverse();
        let mut p = (tree[1].0.inv(n).unwrap() << d).mul_t(q).mod_xn(n + 1);
        p[0] = 0;
        p.interp_rec(&tree, &self.coeff, 1, 0, n)
    }

    /// O(n log^2 n)
    pub fn evals_t_rec(
        &self,
        tree: &mut [Self],
        x: &[E],
        n: usize,
        v: usize,
        l: usize,
        r: usize,
    ) -> Self {
        if r - l == 1 {
            tree[v] = Self::new(vec![1, -x[l]]);
            Self::new(vec![self.coeff[l]])
        } else {
            let m = l + (r - l >> 1);
            let a = self.evals_t_rec(tree, x, n, v << 1, l, m);
            let b = self.evals_t_rec(tree, x, n, v << 1 | 1, m, r);
            tree[v] = (tree[v << 1].clone() * tree[v << 1 | 1].clone())
                .mod_xn(n)
                .truncate_deg()
                .0;
            (a * std::mem::take(&mut tree[v << 1 | 1])).mod_xn(n)
                + (b * std::mem::take(&mut tree[v << 1])).mod_xn(n)
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn evals_t(self, x: &[E], m: usize) -> Self {
        let n = self.len();
        let mut tree = vec![Self::new(vec![]); n.next_power_of_two() << 1];
        let p = self.evals_t_rec(&mut tree, x, m, 1, 0, n);
        (p * tree[1].inv(m).unwrap()).mod_xn(m)
    }

    /// O(n log^2 n)
    pub fn interp_t_rec(
        self,
        tree: &[(Self, Self)],
        y: Self,
        o: &mut [E],
        v: usize,
        l: usize,
        r: usize,
    ) {
        if r - l == 1 {
            o[l] = y[0] * inv::<M>(self.coeff[1]);
        } else {
            let m = l + (r - l >> 1);
            let n = self.len();
            let k = y.len();
            let mut p = self
                .clone()
                .mul_t_ntt(&tree[v << 1 | 1].1)
                .resize(n - tree[v << 1 | 1].0.len() + 1)
                .mod_xn(r - l);
            p[0] = 0;
            p.interp_t_rec(
                tree,
                y.clone()
                    .mul_t_ntt(&tree[v << 1 | 1].1)
                    .resize(k - tree[v << 1 | 1].0.len() + 1),
                o,
                v << 1,
                l,
                m,
            );
            let mut q = self
                .mul_t_ntt(&tree[v << 1].1)
                .resize(n - tree[v << 1].0.len() + 1)
                .mod_xn(r - l);
            q[0] = 0;
            q.interp_t_rec(
                tree,
                y.mul_t_ntt(&tree[v << 1].1)
                    .resize(k - tree[v << 1].0.len() + 1),
                o,
                v << 1 | 1,
                m,
                r,
            );
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn interp_t(self, x: &[E]) -> Self {
        let n = self.len();
        let mut tree = vec![(Self::new(vec![]), Self::new(vec![])); n.next_power_of_two() << 1];
        Self::build_prod_tree_ntt(&mut tree, x, 1, 0, n);
        let q = tree[1].0.clone().diff_x() >> 1;
        let d;
        (tree[1].0, d) = std::mem::take(&mut tree[1].0).truncate_reverse();
        let mut p = (tree[1].0.inv(n).unwrap() << d).mul_t(q).mod_xn(n + 1);
        p[0] = 0;
        let mut o = Self::new(vec![0; n]);
        p.interp_t_rec(&tree, self, &mut o.coeff, 1, 0, n);
        o
    }

    /// O(n log n)
    #[inline]
    pub fn evals_n_fall(self, n: usize) -> Self {
        (self * Self::exp_x(n)).mod_xn(n).inv_borel()
    }

    /// O(n log n)
    #[inline]
    pub fn interp_n_fall(self, n: usize) -> Self {
        (self.borel() * Self::exp_ax(-1, n)).mod_xn(n)
    }

    #[inline]
    pub fn txnpz(t: E, z: E, n: usize) -> Self {
        let mut s = Self::new(vec![0; n]).push(t);
        if n != 0 {
            s[0] = z;
        }
        s
    }

    /// O(n)
    #[inline]
    pub fn exp_x(n: usize) -> Self {
        Self::new(vec![1; n]).borel()
    }

    /// O(n)
    #[inline]
    pub fn q_exp_x(n: usize, q: E) -> Self {
        Self::new(vec![1; n]).q_borel(q)
    }

    /// O(n)
    pub fn autocorrelation(s: &str) -> Self {
        let n = s.len();
        let s = s.chars().collect::<Vec<_>>();
        let mut z = vec![0; n];
        let (mut l, mut r) = (0, 0);
        for i in 1..n {
            if i < r {
                z[i] = (r - i).min(z[i - l]);
            }
            while i + z[i] < n && s[z[i]] == s[i + z[i]] {
                z[i] += 1;
            }
            if i + z[i] > r {
                l = i;
                r = i + z[i];
            }
        }
        let mut p = vec![0; n];
        p[0] = 1;
        for i in 1..n {
            if z[i] == n - i {
                p[i] = 1;
            }
        }
        Self::new(p)
    }

    /// O(n)
    #[inline]
    pub fn exp_ax(a: E, n: usize) -> Self {
        let mut a = a.rem_euclid(M as E);
        if (M as E) >> 1 < a {
            a -= M as E;
        }
        let mut b = 1;
        Self::new(
            (0..n)
                .map(|_| {
                    let v = b;
                    b = (b * a) % M as E;
                    v
                })
                .collect(),
        )
        .borel()
    }

    /// O(n)
    #[inline]
    pub fn n1pkmi(mut self, k: usize) -> Self {
        self.coeff
            .iter_mut()
            .skip(k ^ 1 & 1)
            .step_by(2)
            .for_each(|v| *v = -*v);
        self
    }

    /// O(n)
    #[inline]
    pub fn kci(mut self, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let n = d + 1;
        let invs = inverses_n_div::<M>(n);
        let mut a = 1;
        for i in 1..n.min(k + 1) {
            a *= (k + 1 - i) as u64 * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as E;
            self.coeff[i] %= M as E;
        }
        for i in k + 1..n {
            self.coeff[i] = 0;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn kpici(mut self, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let n = d + 1;
        let invs = inverses_n_div::<M>(n);
        let mut a = 1;
        for i in 1..n {
            a *= (i + k) as u64 * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn ick(mut self, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let n = d + 1;
        let invs = inverses_n_div::<M>(n - k);
        self.coeff[0..k.min(n)].fill(0);
        let mut a = 1;
        for i in k + 1..n {
            a *= i as u64 * invs[i - k] % M;
            a %= M;
            self.coeff[i] *= a as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn i2ci(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let n = d + 1;
        let mut a = 1;
        let invs = inverses_n_div::<M>(n);
        for i in 1..n {
            a *= ((((i as u64) << 1) - 1) << 1) * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn i2qci(mut self, q: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let n = d + 1;
        let mut qim1s = Vec::with_capacity((n << 1) + 3);
        let mut qi = q;
        for _ in 0..(n << 1) + 3 {
            qim1s.push(qi - 1);
            qi = (qi * q) % M as E;
        }
        let qim1is = inverses::<M, _>(&qim1s);
        let mut l = 1;
        for i in 1..n.min(self.coeff.len()) {
            l = (((l * qim1s[(i << 1) - 1]) % M as E * qim1s[(i << 1) - 2] % M as E)
                * qim1is[i - 1])
                % M as E
                * qim1is[i - 1]
                % M as E;
            self.coeff[i] *= l as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(√n log^2 √n)
    #[inline]
    pub fn factorial(n: usize) -> E {
        if n <= 1 << 19 {
            return (1..=n as E).fold(1, |acc, x| acc * x % M as E);
        }
        let m = n.isqrt();
        if m * m == n {
            let p = Self::stirling1(m);
            let x = (m as E..(n + m) as E).step_by(m).collect::<Vec<_>>();
            let p = p.evals(&x).coeff;
            p.iter().fold(1, |a, b| a * b % M as E).rem_euclid(M as E)
        } else {
            let mut a = n as E;
            for i in 1..n - m * m {
                a = (a * (n - i) as E) % M as E;
            }
            a * Self::factorial(m * m) % M as E
        }
    }

    /// O(k log_k n)
    #[inline]
    pub fn stirling2_nk(n: usize, k: usize) -> E {
        let invs = inverses_n_div::<M>(n);
        let pws = sieve_complete(
            k + 1,
            1,
            |a, b| a * b % M as E,
            |p, _| mod_pow_signed::<M>(p as E, n as u64),
        )
        .0;
        let mut r = 0;
        let mut kf = 1;
        let mut b = 1;
        let s = k & 1;
        for i in 1..=k {
            b = b * (k - i + 1) as E % M as E * invs[i] as E % M as E;
            if s ^ (i & 1) == 0 {
                r = (r + b * pws[i]) % M as E;
            } else {
                r = (r - b * pws[i]) % M as E;
            }
            kf = kf * i as E % M as E;
        }
        (inv::<M>(kf) * r % M as E).rem_euclid(M as E)
    }

    /// O(n log n + |k|)
    /// log ∏_{i ∈ k} (1 + x^i t)
    #[inline]
    pub fn log_prod_1pxit(t: E, k: impl Iterator<Item = usize>, n: usize) -> Self {
        let n = n.next_power_of_two();
        let mut p = vec![0; n];
        for i in k {
            let mut x = t;
            for j in (i..n).step_by(i) {
                p[j] += x * i as E;
                x = (-t * x) % M as E;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(n)
    #[inline]
    pub fn kqci(mut self, k: usize, q: E) -> Self {
        let mut qim1s = Vec::with_capacity(k);
        let mut qi = q;
        for _ in 0..k {
            qim1s.push(qi - 1);
            qi = (qi * q) % M as E;
        }
        let qim1is = inverses::<M, _>(&qim1s);
        let mut l = 1;
        for i in 1..self.coeff.len().min(k + 1) {
            l = ((l * qim1s[k - i]) % M as E * qim1is[i - 1]) % M as E;
            self.coeff[i] *= l as E;
            self.coeff[i] %= M as E;
        }
        self.mod_xn(k + 1)
    }

    /// O(n)
    #[inline]
    pub fn kpiqci(mut self, k: usize, q: E) -> Self {
        let n = self.coeff.len();
        let mut qim1s = Vec::with_capacity(n + k);
        let mut qi = q;
        for _ in 0..n + k {
            qim1s.push(qi - 1);
            qi = (qi * q) % M as E;
        }
        let qim1is = inverses::<M, _>(&qim1s);
        let mut l = 1;
        for i in 1..n {
            l = ((l * qim1s[k + i - 1] % M as E) * qim1is[i - 1]) % M as E;
            self.coeff[i] *= l as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn iqck(mut self, k: usize, q: E) -> Self {
        let l = self.len();
        let n = self.coeff.len().min(l);
        let mut qim1s = Vec::with_capacity(n);
        let mut qi = q;
        for _ in 0..n {
            qim1s.push(qi - 1);
            qi = (qi * q) % M as E;
        }
        let qim1is = inverses::<M, _>(&qim1s);
        self.coeff[0..k.min(l)].fill(0);
        let mut l = 1;
        for i in k + 1..n {
            l = ((l * qim1s[i - 1] % M as E) * qim1is[i - k - 1]) % M as E;
            self.coeff[i] *= l as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn inv_q_borel(mut self, q: E) -> Self {
        self = self.truncate_deg().0;
        let mut q_fact = 1;
        let mut qi = (q * q) % M as E;
        let qmii = inv::<M>(q - 1);
        self.coeff.iter_mut().skip(2).for_each(|v| {
            q_fact *= ((qi - 1) * qmii) % M as E;
            q_fact %= M as E;
            *v *= q_fact as E;
            *v %= M as E;
            qi = (qi * q) % M as E;
        });
        self
    }

    /// O(n)
    #[inline]
    pub fn q_borel(mut self, q: E) -> Self {
        self = self.truncate_deg().0;
        let mut qi = (q * q) % M as E;
        let qmii = inv::<M>(q - 1);
        let mut q_fact = 1;
        for _ in 2..self.len() {
            q_fact *= (qi - 1) * qmii % M as E;
            q_fact %= M as E;
            qi = (qi * q) % M as E;
        }
        q_fact = inv::<M>(q_fact);
        let q_inv = inv::<M>(q);
        self.coeff.iter_mut().skip(1).rev().for_each(|v| {
            qi = (qi * q_inv) % M as E;
            *v *= q_fact as E;
            *v %= M as E;
            q_fact *= (qi - 1) * qmii % M as E;
            q_fact %= M as E;
        });
        self
    }

    /// O(n)
    #[inline]
    pub fn log_1o1mx(n: usize) -> Self {
        Self::new(
            inverses_n_div::<M>(n)
                .into_iter()
                .map(|i| i as E)
                .collect::<Vec<_>>(),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1(n: usize) -> Self {
        let mut a = Self::new(vec![0, 1]);
        let mut i = n.ilog2();
        while i > 0 {
            let k = n >> (i - 1);
            let m = k >> 1;
            a *= a.clone().shift(-(m as E));
            if k & 1 == 1 {
                let l = a.len();
                a.coeff.push(a.coeff[l - 1]);
                a.coeff[0] *= -(k as E + 1);
                for i in (1..l).rev() {
                    a.coeff[i] = (-(k as E - 1) * a.coeff[i] % M as E + a.coeff[i - 1]) % M as E;
                }
            }
            i -= 1;
        }
        a
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_k(k: usize, n: usize) -> Self {
        Self::log_1o1mx(n).n1pkmi(1).pow(k, n) * mod_rfact::<M>(k as u64) as E
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_unsigned_k(k: usize, n: usize) -> Self {
        Self::log_1o1mx(n).pow(k, n) * mod_rfact::<M>(k as u64) as E
    }

    /// O(n log n)
    #[inline]
    pub fn stirling2(n: usize) -> Self {
        let mut pws = sieve_complete(
            n + 1,
            1,
            |a, b| a * b % M as E,
            |p, _| mod_pow_signed::<M>(p as E, n as u64),
        )
        .0;
        pws[0] = 0;
        (Self::new(pws).borel() * Self::exp_x(n + 1).n1pkmi(0)).mod_xn(n + 1)
    }

    /// O(n log n)
    #[inline]
    pub fn stirling2_k(k: usize, n: usize) -> Self {
        (Self::exp_x(n) - 1).pow(k, n) * mod_rfact::<M>(k as u64) as E
    }

    /// O(n log n)
    #[inline]
    pub fn corr(self, rhs: Self) -> Self {
        self * rhs.truncate_reverse().0
    }

    /// O(n log n)
    #[inline]
    pub fn semicorr(self, mut rhs: Self) -> Self {
        let d;
        (rhs, d) = rhs.truncate_deg_or_0();
        self.corr(rhs) >> d
    }

    /// O(n log n)
    #[inline]
    pub fn diff_mul(self, rhs: Self) -> Self {
        rhs.inv_borel().semicorr(self).borel()
    }

    /// O(n log n)
    #[inline]
    pub fn dir_mul(&self, rhs: &Self, n: usize) -> Self {
        let m = self.len();
        let k = rhs.len();
        let mut f = vec![0; n];
        for i in 1..m.min(n) {
            for j in (i..=((k - 1) * i).min(n - 1)).step_by(i) {
                f[j] += self.coeff[i] * rhs.coeff[j / i] % M as E;
            }
        }
        Self::new(f)
    }

    /// O(n)
    #[inline]
    pub fn inv_borel(mut self) -> Self {
        self = self.truncate_deg().0;
        let mut a = 1;
        self.coeff[0] %= M as E;
        if self.len() < 2 {
            return self;
        }
        self.coeff[1] %= M as E;
        self.coeff
            .iter_mut()
            .enumerate()
            .skip(2)
            .for_each(|(i, v)| {
                a = (a * i as E) % M as E;
                *v = (*v % M as E * a as E) % M as E;
            });
        self
    }

    /// O(n)
    #[inline]
    pub fn borel(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let mut a = mod_rfact::<M>(d as u64);
        self.coeff[0] %= M as E;
        if self.len() < 2 {
            return self;
        }
        self.coeff[1] %= M as E;
        self.coeff
            .iter_mut()
            .enumerate()
            .skip(2)
            .rev()
            .for_each(|(i, v)| {
                *v = (*v % M as E * a as E) % M as E;
                a = (a * i as E) % M as E;
            });
        self
    }

    /// O(n log^2 n)
    #[inline]
    pub fn mono_to_fall(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let x = (0..(d + 1) as E).collect::<Vec<_>>();
        self.evals(&x).shift_t(-1).borel()
    }

    /// O(n log^2 n)
    #[inline]
    pub fn fall_to_mono(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let x = (0..(d + 1) as E).collect::<Vec<_>>();
        self.inv_borel().shift_t(1).interp(&x)
    }

    /// O(n log^2 n)
    #[inline]
    pub fn mono_to_binom(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let x = (0..(d + 1) as E).collect::<Vec<_>>();
        self.evals(&x).shift_t(-1)
    }

    /// O(n log^2 n)
    #[inline]
    pub fn binom_to_mono(mut self) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let x = (0..(d + 1) as E).collect::<Vec<_>>();
        self.shift_t(1).interp(&x)
    }

    /// O(n log n)
    #[inline]
    pub fn shift(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        self.inv_borel()
            .semicorr(Self::exp_ax(a, d + 1 as usize))
            .borel()
    }

    /// O(n log n)
    #[inline]
    pub fn shift_t(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        (self.borel() * Self::exp_ax(a, d + 1 as usize))
            .mod_xn(d + 1)
            .inv_borel()
    }

    /// O(n log n)
    #[inline]
    pub fn shift_fall(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_deg_or_0();
        let mut a = a.rem_euclid(M as E);
        if (a - M as E).abs() < a {
            a = a - M as E;
        }
        let lhs = if a == 0 {
            return self;
        } else if a > 0 {
            Self::new(vec![1; d + 1]).kci(a as usize)
        } else {
            Self::new(vec![1; d + 1]).kpici((-a) as usize - 1).n1pkmi(0)
        };
        lhs.diff_mul(self)
    }

    /// O(n log n)
    #[inline]
    pub fn shift_pts(self, n: usize) -> Self {
        let d = self.len() - 1;
        ((self.borel().reverse_k(d).borel().n1pkmi(0).reverse_k(d) * Self::log_1o1mx(n))
            .mod_xn(n)
            .inv_borel()
            >> d + 1)
            .borel()
    }

    /// O(n log^2 n)
    pub fn cdq_mul_rec(
        f: &mut impl FnMut(usize, &mut [E], &mut [E], &mut [E]),
        a: &mut [E],
        b: &mut [E],
        c: &mut [E],
        l: usize,
        r: usize,
        k: usize,
    ) {
        if r <= k {
            return;
        } else if r - l == 1 {
            f(l, a, b, c);
            return;
        }
        let m = l + (r - l >> 1);
        Self::cdq_mul_rec(f, a, b, c, l, m, k);
        let x = Self::new(a[l..m].to_vec());
        let y = Self::new(b[0..m.min(r - l)].to_vec());
        let t = x * y;
        for i in m..r.min(t.len() + l + 1) {
            c[i] = (c[i] + t[i - l - 1]) % M as E;
        }
        let x = Self::new(a[0..l.min(r - l)].to_vec());
        let y = Self::new(b[l..m].to_vec());
        let t = x * y;
        for i in m..r.min(t.len() + l + 1) {
            c[i] = (c[i] + t[i - l - 1]) % M as E;
        }
        Self::cdq_mul_rec(f, a, b, c, m, r, k);
    }

    /// O(n log^2 n)
    pub fn cdq_mul(mut f: impl FnMut(usize, &mut [E], &mut [E], &mut [E]), n: usize) -> Self {
        let mut a = vec![0; n];
        let mut b = vec![0; n];
        let mut c = vec![0; n];
        Self::cdq_mul_rec(&mut f, &mut a, &mut b, &mut c, 0, n, 0);
        Self::new(c)
    }

    /// O(n log^2 n)
    pub fn cdq_exp(mut f: impl FnMut(usize, &mut [E], &mut [E]), n: usize) -> Self {
        let mut a = vec![0; n];
        let mut b = vec![0; n];
        let mut c = vec![0; n];
        Self::cdq_mul_rec(
            &mut |i, a, b, c| {
                a[i] = if i == 0 {
                    1
                } else {
                    c[i] * inv::<M>(i as E) % M as E
                };
                f(i, a, b);
                b[i] = b[i] * (i + 1) as E % M as E;
            },
            &mut a,
            &mut b,
            &mut c,
            0,
            n,
            0,
        );
        Self::new(a)
    }

    /// O(n log^2 n)
    pub fn cdq_inv(mut f: impl FnMut(usize, &mut [E], &mut [E]), g0: E, n: usize) -> Self {
        let g0_inv = inv::<M>(g0);
        let mut a = vec![0; n];
        let mut b = vec![0; n];
        let mut c = vec![0; n];
        Self::cdq_mul_rec(
            &mut |i, a, b, c| {
                if i == 0 {
                    a[i] = g0_inv;
                } else {
                    a[i] = -g0_inv * c[i] % M as E;
                }
                f(i, a, b);
            },
            &mut a,
            &mut b,
            &mut c,
            0,
            n,
            0,
        );
        Self::new(a)
    }

    /// O(n log^2 n)
    pub fn cdq_log(mut f: impl FnMut(usize, &mut [E], &mut [E]), n: usize) -> Self {
        let mut a = vec![0; n];
        let mut b = vec![0; n];
        let mut c = vec![0; n];
        let mut l = vec![0; n];
        Self::cdq_mul_rec(
            &mut |i, a, b, c| {
                if i != 0 {
                    a[i] = (i as E * b[i - 1] - c[i]) % M as E;
                }
                l[i] = a[i] * inv::<M>(i as E) % M as E;
                f(i, &mut l, b);
            },
            &mut a,
            &mut b,
            &mut c,
            0,
            n,
            0,
        );
        Self::new(l)
    }

    /// O(n log^2 n)
    pub fn pow_proj(mut self, mut w: Self) -> Self {
        debug_assert_eq!(self.coeff.len(), w.coeff.len());
        let d = self.deg();
        if d.is_none() {
            return Self::new(vec![0; self.len()]);
        } else if self.coeff[0] % M as E != 0 {
            let c = self.coeff[0];
            self.coeff[0] = 0;
            let a = self.pow_proj(w).borel();
            let b = Self::exp_ax(c, a.len());
            return (a * b).inv_borel();
        }
        let mut m = self.coeff.len().next_power_of_two();
        (self, w) = (self.resize(m), w.resize(m));
        w.coeff.reverse();
        let (mut p, mut q) = (vec![Self::new(vec![0]); m], vec![Self::new(vec![0]); m]);
        for i in 0..m {
            p[i].coeff[0] = w[i];
            q[i].coeff[0] = -self.coeff[i];
        }
        let half = inv::<M>(2);
        let v = Self::root_inv_pows_bit_reverse(m).coeff;
        let mut k = 1;
        while m > 1 {
            for i in 0..m {
                p[i] = std::mem::take(&mut p[i]).normalize().double_ntt();
                q[i] = std::mem::take(&mut q[i]).normalize().double_ntt();
            }
            for j in 0..k {
                q[0].coeff[j] += 1;
                q[0].coeff[j + k] -= 1;
            }
            for j in 0..k << 1 {
                let (mut f, mut g) = (Self::new(vec![0; m << 1]), Self::new(vec![0; m << 1]));
                for i in 0..m {
                    (f[i], g[i]) = (p[i][j], q[i][j]);
                }
                (f, g) = (f.ntt(), g.ntt());
                for i in 0..m {
                    f[i] = half * v[i] % M as E
                        * (f[i << 1] * g[i << 1 | 1] % M as E - f[i << 1 | 1] * g[i << 1] % M as E)
                        % M as E;
                }
                for i in 0..m {
                    g[i] = g[i << 1] * g[i << 1 | 1];
                }
                (f, g) = (f.resize(m), g.resize(m));
                (f, g) = (f.intt(), g.intt());
                for i in 0..m >> 1 {
                    p[i][j] = f[i];
                    q[i][j] = g[i];
                }
            }
            for j in 0..k << 1 {
                q[0][j] -= 1;
            }
            p.truncate(m >> 1);
            q.truncate(m >> 1);
            m >>= 1;
            k <<= 1;
        }
        let mut p = std::mem::take(&mut p[0]).intt();
        p.coeff.reverse();
        p
    }

    /// O(n log^2 n)
    pub fn comp_inv(mut self) -> Self {
        let mut n = self.len();
        if n == 0 {
            return Self::new(vec![]);
        };
        n -= 1;
        debug_assert_eq!(self.coeff[0] % M as E, 0);
        debug_assert_ne!(self.coeff[1] % M as E, 0);
        let c = self.coeff[1];
        let ic = inv::<M>(c);
        self *= ic;
        let mut w = vec![0; n + 1];
        w[n] = 1;
        ((self
            .pow_proj(Self::new(w))
            .mod_xn(n + 1)
            .normalize()
            .integr_divx()
            * n as E)
            .reverse_k(n)
            .normalize()
            .pow(M as usize - inv::<M>(n as E).rem_euclid(M as E) as usize, n)
            .normalize()
            << 1)
            .mulx(ic)
    }

    /// O(n log^2 n)
    pub fn comp(mut self, mut rhs: Self) -> Self {
        let m = self.len();
        if m == 0 {
            return Self::new(vec![]);
        };
        let c = rhs[0] % M as E;
        if c != 0 {
            rhs[0] = 0;
            return self
                .inv_borel()
                .semicorr(Self::exp_ax(c, m))
                .mod_xn(m)
                .borel()
                .resize(m)
                .comp(rhs);
        }
        let n = m.next_power_of_two();
        (self, rhs) = (self.resize(n), rhs.resize(n));
        let v = Self::root_inv_pows_bit_reverse(n << 1);
        fn rec<const M: u64>(
            n: usize,
            k: usize,
            mut q: Poly<M>,
            mut f: Poly<M>,
            v: &Poly<M>,
        ) -> Poly<M> {
            if n == 1 {
                f.coeff.reverse();
                let mut p = Poly::<M>::new(vec![0; k << 1]);
                for i in 0..k {
                    p[i << 1] = f[i];
                }
                return p;
            }
            q = q.resize(n * k << 2);
            q[n * k << 1] = 1;
            q = q.normalize().ntt();
            let mut nxt_q = q.ntt_mul_neg_self_even().intt();
            for j in 0..k << 1 {
                for i in n >> 1..n {
                    nxt_q[n * j + i] = 0;
                }
            }
            nxt_q[0] = 0;
            let mut p = rec(n >> 1, k << 1, nxt_q, f, v);
            for j in 0..k << 1 {
                for i in n >> 1..n {
                    p[n * j + i] = 0;
                }
            }
            p = p.normalize().intt_t().resize(n * k << 2);
            let half = inv::<M>(2);
            for i in (0..n * k << 1).rev() {
                let c = p[i] % M as E * half % M as E * v[i] % M as E;
                p[i << 1 | 1] = -q[i << 1] * c % M as E;
                p[i << 1] = q[i << 1 | 1] * c % M as E;
            }
            p.ntt_t().resize(n * k << 1)
        }
        rec(n, 1, (-rhs).resize(n << 1), self, &v)
            .resize(n)
            .reverse()
            .mod_xn(m)
    }

    /// O(n log n)
    pub fn comp_aff(self, a: E, b: E) -> Self {
        self.mulx(b).shift(a * inv::<M>(b))
    }

    /// O(n log n)
    pub fn comp_quad(self, a: E, b: E) -> Self {
        self.shift(a - b * b % M as E * inv::<M>(4) % M as E)
            .sub_xk(2)
            .shift(b * inv::<M>(2) % M as E)
    }

    /// O(n log n)
    pub fn comp_mobius(mut self, a: E, b: E, c: E, d: E, n: usize) -> Self {
        let m;
        (self, m) = self.truncate_deg_or_0();
        let oc = inv::<M>(c);
        let od = inv::<M>(d);
        let f = b * od;
        let e = a - b * od * c;
        self = self.comp_aff(f, e).truncate_reverse().0.comp_aff(c, d);
        (self * Self::new(vec![1; n]).mulx(-d * oc).kpici(m - 1)).mod_xn(n)
            * mod_pow_signed::<M>(oc, m as u64)
    }

    /// O(n log n)
    pub fn comp_xp1ox(self) -> Self {
        self.shift(2)
            .truncate_reverse()
            .0
            .shift(-inv::<M>(4))
            .sub_xk(2)
            .shift(inv::<M>(2))
            .truncate_reverse()
            .0
            .shift(-1)
    }

    /// O(n log^2 n)
    pub fn comp_exp(self, n: usize) -> Self {
        let l = self.len();
        let x = (0..l as E).collect::<Vec<_>>();
        self.evals_t(&x, n).borel()
    }

    /// O(n log^2 n)
    pub fn comp_expm1(self, n: usize) -> Self {
        self.shift(-1).comp_exp(n)
    }

    /// O(n log^2 n)
    pub fn comp_log_1px(self, n: usize) -> Self {
        let x = (0..n as E).collect::<Vec<_>>();
        self.inv_borel().resize(n).interp_t(&x).shift(1)
    }

    /// O(n log^2 n)
    pub fn expm1_pow_proj(self, n: usize) -> Self {
        let x = (0..n as E).collect::<Vec<_>>();
        self.resize(n).borel().evals(&x).shift_t(-1)
    }

    /// O(n log^2 n)
    pub fn log_1px_pow_proj(self, n: usize) -> Self {
        let x = (0..n as E).collect::<Vec<_>>();
        self.resize(n).shift_t(1).interp(&x).inv_borel()
    }

    /// O(n log log n)
    pub fn divisor(mut self, primes: &[usize]) -> Self {
        divisor(&mut self.coeff, primes);
        self
    }

    /// O(n log n)
    pub fn set_aux(&self, n: usize) -> Self {
        let m = self.len();
        let mut p = vec![0; n];
        for i in 1..n.min(m) {
            let v = i as E * self.coeff[i] % M as E;
            for j in (i..n).step_by(i << 1) {
                p[j] += v;
            }
            for j in (i << 1..n).step_by(i << 1) {
                p[j] -= v;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(n log n)
    pub fn mset_aux(mut self) -> Self {
        let n = self.len();
        let primes = sieve_primes(n).0;
        self = self.diff_x();
        divisor(&mut self.coeff, &primes);
        self.integr_divx()
    }

    /// O(n log n)
    pub fn cyc_aux(&self, n: usize) -> Self {
        let m = self.len();
        let totient = sieve(
            n,
            1,
            |a, b| a * b % M as E,
            |p, k, _| mod_pow::<M>(p as u64, k as u64 - 1) as E * (p as E - 1) % M as E,
        )
        .0;
        let mut p = vec![0; n];
        for i in 1..n.min(m) {
            let v = i as E * self.coeff[i] % M as E;
            let mut q = 1;
            for j in (i..n).step_by(i) {
                p[j] += totient[q] * v % M as E;
                q += 1;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(n log n)
    pub fn dir_cyc_aux(&self, n: usize) -> Self {
        let m = self.len();
        let f = sieve(
            n.ilog2() as usize + 1,
            1,
            |a, b| a * b % M as E,
            |p, k, _| {
                if k <= 1 {
                    (p as E - 1) * inv::<M>(p as E)
                } else {
                    mod_pow::<M>(p as u64, k as u64 - 2) as E * (p as E - 1) % M as E
                }
            },
        )
        .0;
        let mut p = vec![0; n];
        for i in 2..n.min(m) {
            let (mut j, mut d) = (i, 1);
            while j < n {
                p[j] += self.coeff[i] * f[d] % M as E;
                (j, d) = (j * i, d + 1);
            }
        }
        Self::new(p)
    }

    /// O(2^n n^2)
    pub fn sps_mul_slice(a: &[E], b: &[E], o: &mut [E]) {
        let n = a.len().trailing_zeros() as usize;
        let mut ahat = vec![vec![0; 1 << n]; n + 1];
        let mut bhat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            ahat[m.count_ones() as usize][m] = a[m];
            bhat[m.count_ones() as usize][m] = b[m];
        }
        for i in 0..=n {
            subset(&mut ahat[i]);
            subset(&mut bhat[i]);
            ahat[i].iter_mut().for_each(|i| *i %= M as E);
            bhat[i].iter_mut().for_each(|i| *i %= M as E);
        }
        let mut h = vec![vec![0; 1 << n]; n + 1];
        for i in 0..=n {
            for j in 0..=i {
                h[i].iter_mut()
                    .zip(&ahat[j])
                    .zip(&bhat[i - j])
                    .for_each(|((a, b), c)| *a += b * c % M as E);
            }
        }
        for i in 0..=n {
            subset_inv(&mut h[i]);
        }
        for m in 0..1 << n {
            o[m] = h[m.count_ones() as usize][m] % M as E;
        }
    }

    /// O(2^n n^2)
    pub fn sps_mul(&self, rhs: &Self) -> Self {
        let mut r = vec![0; self.coeff.len()];
        Self::sps_mul_slice(&self.coeff, &rhs.coeff, &mut r);
        Self::new(r)
    }

    /// O(2^n n^2)
    pub fn sps_mul_t_slice(a: &mut [E], b: &[E], o: &mut [E]) {
        a.reverse();
        Self::sps_mul_slice(a, b, o);
        a.reverse();
        o.reverse();
    }

    /// O(2^n n^2)
    pub fn sps_mul_t(&mut self, rhs: &Self) -> Self {
        let mut r = vec![0; self.coeff.len()];
        Self::sps_mul_t_slice(&mut self.coeff, &rhs.coeff, &mut r);
        Self::new(r)
    }

    /// O(2^n n^2)
    pub fn sps_square(mut self) -> Self {
        let n = self.len().ilog2() as usize;
        let mut fhat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            fhat[m.count_ones() as usize][m] = self.coeff[m];
        }
        for i in 0..=n {
            subset(&mut fhat[i]);
            fhat[i].iter_mut().for_each(|i| *i %= M as E);
        }
        let mut h = vec![vec![0; 1 << n]; n + 1];
        for i in 0..=n {
            for j in 0..=i {
                h[i].iter_mut()
                    .zip(&fhat[j])
                    .zip(&fhat[i - j])
                    .for_each(|((a, b), c)| *a += b * c % M as E);
            }
        }
        for i in 0..=n {
            subset_inv(&mut h[i]);
        }
        for m in 0..1 << n {
            self.coeff[m] = h[m.count_ones() as usize][m];
        }
        self
    }

    /// O(2^n n^2)
    pub fn sps_inv(&self) -> Self {
        let n = self.len().trailing_zeros() as usize;
        let a0_inv = inv::<M>(self.coeff[0]);
        let mut res = vec![0; 1 << n];
        let mut res_hat = vec![vec![0; 1 << n]; n + 1];
        let mut self_hat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            self_hat[m.count_ones() as usize][m] = self.coeff[m];
        }
        for i in 0..=n {
            subset(&mut self_hat[i]);
            self_hat[i].iter_mut().for_each(|i| *i %= M as E);
        }
        for l in 0..=n {
            res_hat[l]
                .iter_mut()
                .zip(&self_hat[0])
                .for_each(|(i, j)| *i += *i * *j % M as E);
            for i in 1..=l {
                let [res_hat_l, res_hat_lmi] = res_hat.get_disjoint_mut([l, l - i]).unwrap();
                res_hat_l
                    .iter_mut()
                    .zip(&self_hat[i])
                    .zip(res_hat_lmi)
                    .for_each(|((i, j), &mut k)| *i += j * k % M as E);
            }
            subset_inv(&mut res_hat[l]);
            if l == 0 {
                res_hat[l][0] = (1 - res_hat[l][0]) * a0_inv % M as E;
                res[0] = res_hat[l][0];
            }
            for x in 1..1_usize << n {
                if x.count_ones() as usize == l {
                    res_hat[l][x] = ((x == 0) as E - res_hat[l][x]) * a0_inv % M as E;
                    res[x] = res_hat[l][x];
                }
            }
            subset(&mut res_hat[l]);
            res_hat[l].iter_mut().for_each(|i| *i %= M as E);
        }
        Self::new(res)
    }

    /// O(2^n n^2)
    pub fn sps_quo_slice(a: &[E], b: &[E], o: &mut [E]) {
        let n = a.len().trailing_zeros() as usize;
        let a0_inv = inv::<M>(b[0]);
        let mut res_hat = vec![vec![0; 1 << n]; n + 1];
        let mut b_hat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            b_hat[m.count_ones() as usize][m] = b[m];
        }
        for i in 0..=n {
            subset(&mut b_hat[i]);
            b_hat[i].iter_mut().for_each(|i| *i %= M as E);
        }
        for l in 0..=n {
            res_hat[l]
                .iter_mut()
                .zip(&b_hat[0])
                .for_each(|(i, j)| *i += *i * *j % M as E);
            for i in 1..=l {
                let [res_hat_l, res_hat_lmi] = res_hat.get_disjoint_mut([l, l - i]).unwrap();
                res_hat_l
                    .iter_mut()
                    .zip(&b_hat[i])
                    .zip(res_hat_lmi)
                    .for_each(|((i, j), &mut k)| *i += j * k % M as E);
            }
            subset_inv(&mut res_hat[l]);
            for x in 0..1_usize << n {
                if x.count_ones() as usize == l {
                    res_hat[l][x] = (a[x] - res_hat[l][x]) * a0_inv % M as E;
                    o[x] = res_hat[l][x];
                }
            }
            subset(&mut res_hat[l]);
            res_hat[l].iter_mut().for_each(|i| *i %= M as E);
        }
    }

    /// O(2^n n^2)
    pub fn sps_quo(self, rhs: &Self) -> Self {
        let mut r = vec![0; self.coeff.len()];
        Self::sps_quo_slice(&self.coeff, &rhs.coeff, &mut r);
        Self::new(r)
    }

    /// O(2^n n^2)
    pub fn sps_exp(&self) -> Option<Self> {
        let n = self.coeff.len().trailing_zeros();
        if self.coeff[0] != 0 {
            return None;
        }
        let mut e = vec![0; 1 << n];
        e[0] = 1;
        for i in 0..n {
            let (a, b) = e.split_at_mut(1 << i);
            Self::sps_mul_slice(&a, &self.coeff[1 << i..2 << i], &mut b[..1 << i]);
        }
        Some(Self::new(e))
    }

    /// O(2^n n^2)
    pub fn sps_log(&self) -> Option<Self> {
        let n = self.coeff.len().trailing_zeros();
        if self.coeff[0] == 0 {
            return None;
        }
        let mut l = vec![0; 1 << n];
        for i in 0..n {
            Self::sps_quo_slice(
                &self.coeff[1 << i..2 << i],
                &self.coeff[..1 << i],
                &mut l[1 << i..2 << i],
            );
        }
        Some(Self::new(l))
    }

    /// O(2^n n^2)
    #[inline]
    pub fn sps_pow(&self, k: usize) -> Self {
        let a0 = self.coeff[0] % M as E;
        if a0 != 0 {
            let mut a0k = mod_pow_signed::<M>(a0, k as u64);
            let mut k = k as E;
            if (M as E) >> 1 < k {
                k -= M as E;
            }
            if (M as E) >> 1 < a0k {
                a0k -= M as E;
            }
            (self.sps_log().unwrap() * k as E)
                .normalize()
                .sps_exp()
                .unwrap()
                * a0k
        } else {
            let n = self.len().trailing_zeros() as usize;
            let mut c = Self::new(vec![0; 1 << n]);
            if k > n {
                return c;
            }
            c[0] = mod_fact::<M>(k as u64) as E;
            for i in (0..k).rev() {
                for j in (0..n - i).rev() {
                    let (x, y) = c.coeff.split_at_mut(1 << j);
                    Self::sps_mul_slice(&x, &self.coeff[1 << j..2 << j], &mut y[..1 << j]);
                }
                c[0] = 0;
            }
            c
        }
    }

    /// O(2^n n^2) if rhs.coeff\[0\] == 0
    /// O(2^n n^2 + d log d) else
    pub fn comp_sps(mut self, mut rhs: Self) -> Self {
        let m = self.coeff.len();
        let n = rhs.len().trailing_zeros() as usize;
        let a1 = rhs.coeff[0] % M as E;
        self = self.inv_borel();
        rhs.coeff[0] = 0;
        if a1 != 0 {
            self = self.semicorr(Self::exp_ax(a1, m));
        }
        let mut c = Self::new(vec![0; 1 << n]);
        for i in (0..=n).rev() {
            for j in (0..n - i).rev() {
                let (x, y) = c.coeff.split_at_mut(1 << j);
                Self::sps_mul_slice(&x, &rhs.coeff[1 << j..2 << j], &mut y[..1 << j]);
            }
            c[0] = if i < m { self.coeff[i] } else { 0 };
        }
        c
    }

    /// O(2^n n^2 + m log m)
    pub fn sps_pow_proj(mut self, mut w: Self, m: usize) -> Self {
        let n = self.len().trailing_zeros() as usize;
        let m = m.next_power_of_two();
        let a1 = self.coeff[0] % M as E;
        self.coeff[0] = 0;
        let mut c = Self::new(vec![0; n + 1]);
        let mut s = vec![0; 1 << n];
        for i in 0..=n {
            c[i] = w.coeff[0];
            w.coeff[0] = 0;
            for j in 0..n - i {
                let (x, y) = w.coeff.split_at_mut(1 << j);
                Self::sps_mul_t_slice(
                    &mut y[..1 << j],
                    &self.coeff[1 << j..2 << j],
                    &mut s[..1 << j],
                );
                y[..1 << j].fill(0);
                x.iter_mut().zip(&s).for_each(|(i, j)| *i += j);
            }
        }
        if a1 != 0 {
            c = (c * Self::exp_ax(a1, m)).mod_xn(m);
        }
        c.inv_borel()
    }
}

impl<const M: u64> Debug for Poly<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coeff)?;
        Ok(())
    }
}

impl<const M: u64> PartialEq for Poly<M> {
    fn eq(&self, other: &Self) -> bool {
        let d0 = self.deg();
        let d1 = other.deg();
        match (d0, d1) {
            (None, None) => true,
            (Some(d0), Some(d1)) => {
                if d0 != d1 {
                    return false;
                }
                for i in 0..=d0 {
                    if (self.coeff[i] - other.coeff[i]) % M as E != 0 {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl<const M: u64> Eq for Poly<M> {}

impl<const M: u64> Neg for Poly<M> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        self.coeff.iter_mut().for_each(|v| *v = -*v);
        self
    }
}

impl<const M: u64> Add<Self> for Poly<M> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += &rhs;
        self
    }
}

impl<const M: u64> Add<&Self> for Poly<M> {
    type Output = Self;

    fn add(mut self, rhs: &Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const M: u64> AddAssign<&Self> for Poly<M> {
    fn add_assign(&mut self, rhs: &Self) {
        let l = self.len().max(rhs.len());
        self.coeff.resize(l, 0);
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .for_each(|(a, b)| *a += b);
    }
}

impl<const M: u64> AddAssign<Self> for Poly<M> {
    fn add_assign(&mut self, rhs: Self) {
        *self += &rhs;
    }
}

impl<const M: u64> Sub<Self> for Poly<M> {
    type Output = Poly<M>;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const M: u64> SubAssign<&Self> for Poly<M> {
    fn sub_assign(&mut self, rhs: &Self) {
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .for_each(|(a, &b)| *a -= b);
    }
}

impl<const M: u64> SubAssign<Self> for Poly<M> {
    fn sub_assign(&mut self, rhs: Self) {
        *self -= &rhs;
    }
}

impl<const M: u64> Mul<Self> for Poly<M> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64> Mul<&Self> for Poly<M> {
    type Output = Self;

    fn mul(mut self, rhs: &Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64> MulAssign<&Self> for Poly<M> {
    fn mul_assign(&mut self, rhs: &Self) {
        let rhs = rhs.clone();
        *self *= rhs;
    }
}

impl<const M: u64> MulAssign<Self> for Poly<M> {
    fn mul_assign(&mut self, mut rhs: Self) {
        let n = self.coeff.len();
        let m = rhs.coeff.len();
        if n <= 400 || m <= 400 {
            let d0 = self.deg_or_0();
            let d1 = rhs.deg_or_0();
            let mut res = vec![0; d0 + d1 + 1];
            for j in 0..m {
                let a = rhs.coeff[j];
                res.iter_mut()
                    .skip(j)
                    .zip(&self.coeff)
                    .for_each(|(i, &j)| *i += a * j % M as E);
            }
            self.coeff = res;
        } else {
            ntt_conv::<M>(&mut self.coeff, &mut rhs.coeff);
        }
        self.coeff.iter_mut().for_each(|i| {
            *i %= M as E;
        });
    }
}

impl<const M: u64> AddAssign<E> for Poly<M> {
    fn add_assign(&mut self, rhs: E) {
        self.coeff[0] += rhs;
    }
}

impl<const M: u64> Add<E> for Poly<M> {
    type Output = Self;

    fn add(mut self, rhs: E) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const M: u64> SubAssign<E> for Poly<M> {
    fn sub_assign(&mut self, rhs: E) {
        self.coeff[0] -= rhs;
    }
}

impl<const M: u64> Sub<E> for Poly<M> {
    type Output = Self;

    fn sub(mut self, rhs: E) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const M: u64> MulAssign<E> for Poly<M> {
    fn mul_assign(&mut self, mut rhs: E) {
        if rhs == 1 {
            return;
        }
        rhs = rhs.rem_euclid(M as E);
        if (M as E) >> 1 < rhs {
            rhs -= M as E;
        }
        self.coeff.iter_mut().for_each(|i| *i *= rhs);
    }
}

impl<const M: u64> Mul<E> for Poly<M> {
    type Output = Self;

    fn mul(mut self, rhs: E) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64, T, S> Index<T> for Poly<M>
where
    Vec<E>: Index<T, Output = S>,
{
    type Output = S;

    fn index(&self, index: T) -> &Self::Output {
        &self.coeff[index]
    }
}

impl<const M: u64, T, S> IndexMut<T> for Poly<M>
where
    Vec<E>: IndexMut<T, Output = S>,
{
    fn index_mut(&mut self, index: T) -> &mut Self::Output {
        &mut self.coeff[index]
    }
}

impl<const M: u64> Div<Self> for &Poly<M> {
    type Output = Poly<M>;

    fn div(self, rhs: &Poly<M>) -> Self::Output {
        self.div_mod(rhs).0
    }
}

impl<const M: u64> Div<Self> for Poly<M> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(&rhs)
    }
}

impl<const M: u64> Div<&Self> for Poly<M> {
    type Output = Self;

    fn div(self, rhs: &Self) -> Self::Output {
        self.div_mod(rhs).0
    }
}

impl<const M: u64> DivAssign<E> for Poly<M> {
    fn div_assign(&mut self, rhs: E) {
        if rhs == 1 {
            return;
        }
        *self *= inv::<M>(rhs);
    }
}

impl<const M: u64> Div<E> for Poly<M> {
    type Output = Self;

    fn div(mut self, rhs: E) -> Self::Output {
        self /= rhs;
        self
    }
}

impl<const M: u64> DivAssign<&Self> for Poly<M> {
    fn div_assign(&mut self, rhs: &Self) {
        *self = self.div_mod(rhs).0;
    }
}

impl<const M: u64> DivAssign<Self> for Poly<M> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.div_mod(&rhs).0;
    }
}

impl<const M: u64> Rem<Self> for &Poly<M> {
    type Output = Poly<M>;

    fn rem(self, rhs: &Poly<M>) -> Self::Output {
        self.div_mod(rhs).1
    }
}

impl<const M: u64> Rem<Self> for Poly<M> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(&rhs)
    }
}

impl<const M: u64> Rem<&Self> for Poly<M> {
    type Output = Self;

    fn rem(self, rhs: &Self) -> Self::Output {
        self.div_mod(rhs).1
    }
}

impl<const M: u64> RemAssign<&Self> for Poly<M> {
    fn rem_assign(&mut self, rhs: &Self) {
        *self = self.div_mod(rhs).1;
    }
}

impl<const M: u64> RemAssign<Self> for Poly<M> {
    fn rem_assign(&mut self, rhs: Self) {
        *self = self.div_mod(&rhs).1;
    }
}

impl<const M: u64> ShrAssign<usize> for Poly<M> {
    fn shr_assign(&mut self, rhs: usize) {
        if rhs == 0 {
            return;
        }
        let l = self.coeff.len();
        if l <= rhs {
            self.coeff.clear();
            return;
        }
        for i in 0..l - rhs {
            self.coeff[i] = self.coeff[i + rhs];
        }
        self.coeff.truncate(l - rhs);
    }
}

impl<const M: u64> Shr<usize> for Poly<M> {
    type Output = Self;

    fn shr(mut self, rhs: usize) -> Self::Output {
        self >>= rhs;
        self
    }
}

impl<const M: u64> ShlAssign<usize> for Poly<M> {
    fn shl_assign(&mut self, rhs: usize) {
        if rhs == 0 {
            return;
        }
        let l = self.coeff.len();
        self.coeff.resize(l + rhs, 0);
        for i in (0..l).rev() {
            self.coeff[i + rhs] = self.coeff[i];
        }
        for i in 0..rhs {
            self.coeff[i] = 0;
        }
    }
}

impl<const M: u64> Shl<usize> for Poly<M> {
    type Output = Self;

    fn shl(mut self, rhs: usize) -> Self::Output {
        self <<= rhs;
        self
    }
}

// SECTION: mat

#[derive(Clone)]
pub struct Mat<const M: u64> {
    pub n: usize,
    pub m: usize,
    pub elems: Vec<E>,
}

impl<const M: u64> Mat<M> {
    #[inline]
    pub fn eye(n: usize, m: usize) -> Self {
        let mut elems = vec![0; n * m];
        for i in 0..n.min(m) {
            elems[(m + 1) * i] = 1;
        }
        Self { n, m, elems }
    }

    #[inline]
    pub fn from_elem(n: usize, m: usize, v: E) -> Self {
        Self {
            n,
            m,
            elems: vec![v; n * m],
        }
    }

    #[inline]
    pub fn from_fn(n: usize, m: usize, mut f: impl FnMut((usize, usize)) -> E) -> Self {
        let mut elems = vec![0; n * m];
        for i in 0..n {
            for j in 0..m {
                elems[i * m + j] = f((i, j));
            }
        }
        Self { n, m, elems }
    }

    #[inline]
    pub fn from_vec(n: usize, m: usize, s: Vec<E>) -> Self {
        Self { n, m, elems: s }
    }

    #[inline]
    pub fn from_slice(n: usize, m: usize, s: &[E]) -> Self {
        Self {
            n,
            m,
            elems: s.to_vec(),
        }
    }

    #[inline]
    pub fn block_diag(blocks: Vec<Self>) -> Self {
        let mut n = 0;
        let mut m = 0;
        for i in 0..blocks.len() {
            n += blocks[i].n;
            m += blocks[i].m;
        }
        let mut s = Self::from_elem(n, m, 0);
        let mut a = 0;
        let mut b = 0;
        for i in 0..blocks.len() {
            for j in 0..blocks[i].n {
                s[a][b..b + blocks[i].m].copy_from_slice(&blocks[i][j]);
                a += 1;
            }
            b += blocks[i].m;
        }
        s
    }

    #[inline]
    pub fn elements(&self) -> impl Iterator<Item = &E> {
        self.elems.iter()
    }

    #[inline]
    pub fn elements_mut(&mut self) -> impl Iterator<Item = &mut E> {
        self.elems.iter_mut()
    }

    #[inline]
    pub fn enumerate_elements(&self) -> impl Iterator<Item = (usize, usize, &E)> {
        self.elems
            .iter()
            .enumerate()
            .map(|(i, v)| (i / self.m, i % self.m, v))
    }

    #[inline]
    pub fn enumerate_elements_mut(&mut self) -> impl Iterator<Item = (usize, usize, &mut E)> {
        self.elems
            .iter_mut()
            .enumerate()
            .map(|(i, v)| (i / self.m, i % self.m, v))
    }

    #[inline]
    pub fn col(&self, i: usize) -> impl Iterator<Item = &E> {
        self.elems.iter().skip(i).step_by(self.n)
    }

    #[inline]
    pub fn col_mut(&mut self, i: usize) -> impl Iterator<Item = &mut E> {
        self.elems.iter_mut().skip(i).step_by(self.n)
    }

    #[inline]
    pub fn transpose(&mut self) -> Self {
        Self::from_fn(self.m, self.n, |(i, j)| self[(j, i)])
    }

    #[inline]
    pub fn resize_rows(&mut self, n: usize) -> &mut Self {
        self.elems.resize(self.m * n, 0);
        self.n = n;
        self
    }

    #[inline]
    pub fn resize_cols(&mut self, m: usize) -> &mut Self {
        if m == self.m {
            return self;
        }
        if m < self.m {
            let mut write_idx = 0;
            for row in 0..self.n {
                let row_start = row * self.m;
                for col in 0..m {
                    self.elems[write_idx] = self.elems[row_start + col];
                    write_idx += 1;
                }
            }
            self.elems.truncate(self.n * m);
        } else {
            self.elems.resize(self.n * m, 0);
            for i in (0..self.n).rev() {
                for j in (0..self.m).rev() {
                    self.elems[i * m + j] = self.elems[i * self.m + j];
                }
                for j in self.m..m {
                    self.elems[i * m + j] = 0;
                }
            }
        }
        self.m = m;
        self
    }

    #[inline]
    pub fn concat_rows(&self, rhs: &Self) -> Self {
        if self.m == 0 {
            return Self {
                n: self.n,
                m: rhs.m,
                elems: rhs.elems.clone(),
            };
        }
        if rhs.m == 0 {
            return Self {
                n: self.n,
                m: self.m,
                elems: self.elems.clone(),
            };
        }
        Self {
            n: self.n,
            m: self.m + rhs.m,
            elems: self
                .elems
                .chunks(self.m)
                .zip(rhs.elems.chunks(rhs.m)) // Use zip instead of interleave
                .flat_map(|(left_chunk, right_chunk)| left_chunk.iter().chain(right_chunk.iter()))
                .cloned()
                .collect::<Vec<_>>(),
        }
    }

    #[inline]
    pub fn concat_cols(&mut self, rhs: &Self) -> &mut Self {
        self.elems.extend_from_slice(&rhs.elems);
        self.n += rhs.n;
        self
    }

    #[inline]
    pub fn normalize(&mut self) -> &mut Self {
        self.elements_mut().for_each(|v| *v %= M as E);
        self
    }

    #[inline]
    pub fn pos_normalize(&mut self) -> &mut Self {
        self.elements_mut().for_each(|v| *v = v.rem_euclid(M as E));
        self
    }

    #[inline]
    pub fn neg_normalize(&mut self) -> &mut Self {
        self.elements_mut().for_each(|i| {
            *i = i.rem_euclid(M as E);
            if (M as E) >> 1 < *i {
                *i -= M as E;
            }
        });
        self
    }

    #[inline]
    pub fn normalize_row(&mut self, i: usize) -> &mut Self {
        self[i].iter_mut().for_each(|v| *v %= M as E);
        self
    }

    #[inline]
    pub fn normalize_col(&mut self, i: usize) -> &mut Self {
        self.col_mut(i).for_each(|v| *v %= M as E);
        self
    }

    #[inline]
    pub fn negate(&mut self) -> &mut Self {
        self.elements_mut().for_each(|v| *v = -*v);
        self
    }

    #[inline]
    pub fn apply(&self, rhs: &[E]) -> Vec<E> {
        let mut r = Vec::with_capacity(self.n);
        for i in 0..self.n {
            let p = self[i]
                .iter()
                .zip(rhs)
                .fold(0, |acc, (&x, y)| (acc + x * y) % M as E);
            r.push(p);
        }
        r
    }

    #[inline]
    pub fn apply_t(&self, rhs: &[E]) -> Vec<E> {
        let mut r = vec![0; self.m];
        for i in 0..self.n {
            let v = rhs[i] % M as E;
            r.iter_mut()
                .zip(&self[i])
                .for_each(|(i, j)| *i = (*i + v * *j) % M as E);
        }
        r
    }

    #[inline]
    pub fn pow(self, mut rhs: usize) -> Self {
        if rhs <= 1 << 3 || (self.n <= 1 << 5 && rhs <= 1 << 5) {
            let mut res = Self::eye(self.n, self.m);
            let mut a = self;
            while rhs != 0 {
                if rhs & 1 != 0 {
                    res = &res * &a;
                }
                a = &a * &a;
                rhs >>= 1;
            }
            res
        } else {
            self.with_frob(|charp| charp.clone().xi_mod(rhs))
        }
    }

    #[inline]
    pub fn diamond(&self, rhs: &Self) -> Self {
        let mut c = Self::from_elem(self.n, rhs.m, 0);
        for i in 0..self.n {
            let row_a = &self[i];
            let row_c = &mut c[i];
            for k in 0..self.m {
                let a_ik = row_a[k];
                row_c
                    .iter_mut()
                    .zip(rhs[k].iter().map(|j| a_ik + j))
                    .for_each(|(i, j)| *i = (*i).max(j));
            }
        }
        c
    }

    pub fn reduce_by(a: &mut [E], b: &[E]) {
        if let Some(piv) = b.iter().position(|&i| i != 0) {
            let mut scale = a[piv] % M as E * inv::<M>(b[piv]);
            scale = scale.rem_euclid(M as E);
            if (M as E) >> 1 < scale {
                scale -= M as E;
            }
            a.iter_mut()
                .zip(b)
                .for_each(|(i, &j)| *i = (*i - j * scale) % M as E);
        }
    }

    pub fn add_scaled(a: &mut [E], b: &[E], mut scale: E) {
        scale = scale.rem_euclid(M as E);
        if (M as E) >> 1 < scale {
            scale -= M as E;
        }
        a.iter_mut()
            .zip(b)
            .for_each(|(i, &j)| *i = (*i + j * scale) % M as E);
    }

    pub fn gauss<const MODE: u8>(&mut self) -> &mut Self {
        for i in 0..self.n {
            let row_i = &mut self[i];
            row_i.iter_mut().for_each(|v| *v %= M as E);
            let p = row_i.iter().position(|&v| v != 0);
            if let Some(p) = p {
                let p_inv = inverse_euclidean::<M, _>(self[(i, p)] as i64) as E;
                for j in if MODE == 1 { 0 } else { i + 1 }..self.n {
                    if MODE == 1 && j == i {
                        continue;
                    }
                    let [row_i, row_j] = self
                        .elems
                        .get_disjoint_mut([
                            i * self.m..(i + 1) * self.m,
                            j * self.m..(j + 1) * self.m,
                        ])
                        .unwrap();
                    let a = (row_j[p] % M as E * (p_inv % M as E)) % M as E;
                    row_j
                        .iter_mut()
                        .zip(row_i.iter().map(|&j| M as E - (a * j % M as E) as E))
                        .skip(p)
                        .for_each(|(i, j)| *i += j);
                    row_j.iter_mut().skip(p).for_each(|i| *i %= M as E);
                }
            }
        }
        self
    }

    pub fn sort_classify(
        &mut self,
        lim: usize,
        mut f: impl FnMut(usize),
        mut g: impl FnMut(usize),
    ) -> &mut Self {
        let mut rk = 0;
        for j in 0..lim {
            if rk < self.n && self[rk][j] % M as E == 0 {
                for i in rk + 1..self.n {
                    if self[i][j] % M as E != 0 {
                        let [row_i, row_rk] = self
                            .elems
                            .get_disjoint_mut([
                                i * self.m..(i + 1) * self.m,
                                rk * self.m..(rk + 1) * self.m,
                            ])
                            .unwrap();
                        row_i.swap_with_slice(row_rk);
                        row_rk.iter_mut().for_each(|i| *i = -*i);
                        break;
                    }
                }
            }
            if rk < self.n && self[rk][j] % M as E != 0 {
                f(j);
                rk += 1;
            } else {
                g(j);
            }
        }
        self
    }

    pub fn echelonize_lim<const MODE: u8>(
        &mut self,
        lim: usize,
        f: impl FnMut(usize),
        g: impl FnMut(usize),
    ) -> &mut Self {
        self.gauss::<MODE>();
        self.sort_classify(lim, f, g);
        self
    }

    pub fn echelonize<const MODE: u8>(
        &mut self,
        f: impl FnMut(usize),
        g: impl FnMut(usize),
    ) -> &mut Self {
        self.gauss::<MODE>();
        self.sort_classify(self.m, f, g);
        self
    }

    pub fn rank(&mut self, mut f: impl FnMut(usize), g: impl FnMut(usize)) -> usize {
        let mut a = self.clone();
        let mut rk = 0;
        a.echelonize::<0>(
            |i| {
                rk += 1;
                f(i);
            },
            g,
        );
        rk
    }

    pub fn det(&self, f: impl FnMut(usize), g: impl FnMut(usize)) -> E {
        let mut a = self.clone();
        a.echelonize::<0>(f, g);
        let mut res = 1;
        for i in 0..self.n {
            res *= a[i][i];
            res %= M as E;
        }
        res
    }

    pub fn inv(&self, mut f: impl FnMut(usize), g: impl FnMut(usize)) -> (E, usize, Self) {
        let n = self.n;
        let mut a = self.concat_rows(&Self::eye(n, n));
        let mut rk = 0;
        a.echelonize::<1>(
            |i| {
                if i < n {
                    rk += 1;
                }
                f(i);
            },
            g,
        );
        if rk < n {
            return (
                0,
                rk,
                Self {
                    n: 0,
                    m: 0,
                    elems: vec![],
                },
            );
        }
        let mut det = 1;
        for i in 0..n {
            let a_ii = a[i][i] % M as E;
            det *= a_ii;
            det %= M as E;
            let a_ii_inv = inverse_euclidean::<M, _>(a_ii as i64) as E;
            let row_i = &mut a[i];
            row_i.iter_mut().for_each(|i| *i %= M as E);
            row_i.iter_mut().for_each(|i| *i *= a_ii_inv);
        }
        let mut counter = 0;
        let mut inv = Self {
            n: self.n,
            m: self.m,
            elems: a
                .elems
                .into_iter()
                .chunks(self.m)
                .into_iter()
                .filter(|_| {
                    counter ^= 1;
                    counter == 0
                })
                .flatten()
                .collect::<Vec<_>>(),
        };
        inv.normalize();
        (det, rk, inv)
    }

    pub fn ker(&self, mut f: impl FnMut(usize), mut g: impl FnMut(usize)) -> Self {
        let mut a = self.clone();
        let mut pivots = Vec::with_capacity(a.m);
        let mut free = Vec::with_capacity(a.m);
        a.echelonize::<1>(
            |i| {
                pivots.push(i);
                f(i)
            },
            |j| {
                free.push(j);
                g(j)
            },
        );
        let mut sols = Self::from_elem(free.len(), a.m, 0);
        for j in 0..pivots.len() {
            let b = inverse_euclidean::<M, _>(a[(j, pivots[j])] as i64) as E;
            for i in 0..free.len() {
                sols[(i, pivots[j])] = (a[(j, free[i])] * b) % M as E;
            }
        }
        for i in 0..free.len() {
            sols[(i, free[i])] = M as E - 1;
        }
        sols
    }

    pub fn solve(&self, t: &Self, f: impl FnMut(usize), g: impl FnMut(usize)) -> Option<[Self; 2]> {
        let a = self.concat_rows(t);
        let sols = a.ker(f, g);
        if sols.n < t.m {
            return None;
        }
        for i in 0..t.m {
            for j in 0..t.m {
                if sols[(sols.n - t.m + i, self.m + j)] % M as E
                    != if i == j { M as E - 1 } else { 0 }
                {
                    return None;
                }
            }
        }
        let mut x_t = Self::from_elem(t.m, self.m, 0);
        for i in 0..t.m {
            x_t[i]
                .iter_mut()
                .zip(&sols[sols.n - t.m + i])
                .for_each(|(i, &j)| *i = j);
        }
        let mut ker = Self::from_elem(sols.n - t.m, self.m, 0);
        for i in 0..sols.n - t.m {
            ker[i].iter_mut().zip(&sols[i]).for_each(|(i, &j)| *i = j);
        }
        Some([x_t, ker])
    }

    pub fn minp(&self) -> Poly<M> {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        let mut basis: Vec<Vec<E>> = Vec::with_capacity(n);
        let mut rng = rand::rng();
        let start = basis.len();
        let mut gen_block = |mut x: Vec<E>| {
            loop {
                let mut y = x.clone();
                let l = y.len();
                y.resize(l + basis.len() + 1, 0);
                y[l + basis.len()] = 1;
                for v in &basis {
                    Mat::<M>::reduce_by(&mut y, &v);
                }
                y.iter_mut().for_each(|i| *i %= M as E);
                if y.iter().take(n).position(|&i| i != 0).unwrap_or(n) == n {
                    return Poly::<M>::new(y[n..].to_vec());
                } else {
                    basis.push(y);
                    x = self.apply_t(&x);
                }
            }
        };
        let full_rec = gen_block((0..n).map(|_| rng.random()).collect());
        full_rec >> start
    }

    pub fn charps(&self) -> Vec<Poly<M>> {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        let mut charps: Vec<Poly<M>> = Vec::new();
        let mut basis: Vec<Vec<E>> = Vec::with_capacity(n);
        let mut rng = rand::rng();
        while basis.len() < n {
            let start = basis.len();
            let mut gen_block = |mut x: Vec<E>| {
                loop {
                    let mut y = x.clone();
                    let l = y.len();
                    y.resize(l + basis.len() + 1, 0);
                    y[l + basis.len()] = 1;
                    for v in &basis {
                        Mat::<M>::reduce_by(&mut y, &v);
                    }
                    y.iter_mut().for_each(|i| *i %= M as E);
                    if y.iter().take(n).position(|&i| i != 0).unwrap_or(n) == n {
                        return Poly::<M>::new(y[n..].to_vec());
                    } else {
                        basis.push(y);
                        x = self.apply_t(&x);
                    }
                }
            };
            let full_rec = gen_block((0..n).map(|_| rng.random()).collect());
            charps.push(full_rec >> start);
        }
        charps
    }

    pub fn frob(&self) -> (Vec<Poly<M>>, Self, Self) {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        let mut charps: Vec<Poly<M>> = Vec::new();
        let (mut basis, mut basis_init): (Vec<Vec<E>>, Vec<Vec<E>>) =
            (Vec::with_capacity(n), Vec::with_capacity(n));
        fn gen_block<const M: u64>(
            mut x: Vec<E>,
            a: &Mat<M>,
            basis: &mut Vec<Vec<E>>,
            basis_init: &mut Vec<Vec<E>>,
            n: usize,
        ) -> Poly<M> {
            loop {
                let mut y = x.clone();
                let l = y.len();
                y.resize(l + n + 1, 0);
                y[l + basis.len()] = 1;
                for v in &*basis {
                    Mat::<M>::reduce_by(&mut y, &v);
                }
                y.iter_mut().for_each(|i| *i %= M as E);
                if y.iter().take(n).position(|&i| i != 0).unwrap_or(n) == n {
                    return Poly::<M>::new(y[n..].to_vec());
                } else {
                    basis_init.push(x.clone());
                    basis.push(y);
                    x = a.apply_t(&x);
                }
            }
        }
        let mut rng = rand::rng();
        while basis.len() < n {
            let start = basis.len();
            let mut full_rec = gen_block(
                (0..n).map(|_| rng.random_range(1..M as E)).collect(),
                self,
                &mut basis,
                &mut basis_init,
                n,
            );
            if !full_rec.clone().mod_xn(start).is_zero() {
                let charp = full_rec.clone() >> start;
                let mut x = std::mem::take(&mut basis_init[start]);
                let shift = (full_rec / charp).normalize();
                for j in 0..shift.deg_or_0() {
                    Self::add_scaled(&mut x, &basis_init[j], shift[j]);
                }
                basis.truncate(start);
                basis_init.truncate(start);
                full_rec = gen_block(x, self, &mut basis, &mut basis_init, n);
            }
            charps.push(full_rec >> start);
        }
        for i in 0..n {
            for j in i + 1..n {
                let [b_i, b_j] = unsafe { basis.get_disjoint_unchecked_mut([i, j]) };
                Self::reduce_by(b_i, &*b_j);
            }
            basis[i].iter_mut().for_each(|i| *i %= M as E);
        }
        let t = Self::from_vec(n, n, basis_init.iter().flatten().cloned().collect());
        let mut t_inv = Self::from_elem(n, (n << 1) + 1, 0);
        for i in 0..n {
            for j in 0..basis[i].len() {
                t_inv[(i, j)] = basis[i][j];
            }
        }
        t_inv.sort_classify(n, |_| {}, |_| {});
        let mut t_inv_p = Vec::with_capacity(n * n);
        for i in 0..n {
            let mut r = t_inv[i][n..n << 1].to_vec();
            let scale = inv::<M>(t_inv[(i, i)]);
            r.iter_mut().for_each(|i| *i = *i * scale % M as E);
            t_inv_p.extend(r);
        }
        t_inv = Self::from_vec(n, n, t_inv_p);
        (charps, t, t_inv)
    }

    pub fn with_frob(&self, mut f: impl FnMut(&Poly<M>) -> Poly<M>) -> Self {
        let (charps, t, t_inv) = self.frob();
        let mut blocks = Vec::new();
        for charp in charps {
            let charp_deg = charp.deg_or_0();
            let mut block = Self::from_elem(charp_deg, charp_deg, 0);
            let mut f_charp = f(&charp);
            for i in 0..charp_deg {
                let l = block[i].len().min(f_charp.coeff.len());
                block[i][..l].copy_from_slice(&f_charp.coeff[..l]);
                f_charp = (f_charp << 1) % &charp;
            }
            blocks.push(block);
        }
        let s = Self::block_diag(blocks);
        t_inv * s * t
    }
}

impl<const M: u64> Debug for Mat<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}×{} matrix mod {}:", self.n, self.m, M)?;
        for i in 0..self.n {
            writeln!(f, "{:?}", &self[i])?;
        }
        Ok(())
    }
}

impl<const M: u64> Index<usize> for Mat<M> {
    type Output = [E];

    fn index(&self, i: usize) -> &Self::Output {
        &self.elems[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: u64> IndexMut<usize> for Mat<M> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.elems[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: u64> Index<(usize, usize)> for Mat<M> {
    type Output = E;

    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.elems[i * self.m + j]
    }
}

impl<const M: u64> IndexMut<(usize, usize)> for Mat<M> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.elems[i * self.m + j]
    }
}

impl<const M: u64> PartialEq for Mat<M> {
    fn eq(&self, other: &Self) -> bool {
        for (a, b) in self.elements().zip(other.elements()) {
            if (a - b) % M as E != 0 {
                return false;
            }
        }
        true
    }
}

impl<const M: u64> Eq for Mat<M> {}

impl<const M: u64> AddAssign for Mat<M> {
    fn add_assign(&mut self, rhs: Self) {
        self.elements_mut()
            .zip(rhs.elements())
            .for_each(|(v, w)| *v += w);
    }
}

impl<const M: u64> SubAssign for Mat<M> {
    fn sub_assign(&mut self, rhs: Self) {
        self.elements_mut().zip(rhs.elements()).for_each(|(v, w)| {
            *v -= w;
        });
    }
}

impl<'a, const M: u64> Mul<&'a Mat<M>> for &'a Mat<M> {
    type Output = Mat<M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut c = vec![0_i128; self.n * rhs.m];
        for i in 0..self.n {
            let row_a = &self[i];
            let row_c = &mut c[i * rhs.m..(i + 1) * rhs.m];
            for k in 0..self.m {
                let a_ik = row_a[k];
                row_c
                    .iter_mut()
                    .zip(&rhs[k])
                    .for_each(|(i, &j)| *i += (a_ik * j % M as E) as i128);
            }
        }
        Mat::from_slice(
            self.n,
            rhs.m,
            &c.into_iter()
                .map(|i| (i % M as i128) as E)
                .collect::<Vec<_>>(),
        )
    }
}

impl<const M: u64> Mul<Mat<M>> for &Mat<M> {
    type Output = Mat<M>;

    fn mul(self, rhs: Mat<M>) -> Self::Output {
        self * &rhs
    }
}

impl<const M: u64> Mul<Self> for Mat<M> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        &self * &rhs
    }
}

impl<const M: u64> Mul<&Self> for Mat<M> {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self::Output {
        &self * rhs
    }
}

type B = u128;

#[derive(Clone)]
pub struct XorBasis {
    pub basis: [B; B::BITS as usize],
    pub mask: B,
}

impl XorBasis {
    pub fn new() -> XorBasis {
        Self {
            basis: [0; B::BITS as usize],
            mask: 0,
        }
    }

    pub fn size(&self) -> u32 {
        self.mask.count_ones()
    }

    pub fn span_size(&self) -> B {
        1 << self.size()
    }

    pub fn ker_size(&self, at: u32) -> B {
        1 << (at - self.size())
    }

    pub fn eliminate(&mut self) -> &mut Self {
        for i in (0..B::BITS as usize).rev() {
            if self.mask & 1 << i == 0 {
                continue;
            }
            for j in i + 1..B::BITS as usize {
                if self.mask & 1 << j != 0 && self.basis[j] & 1 << i != 0 {
                    self.basis[j] ^= self.basis[i];
                }
            }
        }
        self
    }

    pub fn max_span(&self) -> B {
        let mut m = 0;
        for i in (0..B::BITS as usize).rev() {
            if self.mask & 1 << i != 0 && m & 1 << i == 0 {
                m ^= self.basis[i];
            }
        }
        m
    }

    pub fn min_span(&self) -> B {
        let mut m = 0;
        for i in (0..B::BITS as usize).rev() {
            if self.mask & 1 << i != 0 && m & 1 << i != 0 {
                m ^= self.basis[i];
            }
        }
        m
    }

    pub fn kth_span(&self, mut k: B) -> B {
        let mut m = 0;
        let mut tot = self.span_size();
        for i in (0..B::BITS as usize).rev() {
            if self.mask & 1 << i != 0 {
                let low = tot / 2;
                if (low <= k && m & 1 << i == 0) || (low > k && (m & 1 << i != 0)) {
                    m ^= self.basis[i];
                }
                if low <= k {
                    k -= low;
                }
                tot >>= 1;
            }
        }
        m
    }

    pub fn span(&self) -> Vec<usize> {
        let mut span = Vec::with_capacity(self.span_size() as usize);
        span.push(0);
        for i in 0..B::BITS {
            if self.mask & 1 << i != 0 {
                for j in 0..span.len() {
                    let s = span[j];
                    span.push(s | 1 << i);
                }
            }
        }
        span
    }
}

// SECTION: flow

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<F> {
    pub to: usize,
    pub rev: usize,
    pub f: F,
    pub c: F,
}

pub struct PushRelabel<F> {
    pub n: usize,
    pub g: Vec<Vec<Edge<F>>>,
    pub ec: Vec<F>,
    pub cur: Vec<usize>,
    pub hs: Vec<Vec<usize>>,
    pub h: Vec<usize>,
    pub co: Vec<usize>,
}

impl<F: Copy + Default + Ord + AddAssign + SubAssign> PushRelabel<F> {
    #[inline]
    pub fn new(n: usize) -> Self {
        Self {
            n,
            g: vec![Vec::new(); n],
            ec: vec![F::default(); n],
            cur: vec![0; n],
            hs: vec![Vec::new(); 2 * n],
            h: vec![0; n],
            co: vec![0; 2 * n],
        }
    }

    #[inline]
    pub fn reset(&mut self) -> &mut Self {
        self.ec.fill(F::default());
        self.cur.fill(0);
        self.hs.iter_mut().for_each(Vec::clear);
        self.h.fill(0);
        self.co.fill(0);
        self.g.iter_mut().flatten().for_each(|Edge { f, c, .. }| {
            *c += *f;
            *f = F::default();
        });
        self
    }

    #[inline]
    pub fn full_reset(&mut self) -> &mut Self {
        self.g.iter_mut().for_each(Vec::clear);
        self.ec.fill(F::default());
        self.cur.fill(0);
        self.hs.iter_mut().for_each(Vec::clear);
        self.h.fill(0);
        self.co.fill(0);
        self
    }

    #[inline]
    pub fn add_edge(&mut self, s: usize, t: usize, cap: F, rcap: F) -> &mut Self {
        if s == t {
            return self;
        }
        let back_s = self.g[t].len();
        let back_t = self.g[s].len();
        self.g[s].push(Edge {
            to: t,
            rev: back_s,
            f: F::default(),
            c: cap,
        });
        self.g[t].push(Edge {
            to: s,
            rev: back_t,
            f: F::default(),
            c: rcap,
        });
        self
    }

    fn push(&mut self, u: usize, ei: usize, f: F, t: usize) -> &mut Self {
        let v = self.g[u][ei].to;
        let back_idx = self.g[u][ei].rev;
        if v != t && self.ec[v] == F::default() && f > F::default() {
            self.hs[self.h[v]].push(v);
        }
        let e = &mut self.g[u][ei];
        e.f += f;
        e.c -= f;
        self.ec[v] += f;
        let be = &mut self.g[v][back_idx];
        be.f -= f;
        be.c += f;
        self.ec[be.to] -= f;
        self
    }

    #[inline]
    fn relabel(&mut self, u: usize, hi: usize) -> usize {
        let n = self.n;
        let mut nh = usize::MAX;
        let mut nc = 0;
        let ws = &self.g[u];
        for i in 0..self.g[u].len() {
            let Edge { to: w, c, .. } = ws[i];
            let cand = self.h[w] + 1;
            if c > F::default() && cand < nh {
                nh = cand;
                nc = i;
            }
        }
        self.h[u] = nh;
        self.cur[u] = nc;
        self.co[nh] += 1;
        self.co[hi] -= 1;
        if hi < n && self.co[hi] == 0 {
            for i in 0..n {
                if self.h[i] > hi && self.h[i] < n {
                    self.co[self.h[i]] = 0;
                    self.h[i] = n + 1;
                }
            }
        }
        return self.h[u];
    }

    /// O(V^2 √E)
    pub fn calc(&mut self, s: usize, t: usize) -> F {
        if s == t {
            return F::default();
        }
        let n = self.n;
        self.h[s] = n;
        self.co[0] = n - 1;
        for ei in 0..self.g[s].len() {
            let cap = self.g[s][ei].c;
            if cap > F::default() {
                self.push(s, ei, cap, t);
            }
        }
        let mut hi = 0;
        loop {
            while self.hs[hi].is_empty() {
                if hi == 0 {
                    return self.ec[t];
                }
                hi -= 1;
            }
            let u = unsafe { self.hs[hi].pop().unwrap_unchecked() };
            while self.ec[u] > F::default() {
                if self.cur[u] == self.g[u].len() {
                    hi = self.relabel(u, hi);
                } else {
                    let i = self.cur[u];
                    let Edge { to: w, c, .. } = self.g[u][i];
                    if c > F::default() && self.h[u] == self.h[w] + 1 {
                        self.push(u, i, self.ec[u].min(c), t);
                    } else {
                        self.cur[u] += 1;
                    }
                }
            }
        }
    }

    pub fn left_of_min_cut(&self, a: usize) -> bool {
        self.h[a] >= self.n
    }

    pub fn flows(&self) -> Vec<(usize, usize, F)> {
        self.g
            .iter()
            .enumerate()
            .flat_map(|(u, edges)| {
                edges
                    .iter()
                    .filter(|e| e.f > F::default())
                    .map(move |e| (u, e.to, e.f))
            })
            .collect()
    }
}

// SECTION: bitvec

#[derive(Debug, Clone, PartialEq)]
pub struct BitVec {
    pub storage: Vec<u32>,
    pub len: usize,
}

impl BitVec {
    pub fn new(n: usize, initial_value: bool) -> Self {
        let blocks = (n + 31) / 32;

        let fill_value = if initial_value { u32::MAX } else { 0 };

        BitVec {
            storage: vec![fill_value; blocks],
            len: n,
        }
    }

    pub fn from_fn<F>(n: usize, mut f: F) -> Self
    where
        F: FnMut(usize) -> bool,
    {
        let mut bv = BitVec::new(n, false);
        for i in 0..n {
            if f(i) {
                bv.set(i, true);
            }
        }
        bv
    }

    pub fn get(&self, index: usize) -> bool {
        if index >= self.len {
            panic!(
                "BitVec index out of bounds: index {}, len {}",
                index, self.len
            );
        }

        let block_idx = index / 32;
        let bit_idx = index % 32;

        let block = self.storage[block_idx];
        let is_set = (block & (1 << bit_idx)) != 0;

        is_set
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if index >= self.len {
            panic!(
                "BitVec index out of bounds: index {}, len {}",
                index, self.len
            );
        }

        let block_idx = index / 32;
        let bit_idx = index % 32;
        let mask = 1 << bit_idx;

        if value {
            self.storage[block_idx] |= mask;
        } else {
            self.storage[block_idx] &= !mask;
        }
    }

    pub fn push(&mut self, value: bool) {
        let block_idx = self.len / 32;
        let bit_idx = self.len % 32;

        if block_idx == self.storage.len() {
            self.storage.push(0);
        }

        let mask = 1 << bit_idx;
        if value {
            self.storage[block_idx] |= mask;
        } else {
            self.storage[block_idx] &= !mask;
        }

        self.len += 1;
    }

    pub fn negate(&mut self) {
        let n = self.storage.len();
        self.storage[..n - 1]
            .iter_mut()
            .for_each(|a| *a ^= u32::MAX);
        self.storage[n - 1] ^= (1 << self.len() % 32) - 1;
    }

    pub fn fill(&mut self, value: bool) {
        let fill_value = if value { u32::MAX } else { 0 };
        self.storage.fill(fill_value);
    }

    pub fn clear(&mut self) {
        self.fill(false);
    }

    pub fn iter(&'_ self) -> BitVecIter<'_> {
        BitVecIter { bv: self, pos: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl Index<usize> for BitVec {
    type Output = bool;

    fn index(&self, i: usize) -> &Self::Output {
        if self.get(i) { &true } else { &false }
    }
}

pub struct BitVecIter<'a> {
    bv: &'a BitVec,
    pos: usize,
}

impl<'a> Iterator for BitVecIter<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.bv.len {
            let bit = self.bv.get(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }
}

// SECTION: monotone

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MonotoneStack<T, F: FnMut(&T, &T) -> bool> {
    pub stk: Vec<(T, T)>,
    pub min: Option<T>,
    pub cmp: F,
}

impl<T: Clone, F: FnMut(&T, &T) -> bool> MonotoneStack<T, F> {
    pub fn new(cmp: F) -> Self {
        Self {
            stk: Vec::new(),
            min: None,
            cmp,
        }
    }

    pub fn with_capacity(n: usize, cmp: F) -> Self {
        Self {
            stk: Vec::with_capacity(n),
            min: None,
            cmp,
        }
    }

    pub fn push(&mut self, value: T) -> &mut Self {
        let new_min = if self.min.is_none() || (self.cmp)(&value, self.min.as_ref().unwrap()) {
            self.min = Some(value.clone());
            value.clone()
        } else {
            self.min.clone().unwrap()
        };
        self.stk.push((value, new_min));
        self
    }

    pub fn pop(&mut self) -> Option<T> {
        self.stk.pop().map(|v| v.0)
    }

    pub fn min(&self) -> Option<T> {
        self.stk.last().map(|v| v.1.clone())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MonotoneQueue<T, F: FnMut(&T, &T) -> bool> {
    pub q: VecDeque<T>,
    pub cmp: F,
}

impl<T: PartialEq, F: FnMut(&T, &T) -> bool> MonotoneQueue<T, F> {
    pub fn new(cmp: F) -> Self {
        Self {
            q: VecDeque::new(),
            cmp,
        }
    }

    pub fn with_capacity(n: usize, cmp: F) -> Self {
        Self {
            q: VecDeque::with_capacity(n),
            cmp,
        }
    }

    pub fn push_back(&mut self, value: T) -> &mut Self {
        while !self.q.is_empty() && (self.cmp)(&value, self.q.back().unwrap()) {
            self.q.pop_back();
        }
        self.q.push_back(value);
        self
    }

    pub fn pop_front(&mut self, value: &T) -> &mut Self {
        if !self.q.is_empty() && self.q.front().unwrap() == value {
            self.q.pop_front();
        }
        self
    }

    pub fn min(&self) -> Option<&T> {
        self.q.front()
    }
}

// SECTION: sort

/// counting sort O(n + k) time O(k) space
/// k must be a strict upper bound
pub fn counting_sort(a: &mut [usize], k: usize) -> &mut [usize] {
    let mut counts = vec![0; k];
    for &x in &*a {
        counts[x] += 1;
    }
    let mut i = 0;
    for v in 0..k {
        let c = counts[v];
        for _ in 0..c {
            a[i] = v;
            i += 1;
        }
    }
    a
}

/// counting sort with dedup O(n + k) time O(k) space
/// k must be a strict upper bound
pub fn counting_sort_dedup(a: &mut [usize], k: usize) -> usize {
    let mut seen = BitVec::new(k, false);
    for &x in &*a {
        seen.set(x, true);
    }
    let mut i = 0;
    for v in 0..k {
        if seen[v] {
            a[i] = v;
            i += 1;
        }
    }
    i
}

/// counting sort deduped by key O(n + k) time O(k) space
pub fn counting_sort_dedup_by_key<T: Clone, F: Fn(&T) -> usize>(
    a: &mut [T],
    k: usize,
    key: F,
) -> usize {
    let mut seen = BitVec::new(k, false);
    let mut repr: Vec<Option<T>> = vec![None; k];
    for x in a.iter() {
        let v = key(x);
        if !seen[v] {
            seen.set(v, true);
            repr[v] = Some(x.clone());
        }
    }
    let mut i = 0;
    for v in 0..k {
        if seen[v] {
            a[i] = repr[v].take().unwrap();
            i += 1;
        }
    }
    i
}

// SECTION: dsu

pub struct DSU {
    pub p: Vec<isize>,
}

impl DSU {
    pub fn new(n: usize) -> Self {
        Self { p: vec![-1; n] }
    }

    pub fn find(&mut self, mut x: usize) -> usize {
        while self.p[x] >= 0 {
            let p = self.p[x] as usize;
            if self.p[p] >= 0 {
                self.p[x] = self.p[p];
            }
            x = p;
        }
        x
    }

    pub fn same(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn union(&mut self, x: usize, y: usize) -> (bool, usize) {
        let mut i = self.find(x);
        let mut j = self.find(y);
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (false, i);
        }
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        (true, i)
    }

    pub fn union_root(&mut self, x: usize, mut r: usize) -> (bool, usize) {
        let mut i = self.find(x);
        if i == r {
            return (false, r);
        }
        if self.p[i] > self.p[r] {
            (i, r) = (r, i);
        }
        self.p[i] += self.p[r];
        self.p[r] = i as isize;
        (true, i)
    }

    pub fn size(&mut self, x: usize) -> usize {
        let r = self.find(x);
        (-self.p[r]) as usize
    }
}

impl Debug for DSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self.p))
    }
}

impl<Idx, T> Index<Idx> for DSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for DSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}

pub struct RollbackDSU {
    pub p: Vec<isize>,
    pub joins: Vec<(usize, isize)>,
}

impl RollbackDSU {
    pub fn new(n: usize) -> Self {
        Self {
            p: vec![-1; n],
            joins: Vec::new(),
        }
    }

    pub fn find(&self, mut i: usize) -> usize {
        while self.p[i] >= 0 {
            i = self.p[i] as usize;
        }
        i
    }

    pub fn same(&self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn size(&self, x: usize) -> usize {
        (-self.p[self.find(x)]) as usize
    }

    pub fn union(&mut self, x: usize, y: usize) -> (bool, usize) {
        let (mut i, mut j) = (self.find(x), self.find(y));
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (false, i);
        }
        self.joins.push((j, self.p[j]));
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        return (true, i);
    }

    pub fn rollback(&mut self, t: usize) {
        while self.joins.len() > t
            && let Some((i, s)) = self.joins.pop()
        {
            let pi = self.p[i] as usize;
            self.p[pi] -= s;
            self.p[i] = s;
        }
    }
}

impl Debug for RollbackDSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}, {:?}", self.p, self.joins))
    }
}

impl<Idx, T> Index<Idx> for RollbackDSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for RollbackDSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}

// SECTION: range

pub struct BIT<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn new(mut bit: Vec<T>, mut f: F) -> Self {
        let n = bit.len();
        for i in 0..n {
            if i | i + 1 < n {
                bit[i | i + 1] = f(&bit[i | i + 1], &bit[i]);
            }
        }
        Self { bit, f }
    }

    pub fn update(&mut self, mut i: usize, d: T) -> &mut Self {
        while i < self.bit.len() {
            self.bit[i] = (self.f)(&self.bit[i], &d);
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, mut i: usize, id: T) -> T {
        let mut res = id;

        while i > 0 {
            res = (self.f)(&res, &self.bit[i - 1]);
            i &= i - 1;
        }
        res
    }
}

impl<T: PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn lower_bound(&self, max: T) -> usize {
        let mut pos = 0;

        let n = self.bit.len();
        let mut pw = usize::MAX.unbounded_shr(n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= n && self.bit[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}

pub struct BIT2D<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    n: usize,
    m: usize,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn new(mut bit: Vec<T>, n: usize, m: usize, mut f: F) -> Self {
        for i in 0..n {
            for j in 0..m {
                if j | j + 1 < m {
                    bit[i * m + (j | j + 1)] = f(&bit[i * m + (j | j + 1)], &bit[i * m + j]);
                }
            }
        }
        for i in 0..n {
            if i | i + 1 < n {
                for j in 0..m {
                    bit[(i | i + 1) * m + j] = f(&bit[(i | i + 1) * m + j], &bit[i * m + j]);
                }
            }
        }
        Self { bit, n, m, f }
    }

    pub fn update(&mut self, (mut i, j): (usize, usize), d: T) -> &mut Self {
        while i < self.n {
            let mut j = j;
            while j < self.m {
                self.bit[i * self.m + j] = (self.f)(&self.bit[i * self.m + j], &d);
                j |= j + 1;
            }
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, (mut i, j): (usize, usize), identity: T) -> T {
        let mut res = identity;

        while i > 0 {
            let mut j = j;
            while j > 0 {
                res = (self.f)(&res, &self.bit[(i - 1) * self.m + j - 1]);
                j &= j - 1;
            }
            i &= i - 1;
        }
        res
    }
}

impl<T: std::cmp::PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn lower_bound_row(&self, i: usize, max: T) -> usize {
        let mut pos = 0;

        let row = &self.bit[i * self.m..(i + 1) * self.m];
        let mut pw = usize::MAX.unbounded_shr(self.m.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.m && row[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }

    pub fn lower_bound_col(&self, j: usize, max: T) -> usize {
        let mut pos = 0;

        let mut pw = usize::MAX.unbounded_shr(self.n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.n && self.bit[(pos | pw - 1) * self.m + j] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}

// Mo's algorithm using Hilbert curve
// O(n sqrt(q))
pub fn mo<T, R>(
    qs: &mut [(usize, usize, usize, T)],
    init: impl FnOnce(&mut [(usize, usize, usize, T)]) -> R,
    mut add: impl FnMut(usize, &mut R),
    mut remove: impl FnMut(usize, &mut R),
    mut answer: impl FnMut(usize, usize, usize, &T, &mut R),
) -> R {
    let q = qs.len();
    let mut ans = init(qs);
    let k = q.ilog2() + if q.is_power_of_two() { 0 } else { 1 };
    qs.sort_by_key(|&(i, j, ..)| hilbert(i as u64, j as u64, k as u64));
    let (mut l, mut r) = (1, 0);
    for &(q_l, q_r, qi, ref data) in &*qs {
        while l > q_l {
            l -= 1;
            add(l, &mut ans);
        }
        while r < q_r {
            r += 1;
            add(r, &mut ans);
        }
        while l < q_l {
            remove(l, &mut ans);
            l += 1;
        }
        while r > q_r {
            remove(r, &mut ans);
            r -= 1;
        }
        answer(q_l, q_r, qi, data, &mut ans);
    }
    ans
}

// Mo's algorithm on trees using Hilbert curve
// O(n sqrt(q))
pub fn mo_tree_paths<T, R>(
    et: &[usize],
    lca: impl Fn(usize, usize) -> usize,
    qs: &mut [(usize, usize, usize, T)],
    init: impl FnOnce(&mut [(usize, usize, usize, T)]) -> R,
    add: impl Fn(usize, &mut R),
    remove: impl Fn(usize, &mut R),
    mut answer: impl FnMut(usize, usize, usize, &T, &mut R),
) -> R {
    let toggle = move |i, (st, vis): &mut (R, BitVec)| {
        let u = et[i];
        if !vis[u] {
            add(i, st);
        } else {
            remove(i, st);
        }
        vis.set(u, !vis[u]);
    };
    mo(
        qs,
        |qs| (init(qs), BitVec::new(et.len() / 2, false)),
        &toggle,
        &toggle,
        |l, r, qi, data, s| {
            let lc = lca(et[l], et[r]);
            if lc != et[l] && lc != et[r] {
                toggle(lc, s);
            }
            answer(l, r, qi, data, &mut s.0);
            if lc != et[l] && lc != et[r] {
                toggle(lc, s);
            }
        },
    )
    .0
}

type U = u64;
const B: usize = U::BITS as usize;

pub struct RMQ<F: FnMut(usize, usize) -> Ordering> {
    n: usize,
    f: F,
    mask: Vec<U>,
    st: Vec<usize>,
}

impl<F: FnMut(usize, usize) -> Ordering> RMQ<F> {
    pub fn new(n: usize, mut f: F) -> Self {
        let mut curr_mask: U = 0;
        let mut mask = Vec::with_capacity(n);
        for i in 0..n {
            curr_mask = curr_mask << 1;
            while curr_mask != 0 && f(i, i - curr_mask.trailing_zeros() as usize).is_lt() {
                curr_mask &= curr_mask - 1;
            }
            curr_mask |= 1;
            mask.push(curr_mask);
        }
        let n_b_log = (n / B).checked_ilog2().unwrap_or_default() as usize;
        let st_size = (n / B) * (n_b_log + 1);
        let mut st = Vec::with_capacity(st_size);
        st.extend((0..n / B).map(|i| i * B + B - 1 - mask[i * B + B - 1].ilog2() as usize));
        st.resize(st_size, 0);
        let mut min = |i, j| if f(i, j).is_le() { i } else { j };
        for i in 1..=n_b_log {
            for j in 0..=n / B - (1 << i) {
                st[i * n / B + j] = min(
                    st[(i - 1) * n / B + j],
                    st[(i - 1) * n / B + j + (1 << i - 1)],
                )
            }
        }
        Self { n, f, mask, st }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> usize {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r,
            Bound::Excluded(r) => *r - 1,
            Bound::Unbounded => self.n - 1,
        };
        let n = self.n;
        match (r - l + 1).cmp(&B) {
            Ordering::Less => {
                return r - (self.mask[r] & ((1 << r - l + 1) - 1)).ilog2() as usize;
            }
            Ordering::Equal => return r - self.mask[r].ilog2() as usize,
            _ => (),
        }
        let mut min = |i, j| if (self.f)(i, j).is_le() { i } else { j };
        let mut ans = min(
            l + B - 1 - self.mask[l + B - 1].ilog2() as usize,
            r - self.mask[r].ilog2() as usize,
        );
        let (x, y) = (l / B + 1, r / B - 1);
        if x <= y {
            let i = (y - x + 1).ilog2() as usize;
            let q = min(
                self.st[i * n / B + x],
                self.st[i * n / B + y - (1 << i) + 1],
            );
            ans = min(ans, q);
        }

        ans
    }
}

pub struct SegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, &mut [T]),
    Push: FnMut(usize, usize, &mut [T]),
{
    pub n: usize,
    pub t: Vec<T>,
    pub pull: Pull,
    pub push: Push,
}

impl<T, Pull, Push> SegTree<T, Pull, Push>
where
    Pull: FnMut(usize, usize, &mut [T]),
    Push: FnMut(usize, usize, &mut [T]),
{
    pub fn new<Init: FnMut(usize, usize, &mut [T])>(
        a: Vec<T>,
        mut init: Init,
        pull: Pull,
        push: Push,
    ) -> Self {
        let n = a.len();
        let total = n << 1;
        let mut buf: Vec<MaybeUninit<T>> = Vec::with_capacity(total);
        unsafe {
            buf.set_len(total);
        }
        for (i, v) in a.into_iter().enumerate() {
            buf[n + i].write(v);
        }
        let mut l = n;
        let mut r = total - 1;
        let mut k = 2;
        while l > 1 {
            l >>= 1;
            r >>= 1;
            for p in (l..=r).rev() {
                (init)(p, k, unsafe {
                    std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut T, total)
                });
            }
            k <<= 1;
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(buf) };
        SegTree { n, t, pull, push }
    }

    pub fn build(&mut self, mut l: usize, mut r: usize) -> &mut Self {
        let mut k = 2;
        l += self.n;
        r += self.n - 1;
        while l > 1 {
            l >>= 1;
            r >>= 1;
            for i in (l..=r).rev() {
                (self.pull)(i, k, &mut self.t);
            }
            k <<= 1;
        }
        self
    }

    pub fn push(&mut self, mut l: usize, mut r: usize) -> &mut Self {
        let h = self.n.ilog2();
        let mut s = h;
        let mut k = 1 << h;
        l += self.n;
        r += self.n - 1;
        while s > 0 {
            for i in l >> s..=r >> s {
                (self.push)(i, k, &mut self.t);
            }
            s -= 1;
            k >>= 1;
        }
        self
    }

    pub fn update<R>(
        &mut self,
        range: impl RangeBounds<usize>,
        mut left: impl FnMut(usize, usize, &mut [T], &mut R),
        mut right: impl FnMut(usize, usize, &mut [T], &mut R),
        data: &mut R,
    ) -> &mut Self {
        let mut l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let mut r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        self.push(l, l + 1);
        self.push(r - 1, r);
        let (mut cl, mut cr) = (false, false);
        let mut k = 1;
        l += self.n;
        r += self.n;
        while l < r {
            if cl {
                (self.pull)(l - 1, k, &mut self.t)
            };
            if cr {
                (self.pull)(r, k, &mut self.t)
            };
            if l & 1 != 0 {
                left(l, k, &mut self.t, data);
                cl = true;
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                right(r, k, &mut self.t, data);
                cr = true;
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
        l -= 1;
        while r > 0 {
            if cl {
                (self.pull)(l, k, &mut self.t)
            };
            if cr && (!cl || l != r) {
                (self.pull)(r, k, &mut self.t);
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
        self
    }

    pub fn query<R>(
        &mut self,
        range: impl RangeBounds<usize>,
        data: &mut R,
        mut left: impl FnMut(usize, usize, &mut [T], &mut R),
        mut right: impl FnMut(usize, usize, &mut [T], &mut R),
    ) {
        let mut l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let mut r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        self.push(l, l + 1);
        if r > 0 {
            self.push(r - 1, r);
        }
        let mut k = 1;
        l += self.n;
        r += self.n;
        while l < r {
            if l & 1 != 0 {
                left(l, k, &mut self.t, data);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                right(r, k, &mut self.t, data);
            }
            l >>= 1;
            r >>= 1;
            k <<= 1;
        }
    }

    pub fn max_right<S, P>(
        &mut self,
        l: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(&S, &T) -> S,
    ) -> usize
    where
        S: Clone,
        P: FnMut(&S) -> bool,
    {
        if l == self.n {
            return self.n;
        }
        self.push(l, l + 1);
        let mut acc = init;
        let mut i = l + self.n;
        let mut k = 0;
        loop {
            while i & 1 == 0 {
                i >>= 1;
                k += 1;
            }
            let combined = (op)(&acc, &self.t[i]);
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, 1 << k, &mut self.t);
                    i <<= 1;
                    k -= 1;
                    let cand = (op)(&acc, &self.t[i]);
                    if p(&cand) {
                        acc = cand;
                        i += 1;
                    }
                }
                break i - self.n;
            }
            acc = combined;
            i += 1;
            if i.is_power_of_two() {
                break self.n;
            }
        }
    }

    pub fn min_left<S, P>(
        &mut self,
        r: usize,
        mut p: P,
        init: S,
        mut op: impl FnMut(&T, &S) -> S,
    ) -> usize
    where
        S: Clone,
        P: FnMut(&S) -> bool,
    {
        if r == 0 {
            return 0;
        }
        self.push(r - 1, r);
        let mut acc = init;
        let mut i = r + self.n;
        let mut k = 0;
        loop {
            i -= 1;
            while i > 1 && i & 1 == 1 {
                i >>= 1;
                k += 1;
            }
            let combined = (op)(&self.t[i], &acc);
            if !p(&combined) {
                while i < self.n {
                    (self.push)(i, k, &mut self.t);
                    i = i << 1 | 1;
                    k -= 1;
                    let cand = (op)(&self.t[i], &acc);
                    if p(&cand) {
                        acc = cand;
                        i -= 1;
                    }
                }
                break i + 1 - self.n;
            }
            acc = combined;
            if i.is_power_of_two() {
                break 0;
            }
        }
    }

    pub fn n(&self) -> usize {
        self.n
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseTable<T, F: FnMut(&T, &T) -> T> {
    pub n: usize,
    pub t: Vec<T>,
    pub f: F,
}

impl<T: Clone, F: FnMut(&T, &T) -> T> SparseTable<T, F> {
    pub fn new(a: Vec<T>, mut f: F) -> Self {
        let n = a.len();
        let l = if n == 0 { 0 } else { n.ilog2() as usize + 1 };
        let mut t: Vec<MaybeUninit<T>> = Vec::with_capacity(n * l);
        unsafe {
            t.set_len(n * l);
        }
        for (i, v) in a.into_iter().enumerate() {
            t[i].write(v);
        }
        let mut i = 1;
        let mut p = 2;
        while p <= n {
            let off = i * n;
            for j in 0..=n - p {
                let r = f(unsafe { t[(i - 1) * n + j].assume_init_ref() }, unsafe {
                    t[(i - 1) * n + j + (p >> 1)].assume_init_ref()
                });
                t[off + j].write(r);
            }
            i += 1;
            p <<= 1;
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(t) };
        Self { n, t, f }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> T {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };
        debug_assert!(l < r);
        debug_assert!(r <= self.n);
        let n = self.n;
        let i = (r - l).ilog2() as usize;
        (self.f)(&self.t[i * n + l], &self.t[i * n + r - (1 << i)])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisjointSparseTable<T, F> {
    pub n: usize,
    pub t: Vec<T>,
    pub f: F,
}

impl<T: Clone + std::fmt::Debug, F> DisjointSparseTable<T, F>
where
    F: FnMut(&T, &T) -> T,
{
    pub fn new(a: Vec<T>, mut f: F) -> Self {
        let n = a.len();
        let l = if n == 0 { 0 } else { n.ilog2() as usize + 1 };
        let total = n * l;
        let mut buf: Vec<MaybeUninit<T>> = Vec::with_capacity(total);
        unsafe {
            buf.set_len(total);
        }
        for h in 0..l {
            let l = 1 << h;
            let mut c = l;
            while c < n + l {
                if c < n {
                    buf[h * n + c].write(a[c].clone());
                }
                if c - 1 < n {
                    buf[h * n + c - 1].write(a[c - 1].clone());
                }
                for i in (c + 1)..n.min(c + l) {
                    let prev_val = unsafe { buf[h * n + i - 1].assume_init_ref() };
                    let curr_val = &a[i];
                    let result = f(prev_val, curr_val);
                    buf[h * n + i].write(result);
                }
                for i in (c - l..n.min(c - 1)).rev() {
                    let curr_val = &a[i];
                    let next_val = unsafe { buf[h * n + i + 1].assume_init_ref() };
                    let result = f(curr_val, next_val);
                    buf[h * n + i].write(result);
                }
                c += l << 1;
            }
        }
        let t = unsafe { std::mem::transmute::<_, Vec<T>>(buf) };
        Self { n, t, f }
    }

    pub fn query(&mut self, range: impl RangeBounds<usize>) -> T {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r,
            Bound::Excluded(r) => *r - 1,
            Bound::Unbounded => self.n - 1,
        };
        debug_assert!(l <= r);
        debug_assert!(r < self.n);
        if l == r {
            return self.t[l].clone();
        }
        let n = self.n;
        let h = (l ^ r).ilog2() as usize;
        (self.f)(&self.t[h * n + l], &self.t[h * n + r])
    }
}

// SECTION: scc

/// Tarjan's SCC
/// calls f on the SCCs in reverse topological order
/// outputs the indices of the SCCs that the vertices are in (also in reverse topological order)
pub fn scc<F: FnMut(Vec<usize>)>(g: &[Vec<usize>], mut f: F) -> Vec<usize> {
    let n = g.len();
    if n == 0 {
        return Vec::new();
    }
    let mut idx = 1;
    let mut comp_count = usize::MAX;
    let mut root_idx = vec![0; n];
    let mut child = BitVec::new(n, false);
    let mut start = 0;
    let mut stk = Vec::with_capacity(n);
    let mut cur = 0;
    stk.push((start, 0));
    root_idx[start] = idx;
    idx += 1;
    'a: loop {
        let (v, e_m) = &mut stk[cur];
        let v = *v;
        let e = *e_m;
        let ws = &g[v];
        if e < ws.len() {
            let w = ws[e];
            if root_idx[w] == 0 {
                root_idx[w] = idx;
                stk.push((w, 0));
                idx += 1;
                cur = stk.len() - 1;
                continue 'a;
            } else {
                if root_idx[w] < root_idx[v] {
                    root_idx[v] = root_idx[w];
                    child.set(v, true);
                }
                *e_m += 1;
            }
        } else {
            if !child.get(v) {
                let comp = stk.drain(cur..).map(|(v, _)| v).collect::<Vec<_>>();
                idx -= comp.len();
                for &v in &comp {
                    root_idx[v] = comp_count;
                }
                f(comp);
                comp_count -= 1;
            }
            if cur != 0 {
                cur -= 1;
            } else {
                while start < n && root_idx[start] != 0 {
                    start += 1;
                }
                if start < n {
                    root_idx[start] = idx;
                    stk.push((start, 0));
                    cur = stk.len() - 1;
                    idx += 1;
                    start += 1;
                } else {
                    break;
                }
            }
        }
    }
    for v in &mut root_idx {
        *v = !*v;
    }
    root_idx
}

// SECTION: matching

// Hopcroft-Karp maximum bipartite matching O(sqrt(|V|) |E|)
pub fn hopcroft_karp(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
) -> (usize, Vec<usize>, Vec<usize>) {
    let mut l = vec![usize::MAX; n];
    let mut r = vec![usize::MAX; k];
    let mut size = 0;
    let mut rt = vec![usize::MAX; n];
    let mut fa = vec![usize::MAX; n];
    let mut q = vec![0; n];
    for u in 0..n {
        if l[u] != usize::MAX {
            continue;
        }
        for &v in &g[d[u]..d[u + 1]] {
            if r[v] == usize::MAX {
                l[u] = v;
                r[v] = u;
                size += 1;
                break;
            }
        }
    }
    loop {
        rt.fill(usize::MAX);
        fa.fill(usize::MAX);
        let mut q_n = 0;
        for i in 0..n {
            if l[i] == usize::MAX {
                q[q_n] = i;
                rt[i] = i;
                fa[i] = i;
                q_n += 1;
            }
        }
        let mut matched = false;
        let mut i = 0;
        while i < q_n {
            let u = q[i];
            if l[rt[u]] != usize::MAX {
                i += 1;
                continue;
            }
            for j in d[u]..d[u + 1] {
                let v = g[j] as usize;
                if r[v] == usize::MAX {
                    let mut vv = v;
                    let mut uu = u;
                    while vv != usize::MAX {
                        r[vv] = uu;
                        let nvv = l[uu];
                        l[uu] = vv;
                        vv = nvv;
                        uu = fa[uu];
                    }
                    matched = true;
                    size += 1;
                    break;
                }
                let rv = r[v] as usize;
                if fa[rv] == usize::MAX {
                    q[q_n] = rv;
                    fa[rv] = u;
                    rt[rv] = rt[u];
                    q_n += 1;
                }
            }
            i += 1;
        }
        if !matched {
            break;
        }
    }
    (size, l, r)
}

#[inline]
pub fn edges_to_csr_undir(n: usize, es: &[[usize; 2]]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 1];

    for &[x, _] in es {
        d[x] += 1;
    }
    for i in 1..=n {
        d[i] += d[i - 1];
    }
    for &[x, y] in es {
        d[x] -= 1;
        g[d[x]] = y;
    }

    (g, d)
}

#[inline]
pub fn edges_to_csr_undir_one_based(n: usize, es: &[[usize; 2]]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 2];

    for &[x, _] in es {
        d[x] += 1;
    }
    for i in 2..=n + 1 {
        d[i] += d[i - 1];
    }
    for &[x, y] in es {
        d[x] -= 1;
        g[d[x]] = y;
    }

    (g, d)
}

pub fn es_to_xor<T: Copy + Default + BitXorAssign, E>(
    n: usize,
    es: impl Iterator<Item = E>,
    mut to: impl FnMut(&E) -> (usize, usize, T),
) -> (Vec<usize>, Vec<usize>, Vec<T>) {
    let (mut d, mut p, mut w) = (vec![0; n], vec![0; n], vec![T::default(); n]);
    for e in es {
        let (u, v, c) = to(&e);
        d[u] += 1;
        d[v] += 1;
        p[u] ^= v;
        p[v] ^= u;
        w[u] ^= c;
        w[v] ^= c;
    }
    d[0] = usize::MAX;
    (p, d, w)
}

/// O(n^3)
pub fn blossom(n: usize, g: &[usize], d: &[usize]) -> (usize, Vec<usize>) {
    let mut n_matches = 0;
    let mut mate = vec![0; n + 1];
    let mut q = vec![0; n + 1];
    let mut book = BitVec::new(n + 1, false);
    let mut typ = vec![u8::MAX; n + 1];
    let mut fa = vec![0; n + 1];
    let mut bl = vec![0; n + 1];
    for u in 1..=n {
        if mate[u] != 0 {
            continue;
        }
        for &v in &g[d[u]..d[u + 1]] {
            if mate[v] == 0 {
                mate[u] = v;
                mate[v] = u;
                n_matches += 1;
                break;
            }
        }
    }
    'a: for sv in 1..=n {
        if mate[sv] != 0 {
            continue;
        }
        for u in 1..=n {
            bl[u] = u;
            typ[u] = u8::MAX;
        }
        q[0] = sv;
        let mut q_n = 1;
        typ[sv] = 0;
        let mut i = 0;
        while i < q_n {
            let u = q[i];
            for &v in &g[d[u]..d[u + 1]] {
                if typ[v] == u8::MAX {
                    fa[v] = u;
                    typ[v] = 1;
                    let nu = mate[v];
                    if nu == 0 {
                        let mut vv = v;
                        while vv != 0 {
                            let nvv = mate[fa[vv]];
                            mate[vv] = fa[vv];
                            mate[fa[vv]] = vv;
                            vv = nvv;
                        }
                        n_matches += 1;
                        continue 'a;
                    }
                    q[q_n] = nu;
                    q_n += 1;
                    typ[nu] = 0;
                } else if typ[v] == 0 && bl[u] != bl[v] {
                    book.clear();
                    let mut uu = u;
                    let mut vv = v;
                    let lca = loop {
                        if uu != 0 {
                            if book.get(uu) {
                                break uu;
                            }
                            book.set(uu, true);
                            uu = bl[fa[mate[uu]]];
                        }
                        (uu, vv) = (vv, uu);
                    };
                    let mut go_up = |mut u, mut v, lca| {
                        while bl[u] != lca {
                            fa[u] = v;
                            v = mate[u];
                            if typ[v] == 1 {
                                q[q_n] = v;
                                q_n += 1;
                                typ[v] = 0;
                            }
                            bl[u] = lca;
                            bl[v] = lca;
                            u = fa[v];
                        }
                    };
                    go_up(u, v, lca);
                    go_up(v, u, lca);
                    for u in 1..=n {
                        bl[u] = bl[bl[u]];
                    }
                }
            }
            i += 1;
        }
    }
    (n_matches, mate)
}

// SECTION: tree

pub struct LCA<'a, F: FnMut(usize, usize) -> Ordering> {
    p: &'a [usize],
    dfs: &'a [usize],
    pos: &'a [usize],
    rmq: RMQ<F>,
}

impl<'a, F: FnMut(usize, usize) -> Ordering> LCA<'a, F> {
    /// O(n)
    /// cmp must be
    /// z\[i\].cmp(&z\[j\])
    /// where z\[i\] = depth\[p\[dfs\[i\]\]\]
    /// can't be done ahead of time without boxing
    pub fn new(n: usize, p: &'a [usize], dfs: &'a [usize], pos: &'a [usize], cmp: F) -> Self {
        Self {
            p,
            dfs,
            pos,
            rmq: RMQ::new(n, cmp),
        }
    }

    /// O(1)
    pub fn query(&mut self, a: usize, b: usize) -> usize {
        let (l, r) = if self.pos[a] <= self.pos[b] {
            (self.pos[a], self.pos[b])
        } else {
            (self.pos[b], self.pos[a])
        };
        if a == b {
            a
        } else {
            self.p[self.dfs[self.rmq.query(l + 1..=r)]]
        }
    }
}

// builds jmp table for binary lifting in O(n)
pub fn build_jmp(par: &[usize], dfs: &[usize], depth: &[usize]) -> Vec<usize> {
    let n = par.len();
    let mut jmp = vec![0; n];
    for &v in dfs {
        let p = par[v];
        if v == p {
            jmp[v] = v;
        } else {
            let pj = jmp[p];
            let ppj = jmp[pj];
            if depth[p] - depth[pj] == depth[pj] - depth[ppj] {
                jmp[v] = ppj;
            } else {
                jmp[v] = p;
            }
        }
    }
    jmp
}

// O(log n)
pub fn depth_jmp(mut u: usize, d: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    while depth[u] > d {
        if depth[jmp[u]] < d {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

// O(log n)
pub fn search_jmp(
    mut u: usize,
    mut p: impl FnMut(usize) -> bool,
    par: &[usize],
    jmp: &[usize],
) -> usize {
    while !p(u) {
        if p(jmp[u]) {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

// O(log n)
pub fn lca_jmp(mut u: usize, mut v: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    if depth[u] > depth[v] {
        (u, v) = (v, u);
    }
    v = depth_jmp(v, depth[u], par, jmp, depth);
    while u != v {
        if jmp[u] == jmp[v] {
            (u, v) = (par[u], par[v]);
        } else {
            (u, v) = (jmp[u], jmp[v]);
        }
    }
    u
}

pub fn cartesian<T: PartialOrd>(a: &[T]) -> Vec<usize> {
    let n = a.len();
    let mut p = vec![usize::MAX; n];
    let mut stk = Vec::with_capacity(n);
    for i in 0..n {
        let mut last = usize::MAX;
        while let Some(&l) = stk.last() {
            if a[l] < a[i] {
                break;
            }
            last = l;
            stk.pop();
        }
        if let Some(&l) = stk.last() {
            p[i] = l;
        }
        if last != usize::MAX {
            p[last] = i;
        }
        stk.push(i);
    }
    p
}

/// returns (p, d)
/// add_edge takes \[u, v, i\], where (u, v) is the ith edge produced by es
/// update takes \[u, v, deg\[v\]\] where v = p\[u\]
pub fn xor_linked_tree(
    n: usize,
    mut p: Vec<usize>,
    mut d: Vec<usize>,
    mut update: impl FnMut([usize; 3]),
) -> (Vec<usize>, Vec<usize>) {
    for i in 0..n {
        let mut u = i;
        while d[u] == 1 {
            d[u] = 0;
            let v = p[u];
            update([u, v, d[v]]);
            p[v] ^= u;
            d[v] -= 1;
            u = v;
        }
    }
    (p, d)
}

/// returns (p, ss, pos, dfs, depth)
/// add_edge takes an edge (u, v, deg\[u\], deg\[v\])
/// update takes (u, v, deg\[v\], ss\[u\], ss\[v\], idx)
/// where v = p\[u\], ss is subtree size, ss\[v\] is correct if deg\[v\] == 1
/// and idx is the dfs order index of u
pub fn xor_linked_tree_dfs(
    n: usize,
    p: Vec<usize>,
    d: Vec<usize>,
    mut update: impl FnMut([usize; 6]),
) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let (mut ss, mut dfs, mut depth) = (vec![1; n], vec![0; n], vec![0; n]);
    let mut idx = n - 1;
    let (p, d) = xor_linked_tree(n, p, d, |[u, v, d_v]| {
        ss[v] += ss[u];
        update([u, v, d_v, ss[u], ss[v], idx]);
        dfs[idx] = u;
        idx -= 1;
    });
    let mut pos = d;
    pos.copy_from_slice(&ss);
    for i in 1..n {
        let u = dfs[i];
        let v = p[u];
        depth[u] = depth[v] + 1;
        (pos[u], pos[v]) = (pos[v], pos[v] - pos[u]);
    }
    for i in 0..n {
        pos[i] -= 1;
        dfs[pos[i]] = i;
    }
    (p, ss, pos, dfs, depth)
}

/// maximum o of weights over path
pub fn diameter<T: Clone + PartialOrd + BitXorAssign>(
    n: usize,
    p: Vec<usize>,
    d: Vec<usize>,
    mut ws: Vec<T>,
    id: T,
    bot: T,
    mut o: impl FnMut(&T, &T) -> T,
) -> (T, Vec<usize>) {
    let mut f = vec![usize::MAX; n];
    let mut mx = vec![id.clone(); n];
    let mut ans = bot;
    let mut l = 0;
    let mut r = 0;
    let (p, mut d) = xor_linked_tree(n, p, d, |[u, v, _]: [usize; 3]| {
        let w = ws[u].clone();
        let cur = o(&mx[u], &w);
        let len = o(&cur, &mx[v]);
        if ans < len {
            ans = len;
            l = u;
            r = f[v];
        }
        if mx[v] < cur {
            mx[v] = cur;
            f[v] = u;
        }
        ws[v] ^= w;
    });
    d.clear();
    d.push(p[l]);
    while l != usize::MAX {
        d.push(l);
        l = f[l];
    }
    d.reverse();
    while r != usize::MAX {
        d.push(r);
        r = f[r];
    }
    (ans, d)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub n: Vec<LCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
}

impl<T, Push, Pull, Rev> LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub fn new(init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        Self {
            n: vec![LCTNode {
                v: init,
                p: 0,
                ch: [0; 2],
                rev: false,
                k: -1,
            }],
            pull,
            push,
            rev,
        }
    }

    pub fn with_capacity(capacity: usize, init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        let mut nodes = Vec::with_capacity(capacity + 1);
        nodes.push(LCTNode {
            v: init,
            p: 0,
            ch: [0; 2],
            rev: false,
            k: -1,
        });
        Self {
            n: nodes,
            pull,
            push,
            rev,
        }
    }

    pub fn add_node(&mut self, v: T) -> usize {
        self.n.push(LCTNode {
            v,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        self.n.len() - 2
    }

    fn reverse(&mut self, x: usize) {
        if x != 0 {
            self.n[x].rev ^= true;
            (self.rev)(x, &mut self.n);
        }
    }

    fn push(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [mut ch0, mut ch1] = self.n[x].ch;
        if self.n[x].rev {
            self.n[x].ch.swap(0, 1);
            (ch0, ch1) = (ch1, ch0);
            self.n[ch0].k = 0;
            self.n[ch1].k = 1;
            self.reverse(ch0);
            self.reverse(ch1);
            self.n[x].rev = false;
        }
        (self.push)([x, ch0, ch1], &mut self.n);
    }

    fn pull(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [ch0, ch1] = self.n[x].ch;
        (self.pull)([x, ch0, ch1], &mut self.n);
    }

    fn rot(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let p = self.n[x].p;
        if p == 0 {
            return;
        }
        let g = self.n[p].p;
        let k = self.n[x].k as usize;
        let t = self.n[p].k;
        let child = self.n[x].ch[k ^ 1];
        self.n[child].p = p;
        self.n[child].k = k as i8;
        self.n[p].ch[k] = child;
        self.n[p].p = x;
        self.n[p].k = (k ^ 1) as i8;
        self.n[x].ch[k ^ 1] = p;
        self.n[x].p = g;
        self.n[x].k = t;
        if t != -1 {
            self.n[g].ch[t as usize] = x;
        }
        self.pull(p);
    }

    #[inline]
    fn is_root(&self, x: usize) -> bool {
        self.n[x].k == -1
    }

    fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.push(x);
        while !self.is_root(x) {
            let p = self.n[x].p;
            if self.is_root(p) {
                self.push(p);
                self.push(x);
                self.rot(x);
            } else {
                let g = self.n[p].p;
                self.push(g);
                self.push(p);
                self.push(x);
                if self.n[x].k == self.n[p].k {
                    self.rot(p);
                    self.rot(x);
                } else {
                    self.rot(x);
                    self.rot(x);
                }
            }
        }
    }

    fn access(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.splay(x);
        let [_, ch1] = self.n[x].ch;
        self.n[ch1].k = -1;
        self.n[x].ch[1] = 0;
        while self.n[x].p != 0 {
            let p = self.n[x].p;
            self.splay(p);
            let [_, ch1] = self.n[p].ch;
            self.n[ch1].k = -1;
            self.n[p].ch[1] = x;
            self.n[x].k = 1;
            self.rot(x);
        }
    }

    #[inline]
    fn make_root(&mut self, x: usize) {
        self.access(x);
        self.reverse(x);
    }

    #[inline]
    pub fn link(&mut self, mut w: usize, mut x: usize) {
        w += 1;
        x += 1;
        self.make_root(w);
        self.n[w].p = x;
    }

    pub fn cut(&mut self, mut u: usize, mut v: usize) {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        let [ch0, _] = self.n[v].ch;
        self.n[ch0].p = 0;
        self.n[ch0].k = -1;
        self.n[v].ch[0] = 0;
        self.pull(v);
    }

    pub fn update<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.splay(u);
        f(u, self.n[u].ch, &mut self.n)
    }

    pub fn query_root<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.make_root(u);
        f(u, self.n[u].ch, &mut self.n)
    }

    pub fn query<R>(
        &mut self,
        mut u: usize,
        mut v: usize,
        mut f: impl FnMut(usize, [usize; 2], usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        f(u, self.n[u].ch, v, self.n[v].ch, &mut self.n)
    }

    pub fn conn(&mut self, mut u: usize, mut v: usize) -> bool {
        u += 1;
        v += 1;
        if u == v {
            true
        } else {
            self.make_root(u);
            self.access(v);
            self.n[u].p != 0
        }
    }

    #[inline]
    pub fn parent(&mut self, mut v: usize, mut w: usize) {
        v += 1;
        w += 1;
        self.n[v].p = w;
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.n.len()
    }
}

pub struct MergeSortTree<T> {
    t: Vec<Vec<T>>,
    n: usize,
}

impl<T> MergeSortTree<T>
where
    T: Copy + Ord,
{
    pub fn new(a: &[T]) -> Self {
        let n = a.len();
        let mut t = vec![Vec::new(); n.next_power_of_two() << 1];
        let mut a = a
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, i))
            .collect::<Vec<_>>();
        a.sort_unstable();
        for (v, mut i) in a {
            i += n;
            while i > 0 {
                t[i].push(v);
                i >>= 1;
            }
        }
        Self { t, n }
    }

    fn _merge(a: &[T], b: &[T]) -> Vec<T> {
        let mut res = Vec::with_capacity(a.len() + b.len());
        let mut i = 0;
        let mut j = 0;
        while i < a.len() && j < b.len() {
            if a[i] < b[j] {
                res.push(a[i]);
                i += 1;
            } else {
                res.push(b[j]);
                j += 1;
            }
        }
        res.extend_from_slice(&a[i..]);
        res.extend_from_slice(&b[j..]);
        res
    }

    pub fn count_le(&self, mut l: usize, mut r: usize, k: T) -> usize {
        let n = self.n;
        let mut res = 0;
        l += n;
        r += n;
        while l < r {
            if l & 1 != 0 {
                res += self.t[l].partition_point(|&x| x <= k);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res += self.t[r].partition_point(|&x| x <= k);
            }
            l >>= 1;
            r >>= 1;
        }
        res
    }
}

const NULL: usize = 0;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplayNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
    pub size: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    pub n: Vec<SplayNode<T>>,
    pub push: Push,
    pub pull: Pull,
    pub rt: usize,
    pub nxt: usize,
    pub removed: usize,
    pub open: BitVec,
}

impl<T, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    #[inline]
    pub fn new(init: T, push: Push, pull: Pull) -> Self {
        Self {
            n: vec![SplayNode {
                v: init,
                l: NULL,
                r: NULL,
                size: 0,
            }],
            push,
            pull,
            rt: NULL,
            nxt: 1,
            removed: 0,
            open: BitVec::new(1, false),
        }
    }

    #[inline]
    fn pull(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.n[x];
            let (l, r) = (n.l, n.r);
            self.n[x].size = self.n[l].size + self.n[r].size + 1;
            (self.pull)(x, l, r, &mut self.n);
        }
        self
    }

    #[inline]
    fn push(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.n[x];
            (self.push)(x, n.l, n.r, &mut self.n);
        }
        self
    }

    #[inline]
    fn zig(&mut self, x: usize) -> usize {
        let l = self.n[x].l;
        self.n[x].l = self.n[l].r;
        self.pull(x);
        self.n[l].r = x;
        l
    }

    #[inline]
    fn zag(&mut self, x: usize) -> usize {
        let r = self.n[x].r;
        self.n[x].r = self.n[r].l;
        self.pull(x);
        self.n[r].l = x;
        r
    }

    fn splay(&mut self, x: usize, mut k: usize) -> usize {
        self.push(x);
        let l = self.n[x].l;
        let size = self.n[l].size;
        if k == size {
            x
        } else if k < size {
            self.push(l);
            let (ll, lr) = (self.n[l].l, self.n[l].r);
            let ll_size = self.n[ll].size;
            if k == ll_size {
                self.zig(x)
            } else if k < ll_size {
                self.n[l].l = self.splay(ll, k);
                let new_l = self.zig(x);
                self.zig(new_l)
            } else {
                self.n[l].r = self.splay(lr, k - ll_size - 1);
                self.n[x].l = self.zag(l);
                self.zig(x)
            }
        } else {
            let r = self.n[x].r;
            self.push(r);
            k -= size + 1;
            let (rl, rr) = (self.n[r].l, self.n[r].r);
            let rl_size = self.n[rl].size;
            if k == rl_size {
                self.zag(x)
            } else if k < rl_size {
                self.n[r].l = self.splay(rl, k);
                self.n[x].r = self.zig(r);
                self.zag(x)
            } else {
                self.n[r].r = self.splay(rr, k - rl_size - 1);
                let new_r = self.zag(x);
                self.zag(new_r)
            }
        }
    }

    #[inline]
    pub fn get(&mut self, k: usize) -> Option<&T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&self.n[self.rt].v)
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: usize) -> Option<&mut T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&mut self.n[self.rt].v)
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: usize, v: T) -> &mut Self {
        let len = self.n.len();
        while self.nxt < self.n.len() && !self.open[self.nxt] {
            self.nxt += 1;
        }
        let nxt = self.nxt;
        if self.len() <= k {
            let n = SplayNode {
                v,
                l: self.rt,
                r: NULL,
                size: 0,
            };
            if nxt < len {
                self.n[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.n.push(n);
                self.open.push(false);
            }
        } else {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            let l = self.n[self.rt].l;
            self.n[self.rt].l = NULL;
            self.pull(self.rt);
            let n = SplayNode {
                v,
                l,
                r: self.rt,
                size: 0,
            };
            if nxt < len {
                self.n[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.n.push(n);
                self.open.push(false);
            }
        }
        self.pull(nxt);
        self.push(nxt);
        self.rt = nxt;
        self.nxt += 1;
        self
    }

    pub fn remove(&mut self, k: usize) -> &mut Self {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.open.set(self.rt, true);
            self.push(self.rt);
            let r = self.n[self.rt].r;
            if r != NULL {
                let r = self.splay(r, 0);
                (self.n[r].l, self.n[self.rt].l, self.rt) = (self.n[self.rt].l, NULL, r);
                self.pull(r);
            } else {
                (self.rt, self.n[self.rt].l) = (self.n[self.rt].l, NULL);
            }
        }
        self.removed += 1;
        let len = self.n.len();
        if self.removed << 1 > len {
            self.nxt = self.open.iter().position(|v| v == true).unwrap_or(len);
            self.removed = 0;
        }
        self
    }

    pub fn merge_nodes(&mut self, mut a: usize, b: usize) -> usize {
        if a == NULL {
            return b;
        } else if b == NULL {
            return a;
        }
        let a_size = self.n[a].size;
        a = self.splay(a, a_size - 1);
        self.pull(a);
        self.push(a);
        self.n[a].r = b;
        self.pull(a);
        a
    }

    pub fn split_node(&mut self, mut a: usize, k: usize) -> (usize, usize) {
        if a == NULL {
            (NULL, NULL)
        } else if k == NULL {
            self.push(a);
            (NULL, a)
        } else if k >= self.n[a].size {
            self.push(a);
            (a, NULL)
        } else {
            a = self.splay(a, k - 1);
            self.pull(a);
            self.push(a);
            let r = self.n[a].r;
            self.n[a].r = NULL;
            if r != NULL {
                self.push(r);
            }
            self.pull(a);
            (a, r)
        }
    }

    pub fn range<R, F>(&mut self, range: impl RangeBounds<usize>, mut f: F) -> Option<R>
    where
        F: FnMut(usize, &mut [SplayNode<T>]) -> R,
    {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.len(),
        };
        if l >= r {
            return None;
        }
        let (a, b) = self.split_node(self.rt, l);
        let (b, c) = self.split_node(b, r - l);
        let res = if b != NULL {
            Some(f(b, &mut self.n))
        } else {
            None
        };
        let merged_ab = self.merge_nodes(a, b);
        self.rt = self.merge_nodes(merged_ab, c);
        res
    }

    #[inline]
    pub fn for_each<F>(&mut self, mut f: F) -> &mut Self
    where
        F: FnMut(&T),
    {
        self.for_each_node(self.rt, &mut f);
        self
    }

    fn for_each_node<F>(&mut self, n: usize, f: &mut F)
    where
        F: FnMut(&T),
    {
        if n != NULL {
            let (l, r) = (self.n[n].l, self.n[n].r);
            self.push(n);
            self.for_each_node(l, f);
            f(&self.n[n].v);
            self.for_each_node(r, f);
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.rt != NULL {
            self.n[self.rt].size
        } else {
            0
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rt == NULL
    }
}

impl<T: Clone, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    fn build<S>(&mut self, v: &[S], elem: &mut impl FnMut(&S) -> T, l: usize, r: usize) -> usize {
        if l == r {
            NULL
        } else if l + 1 == r {
            self.n[l].v = elem(&v[l - 1]);
            self.pull(l);
            l
        } else {
            let m = l + (r - l >> 1);
            self.n[m].v = elem(&v[m - 1]);
            self.n[m].l = self.build(v, elem, l, m);
            self.n[m].r = self.build(v, elem, m + 1, r);
            self.pull(m);
            m
        }
    }

    pub fn from_slice<S>(
        v: &[S],
        init: T,
        mut elem: impl FnMut(&S) -> T,
        push: Push,
        pull: Pull,
    ) -> Splay<T, Push, Pull> {
        let len = v.len();
        let mut s = Splay {
            n: vec![
                SplayNode {
                    v: init,
                    l: NULL,
                    r: NULL,
                    size: 0
                };
                len + 1
            ],
            push,
            pull,
            rt: NULL,
            nxt: len,
            removed: 0,
            open: BitVec::new(len + 1, false),
        };
        s.rt = s.build(v, &mut elem, 1, len + 1);
        s
    }
}

// O(n + |key| f(n)) if f(n) is the cost of calling lca
// Thus total including building LCA with O(1) / O(n) lca will be O(n + |key|) = O(n)
pub fn vtree(
    n: usize,
    key: &mut [usize],
    vs: &mut Vec<usize>,
    vadj: &mut [Vec<usize>],
    pos: &[usize],
    mut lca: impl FnMut(usize, usize) -> usize,
) {
    vs.clear();
    if key.is_empty() {
        return;
    }
    let z = counting_sort_dedup_by_key(key, n, |&v| pos[v]);
    vs.truncate(z);
    vs.resize(key.len(), 0);
    vs.copy_from_slice(key);
    for i in 1..key.len() {
        vs.push(lca(key[i - 1], key[i]));
    }
    let z = counting_sort_dedup_by_key(vs, n, |&v| pos[v]);
    vs.truncate(z);
    for &v in &*vs {
        vadj[v].clear();
    }
    for i in 1..vs.len() {
        vadj[lca(vs[i - 1], vs[i])].push(vs[i]);
    }
}

/// Online Bridge Tree O(n log n α(n) + m α(n))
pub struct BridgeTree {
    pub par: Vec<usize>,
    pub ecc2: DSU,
    pub cc: DSU,
    pub count: usize,
    pub mask: BitVec,
    pub seen: BitVec,
}

impl BridgeTree {
    pub fn new(n: usize) -> Self {
        BridgeTree {
            par: vec![usize::MAX; n],
            ecc2: DSU::new(n),
            cc: DSU::new(n),
            count: 0,
            mask: BitVec::new(n, false),
            seen: BitVec::new(n, false),
        }
    }

    fn make_root(&mut self, v: usize) -> &mut Self {
        if self.par[v] == usize::MAX {
            return self;
        }
        let mut cur = v;
        let root = v;
        let mut child = usize::MAX;
        while self.par[cur] != usize::MAX {
            let p = self.ecc2.find(self.par[cur]);
            self.par[cur] = child;
            self.cc[cur] = root as isize;
            (child, cur) = (cur, p);
        }
        self.par[cur] = child;
        self.cc[child] = self.cc[cur];
        self.cc[cur] = root as isize;
        self
    }

    fn merge_path(&mut self, mut a: usize, mut b: usize) -> &mut Self {
        self.seen.clear();
        let mut path_a = Vec::new();
        let mut path_b = Vec::new();
        let mut lca = usize::MAX;
        while lca == usize::MAX {
            if a != usize::MAX {
                a = self.ecc2.find(a);
                path_a.push(a);
                if self.seen[a] {
                    lca = a;
                    break;
                } else {
                    self.seen.set(a, true);
                    a = self.par[a];
                }
            }
            if b != usize::MAX {
                b = self.ecc2.find(b);
                path_b.push(b);
                if self.seen[b] {
                    lca = b;
                    break;
                } else {
                    self.seen.set(b, true);
                    b = self.par[b];
                }
            }
        }
        let mut r = self.ecc2.find(lca);
        for i in 0..path_a.len() {
            let v = path_a[i];
            if v == lca {
                break;
            }
            self.mask.set(v, true);
            self.count -= 1;
            (_, r) = self.ecc2.union_root(v, r);
        }
        for i in 0..path_b.len() {
            let v = path_b[i];
            if v == lca {
                break;
            }
            self.mask.set(v, true);
            self.count -= 1;
            (_, r) = self.ecc2.union_root(v, r);
        }
        self.par[r] = self.par[lca];
        self
    }

    pub fn add_edge(&mut self, mut a: usize, mut b: usize) -> &mut Self {
        a = self.ecc2.find(a);
        b = self.ecc2.find(b);
        if a == b {
            return self;
        }
        let ca = self.cc.find(a);
        let mut cb = self.cc.find(b);
        if ca != cb {
            if self.cc[ca] < self.cc[cb] {
                (a, b, cb) = (b, a, ca);
            }
            self.count += 1;
            self.make_root(a);
            self.par[a] = b;
            self.cc[cb] += self.cc[a];
            self.cc[a] = b as isize;
        } else {
            self.merge_path(a, b);
        }
        self
    }

    pub fn bridges(&self) -> Vec<(usize, usize)> {
        self.par
            .iter()
            .enumerate()
            .filter_map(|(i, &j)| (j != usize::MAX && !self.mask[i]).then_some((i, j)))
            .collect()
    }
}

/// O(n log n + sum_{cd} F(cd)) where F(cd) is the cost of calling F on that centroid
pub fn centroid_decomp(
    adj: &[Vec<usize>],
    mut f: impl FnMut([usize; 3], &mut BitVec, &mut [usize]),
) {
    let n = adj.len();
    let mut is_removed = BitVec::new(n, false);
    let mut ss = vec![0; n];
    let mut stk = Vec::with_capacity(n);
    let mut get_ss = |u, p, is_removed: &BitVec, ss: &mut [usize]| {
        stk.push((u, p, 0, 1));
        while let Some((u, p, idx_m, acc)) = stk.last_mut() {
            let (u, p, idx, acc) = (*u, *p, *idx_m, *acc);
            let ws: &Vec<usize> = &adj[u];
            if idx < ws.len() {
                let v = ws[idx];
                *idx_m += 1;
                if v != p && !is_removed[v] {
                    stk.push((v, u, 0, 1));
                }
            } else {
                stk.pop();
                ss[u] = acc;
                if let Some(top) = stk.last_mut() {
                    top.3 += acc;
                }
            }
        }
        ss[u]
    };
    let mut stk = Vec::with_capacity(n);
    stk.push((0, usize::MAX, 0));
    while let Some((u, pcd, d)) = stk.pop() {
        let mut v = u;
        let mut p = usize::MAX;
        let tree_size = get_ss(u, usize::MAX, &is_removed, &mut ss);
        let cd = 'a: loop {
            for &w in &adj[v] {
                if w != p && !is_removed[w] && ss[w] * 2 > tree_size {
                    (p, v) = (v, w);
                    continue 'a;
                }
            }
            break v;
        };
        f([cd, pcd, d], &mut is_removed, &mut ss);
        is_removed.set(cd, true);
        for &v in &adj[cd] {
            if !is_removed[v] {
                stk.push((v, cd, d + 1));
            }
        }
    }
}

/// Heavy-light decomposition
/// MODE = 0 indicates values are on vertices, 1 is values are on edges
pub struct HLD<const MODE: u8> {
    pub n: usize,
    pub pos: Vec<usize>,
    pub rt: Vec<usize>,
    pub ss: Vec<usize>,
    pub tim: usize,
    pub p: Vec<usize>,
}

impl<const MODE: u8> HLD<MODE> {
    pub fn new(adj: &mut [Vec<usize>]) -> Self {
        let n = adj.len();
        let mut pos = vec![0; n];
        let mut rt = vec![0; n];
        let mut ss = vec![1; n];
        let mut tim = 0;
        let mut p = vec![usize::MAX; n];
        let mut stk = Vec::with_capacity(n);
        let mut done = BitVec::new(n, false);
        stk.push((0, 0));
        while let Some((u, e)) = stk.last_mut() {
            let u = *u;
            if *e < adj[u].len() {
                let v = adj[u][*e];
                if v == p[u] {
                    *e += 1;
                    continue;
                }
                if done[v] {
                    ss[u] += ss[v];
                    if ss[v] > ss[adj[u][0]] {
                        adj[u].swap(0, *e);
                    }
                    *e += 1;
                } else {
                    p[v] = u;
                    stk.push((v, 0));
                }
            } else {
                done.set(u, true);
                stk.pop();
            }
        }
        stk.clear();
        done.clear();
        stk.push((0, 0));
        while let Some((u, e)) = stk.last_mut() {
            let u = *u;
            if *e < adj[u].len() {
                let v = adj[u][*e];
                if v == p[u] {
                    *e += 1;
                    continue;
                }
                if done[v] {
                    *e += 1;
                } else {
                    tim += 1;
                    pos[v] = tim;
                    rt[v] = if v == adj[u][0] { rt[u] } else { v };
                    stk.push((v, 0));
                }
            } else {
                done.set(u, true);
                stk.pop();
            }
        }
        Self {
            n,
            pos,
            rt,
            ss,
            tim,
            p,
        }
    }

    #[inline]
    pub fn lca(&self, mut u: usize, mut v: usize) -> usize {
        let (rt, p, pos) = (&self.rt, &self.p, &self.pos);
        while rt[u] != rt[v] {
            if pos[rt[u]] > pos[rt[v]] {
                u = p[rt[u]];
            } else {
                v = p[rt[v]];
            }
        }
        if pos[u] < pos[v] { u } else { v }
    }

    #[inline]
    /// calls o on (inclusive) ranges summing to path from u to v
    pub fn path(&self, mut u: usize, mut v: usize, mut o: impl FnMut(usize, usize)) -> &Self {
        let (rt, p, pos) = (&self.rt, &self.p, &self.pos);
        loop {
            if pos[u] > pos[v] {
                (u, v) = (v, u);
            }
            if rt[u] == rt[v] {
                break;
            }
            o(pos[rt[v]], pos[v]);
            v = p[rt[v]];
        }
        o(pos[u] + MODE as usize, pos[v]);
        self
    }

    /// calls o on (inclusive) range of subtree
    #[inline]
    pub fn subtree(&self, u: usize, o: impl FnOnce(usize, usize)) -> &Self {
        o(self.pos[u] + MODE as usize, self.pos[u] + self.ss[u] - 1);
        self
    }
}

/// Kruskal reconstruction tree
pub struct KRT<F: FnMut(usize, usize, usize)> {
    pub n: usize,
    pub chs: Vec<[usize; 2]>,
    pub nxt: usize,
    pub p: Vec<usize>,
    pub idx: Vec<usize>,
    pub dsu: Vec<usize>,
    pub on_union: F,
}

impl<F: FnMut(usize, usize, usize)> KRT<F> {
    pub fn new(n: usize, on_union: F) -> Self {
        let mut dsu = Vec::with_capacity(n << 1);
        dsu.extend(0..n << 1);
        let mut p = Vec::with_capacity(n << 1);
        p.extend(0..n << 1);
        Self {
            n,
            chs: vec![[usize::MAX; 2]; n << 1],
            nxt: n,
            p,
            idx: vec![usize::MAX; n],
            dsu,
            on_union,
        }
    }

    /// O(log n)
    pub fn find(&mut self, mut x: usize) -> usize {
        while self.dsu[x] != x {
            let p = self.dsu[x];
            self.dsu[x] = self.dsu[p];
            x = p;
        }
        x
    }

    /// O(log n)
    pub fn add_edge(&mut self, u: usize, v: usize, idx: usize) -> &mut Self {
        let (ru, rv) = (self.find(u), self.find(v));
        if ru != rv {
            self.chs[self.nxt] = [ru, rv];
            self.idx[self.nxt - self.n] = idx;
            (self.p[ru], self.p[rv]) = (self.nxt, self.nxt);
            self.dsu[ru] = self.nxt;
            self.dsu[rv] = self.nxt;
            self.nxt += 1;
            (self.on_union)(ru, rv, self.nxt);
        }
        self
    }

    /// O(n)
    pub fn dfs(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let k = self.nxt;
        let mut ss = vec![1; k];
        let mut depth = vec![0; k];
        let mut pos = vec![0; k];
        let mut dfs = vec![0; k];
        for u in 0..k - 1 {
            ss[self.p[u]] += ss[u];
        }
        pos.copy_from_slice(&ss);
        for u in (0..k - 1).rev() {
            let v = self.p[u];
            depth[u] = depth[v] + 1;
            (pos[u], pos[v]) = (pos[v], pos[v] - pos[u]);
        }
        for i in 0..k {
            pos[i] -= 1;
            dfs[pos[i]] = i;
        }
        (ss, pos, dfs, depth)
    }

    /// O(n) construction, O(1) query
    pub fn leaf_pos_rmq(
        &self,
        pos: &[usize],
    ) -> (
        RMQ<impl FnMut(usize, usize) -> Ordering>,
        RMQ<impl FnMut(usize, usize) -> Ordering>,
    ) {
        (
            RMQ::new(self.n, |i, j| pos[i].cmp(&pos[j])),
            RMQ::new(self.n, |i, j| pos[j].cmp(&pos[i])),
        )
    }

    /// O(n) construction O(1) query
    pub fn lca<'a>(
        &'a self,
        dfs: &'a [usize],
        pos: &'a [usize],
        depth: &'a [usize],
    ) -> LCA<'a, impl FnMut(usize, usize) -> Ordering> {
        let k = self.nxt;
        let mut z = Vec::with_capacity(k);
        z.extend((0..k).map(|i| depth[self.p[dfs[i]]]));
        let lca = LCA::new(k, &self.p, dfs, pos, move |i, j| z[i].cmp(&z[j]));
        lca
    }
}

// SECTION: geo

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

impl<T> Point<T> {
    pub fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
}

impl<T: Display> Debug for Point<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "⟨{}, {}⟩", self.x, self.y)
    }
}

impl<S, R: Add<Output = S>, T: Clone + Mul<Output = R>> Point<T> {
    pub fn dot(&self, rhs: &Point<T>) -> S {
        self.x.clone() * rhs.x.clone() + self.y.clone() * rhs.y.clone()
    }
}

impl<S, R: Sub<Output = S>, T: Clone + Mul<Output = R> + Sub<Output = T>> Point<T> {
    pub fn cross(&self, rhs: &Point<T>) -> S {
        self.x.clone() * rhs.y.clone() - self.y.clone() * rhs.x.clone()
    }
}

impl<S, R: Sub<Output = S>, T: Clone + Mul<Output = R> + Sub<Output = T>> Point<T> {
    pub fn area(&self, a: &Point<T>, b: &Point<T>) -> S {
        (a.clone() - self.clone()).cross(&(b.clone() - self.clone()))
    }
}

impl<R, S, T: Add<S, Output = R>> Add<Point<S>> for Point<T> {
    type Output = Point<R>;

    fn add(self, rhs: Point<S>) -> Self::Output {
        Point {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<S, T: AddAssign<S>> AddAssign<Point<S>> for Point<T> {
    fn add_assign(&mut self, rhs: Point<S>) {
        self.x += rhs.x;
        self.y += rhs.y;
    }
}

impl<R, S, T: Sub<S, Output = R>> Sub<Point<S>> for Point<T> {
    type Output = Point<R>;

    fn sub(self, rhs: Point<S>) -> Self::Output {
        Point {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<S, T: SubAssign<S>> SubAssign<Point<S>> for Point<T> {
    fn sub_assign(&mut self, rhs: Point<S>) {
        self.x -= rhs.x;
        self.y -= rhs.y;
    }
}

impl<R, S: Clone, T: Mul<S, Output = R>> Mul<S> for Point<T> {
    type Output = Point<R>;

    fn mul(self, rhs: S) -> Self::Output {
        Point {
            x: self.x * rhs.clone(),
            y: self.y * rhs,
        }
    }
}

impl<S: Clone, T: MulAssign<S>> MulAssign<S> for Point<T> {
    fn mul_assign(&mut self, rhs: S) {
        self.x *= rhs.clone();
        self.y *= rhs;
    }
}

impl<R, S: Clone, T: Div<S, Output = R>> Div<S> for Point<T> {
    type Output = Point<R>;

    fn div(self, rhs: S) -> Self::Output {
        Point {
            x: self.x / rhs.clone(),
            y: self.y / rhs,
        }
    }
}

impl<S: Clone, T: DivAssign<S>> DivAssign<S> for Point<T> {
    fn div_assign(&mut self, rhs: S) {
        self.x /= rhs.clone();
        self.y /= rhs;
    }
}

pub fn convex_hull<T: Clone + Ord + Default + Mul<T, Output = T> + Sub<T, Output = T>>(
    pts: &mut [Point<T>],
) -> Vec<Point<T>> {
    let n = pts.len();
    let mut hull = Vec::new();
    if n < 3 {
        hull.extend_from_slice(pts);
        return hull;
    }
    pts.sort_unstable();
    for i in 0..n {
        while hull.len() > 1
            && hull[hull.len() - 2]
                .clone()
                .area(&hull[hull.len() - 1], &pts[i])
                <= T::default()
        {
            hull.pop();
        }
        hull.push(pts[i].clone());
    }
    let lower_len = hull.len();
    for i in (0..n).rev() {
        while hull.len() > lower_len
            && hull[hull.len() - 2]
                .clone()
                .area(&hull[hull.len() - 1], &pts[i])
                <= T::default()
        {
            hull.pop();
        }
        hull.push(pts[i].clone());
    }
    hull.pop();
    hull
}

pub fn hilbert(mut x: u64, mut y: u64, k: u64) -> u64 {
    let mut d = 0;
    let mut s = k >> 1;
    while s != 0 {
        let (rx, ry) = ((x & s != 0) as u64, (y & s != 0) as u64);
        d <<= 2;
        d |= (3 * rx) ^ ry;
        let mut mask = (ry ^ 1).wrapping_neg();
        x ^= y & mask;
        y ^= x & mask;
        x ^= y & mask;
        mask &= rx.wrapping_neg();
        x ^= mask;
        y ^= mask;
        s >>= 1;
    }
    d
}

// SECTION: io

#[derive(Default)]
struct Scanner {
    buffer: Vec<String>,
}

impl Scanner {
    fn next<T: std::str::FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}

use itertools::Itertools;
use rand::Rng;
use std::cmp::Ordering;
#[allow(unused_imports)]
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::io::{BufWriter, Write, stdin, stdout};
use std::mem::MaybeUninit;
use std::ops::BitXorAssign;
use std::{
    fmt::{Debug, Display},
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};
