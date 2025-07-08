use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

/// O(n log log n)
pub fn divisor<T: for<'a> AddAssign<&'a T>>(a: &mut [T], primes: &[usize]) {
    let n = a.len() - 1;
    for &p in primes {
        let mut i = 1;
        let mut j = p;
        while j <= n {
            let [a_j, a_i] = a.get_disjoint_mut([j, i]).unwrap();
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
            let [a_j, a_i] = a.get_disjoint_mut([j, i]).unwrap();
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
            let [a_i, a_j] = a.get_disjoint_mut([i, j]).unwrap();
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
            let [a_i, a_j] = a.get_disjoint_mut([i, j]).unwrap();
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

/// O(n log n)
pub fn subset<T: for<'a> AddAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                let [a_j, a_jk] = a.get_disjoint_mut([j, j + k]).unwrap();
                *a_j += &*a_jk;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn subset_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                let [a_j, a_jk] = a.get_disjoint_mut([j, j + k]).unwrap();
                *a_j -= &*a_jk;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn and_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
) {
    subset(a);
    subset(&mut b);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    subset(a);
}

/// O(n log^2 n)
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
        superset(&mut fhat[i]);
        superset(&mut ghat[i]);
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
        superset_inv(&mut h[i]);
    }
    for m in 0..1 << n {
        a[m] = h[m.count_ones() as usize][m].clone();
    }
}

/// O(n log n)
pub fn superset<T: for<'a> AddAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                let [a_jk, a_j] = a.get_disjoint_mut([j + k, j]).unwrap();
                *a_jk += &*a_j;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn superset_inv<T: for<'a> SubAssign<&'a T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                let [a_jk, a_j] = a.get_disjoint_mut([j + k, j]).unwrap();
                *a_jk -= &*a_j;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn or_conv<T: for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T> + MulAssign>(
    a: &mut [T],
    mut b: Vec<T>,
) {
    superset(a);
    superset(&mut b);
    a.iter_mut().zip(b.into_iter()).for_each(|(i, j)| *i *= j);
    superset_inv(a);
}

/// O(n log n)
pub fn xor<T>(a: &mut [T])
where
    T: Clone + for<'a> AddAssign<&'a T> + for<'a> SubAssign<&'a T>,
{
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                let v = a[j + k].clone();
                a[j + k] = a[j].clone();
                a[j + k] -= &v;
                a[j] += &v;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
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

/// O(n log n)
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
