// TODO: implement algorithm for frobenius form
// https://codeforces.com/blog/entry/124815

use crate::alg::ops::inverse_euclidean;
use itertools::Itertools;
use std::{
    fmt::Debug,
    ops::{AddAssign, Index, IndexMut, Mul, SubAssign},
};

type E = i64;

/// Matrix with elements in Z/MZ
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
    pub fn from_slice(n: usize, m: usize, s: &[E]) -> Self {
        Self {
            n,
            m,
            elems: s.to_vec(),
        }
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
    pub fn pow(self, mut rhs: u32) -> Self {
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

    // https://codeforces.com/blog/entry/124815
    // TODO: frobenius form algorithm
    pub fn frobenius() {}

    // https://judge.yosupo.jp/submission/285790
    // TODO: characteristic polynomial
    pub fn charpoly() {}

    // https://judge.yosupo.jp/submission/285768
    // TODO: fast pow
    pub fn fast_pow() {}
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

#[cfg(test)]
mod tests {
    use super::*;
    const M: u64 = (15 << 27) + 1;

    #[test]
    fn pow_tests() {
        let a = Mat::<M>::eye(3, 3);
        let b = a.clone().pow(1000);
        assert_eq!(a, b, "Identity raised to power should remain identity");

        let a = Mat::<M>::from_fn(3, 3, |(i, j)| if i == j { 2 } else { 0 });
        let b = a.pow(10);
        for i in 0..3 {
            for j in 0..3 {
                if i == j {
                    assert_eq!(b[(i, j)], 1024 % M as i64);
                } else {
                    assert_eq!(b[(i, j)], 0);
                }
            }
        }
    }

    fn dummy(_: usize) {}

    #[test]
    fn rank_tests() {
        let a = Mat::<M>::eye(5, 5);
        let rank = a.clone().rank(dummy, dummy);
        assert_eq!(rank, 5, "Identity matrix should have full rank");

        let a = Mat::<M>::from_elem(4, 4, 0);
        let rank = a.clone().rank(dummy, dummy);
        assert_eq!(rank, 0, "Zero matrix should have rank 0");

        let a = Mat::<M>::from_fn(3, 4, |(_, j)| j as i64); // All rows equal
        let rank = a.clone().rank(dummy, dummy);
        assert_eq!(rank, 1, "All rows equal should give rank 1");

        let mut a = Mat::<M>::from_elem(3, 3, 0);
        a[(0, 0)] = 1;
        a[(1, 0)] = M as i64; // ≡ 0 mod M
        let rank = a.clone().rank(dummy, dummy);
        assert_eq!(rank, 1, "Element equal to modulus should be zero mod M");
    }

    #[test]
    fn inv_tests() {
        let a = Mat::from_slice(3, 3, &[1, 2, 3, 4, 5, 6, 7, 8, 10]);
        let (det, rk, inv) = a.inv(dummy, dummy);
        assert_eq!(rk, 3, "Should be full rank");
        assert_ne!(det, 0, "Should have non-zero determinant");
        let mut prod = &a * &inv;
        assert_eq!(
            prod.normalize(),
            &Mat::<M>::eye(3, 3),
            "A * A^-1 must be identity"
        );

        let mut a = Mat::<M>::from_elem(3, 3, 0);
        a[(0, 0)] = 1;
        a[(1, 0)] = 1;
        a[(2, 0)] = 1;
        let (det, rk, inv) = a.inv(dummy, dummy);
        assert_eq!(rk, 1, "Rank should reflect row span");
        assert_eq!(det, 0, "Singular matrix must have zero determinant");
        assert_eq!(inv.n, 0, "Should not return inverse for singular matrix");

        let mut a = Mat::<M>::eye(2, 2);
        a[(0, 0)] = M as i64; // ≡ 0 mod M
        let (_, rk, _) = a.inv(dummy, dummy);
        assert!(
            rk < 2,
            "Matrix with zero on diagonal mod M should not be full rank"
        );

        let a = Mat::from_fn(10, 10, |(i, j)| (-(i as E)).pow(j as u32) % M as E);
        let (det, rk, inv) = a.inv(dummy, dummy);
        assert_eq!(rk, 10);
        assert_ne!(det, 0);
        let mut prod = &a * &inv;
        prod.pos_normalize();
        let id = Mat::<M>::eye(10, 10);
        assert_eq!(prod, id);
    }
}
