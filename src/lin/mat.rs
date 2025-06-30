// TODO: implement algorithm for frobenius form
// https://codeforces.com/blog/entry/124815

use crate::alg::ops::inverse_euclidean;
use itertools::Itertools;
use std::{
    fmt::Debug,
    ops::{AddAssign, Index, IndexMut, Mul, SubAssign},
};

type E = u64;

/// Matrix with elements in Z/MZ
#[derive(Clone)]
pub struct Mat<const M: E> {
    pub n: usize,
    pub m: usize,
    pub elems: Vec<E>,
}

impl<const M: E> Mat<M> {
    #[inline]
    pub fn eye(n: usize, m: usize) -> Mat<M> {
        let mut elems = vec![0; n * m];
        for i in 0..n.min(m) {
            elems[(m + 1) * i] = 1;
        }
        Mat { n, m, elems }
    }

    #[inline]
    pub fn from_elem(n: usize, m: usize, v: u64) -> Mat<M> {
        Mat {
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
        Mat { n, m, elems }
    }

    #[inline]
    pub fn from_slice(n: usize, m: usize, s: &[E]) -> Self {
        Mat {
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
    pub fn transpose(&mut self) -> Mat<M> {
        Mat::from_fn(self.m, self.n, |(i, j)| self[(j, i)])
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
    pub fn concat_rows(&self, rhs: &Self) -> Mat<M> {
        if self.m == 0 {
            return Mat {
                n: self.n,
                m: rhs.m,
                elems: rhs.elems.clone(),
            };
        }
        if rhs.m == 0 {
            return Mat {
                n: self.n,
                m: self.m,
                elems: self.elems.clone(),
            };
        }
        Mat {
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
        self.elements_mut().for_each(|v| *v %= M);
        self
    }

    #[inline]
    pub fn normalize_row(&mut self, i: usize) -> &mut Self {
        self[i].iter_mut().for_each(|v| *v %= M);
        self
    }

    #[inline]
    pub fn normalize_col(&mut self, i: usize) -> &mut Self {
        self.col_mut(i).for_each(|v| *v %= M);
        self
    }

    #[inline]
    pub fn negate(&mut self) -> &mut Self {
        self.normalize();
        self.elements_mut().for_each(|v| *v = M - *v);
        self
    }

    #[inline]
    pub fn pow(self, mut rhs: u32) -> Mat<M> {
        let mut res = Mat::eye(self.n, self.m);
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

    /// Does not normalize, if matrices have been normalized will be wrong
    #[inline]
    pub fn diamond(&self, rhs: &Self) -> Self {
        let mut c = Mat::from_elem(self.n, rhs.m, 0);
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
            row_i.iter_mut().for_each(|v| *v %= M);
            let p = row_i.iter().position(|&v| v != 0);
            if let Some(p) = p {
                let p_inv = inverse_euclidean::<M>(self[(i, p)]);
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
                    let a = (row_j[p] * p_inv) % M;
                    row_j
                        .iter_mut()
                        .zip(row_i.iter().map(|&j| M - (a * j) % M))
                        .skip(p)
                        .for_each(|(i, j)| *i += j);
                    row_j.iter_mut().skip(p).for_each(|i| *i %= M);
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
            if rk < self.n && self[rk][j] % M == 0 {
                for i in rk + 1..self.n {
                    if self[i][j] % M != 0 {
                        let [row_i, row_rk] = self
                            .elems
                            .get_disjoint_mut([
                                i * self.m..(i + 1) * self.m,
                                rk * self.m..(rk + 1) * self.m,
                            ])
                            .unwrap();
                        row_i.swap_with_slice(row_rk);
                        row_rk.iter_mut().for_each(|i| *i = (M - *i) % M);
                        break;
                    }
                }
            }
            if rk < self.n && self[rk][j] % M != 0 {
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

    pub fn rank(&mut self, mut f: impl FnMut(usize), g: impl FnMut(usize)) -> E {
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
            res %= M;
        }
        res
    }

    pub fn inv(&self, mut f: impl FnMut(usize), g: impl FnMut(usize)) -> (E, usize, Mat<M>) {
        let n = self.n;
        let mut a = self.concat_rows(&Mat::eye(n, n));
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
                Mat {
                    n: 0,
                    m: 0,
                    elems: vec![],
                },
            );
        }
        let mut det = 1;
        for i in 0..n {
            let a_ii = a[i][i] % M;
            det *= a_ii;
            det %= M;
            let a_ii_inv = inverse_euclidean::<M>(a_ii);
            let row_i = &mut a[i];
            row_i.iter_mut().for_each(|i| *i *= a_ii_inv);
            row_i.iter_mut().for_each(|i| *i %= M);
        }
        let mut counter = 0;
        (
            det,
            rk,
            Mat {
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
            },
        )
    }

    pub fn ker(&self, mut f: impl FnMut(usize), mut g: impl FnMut(usize)) -> Mat<M> {
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
        let mut sols = Mat::from_elem(free.len(), a.m, 0);
        for j in 0..pivots.len() {
            let b = inverse_euclidean::<M>(a[(j, pivots[j])]);
            for i in 0..free.len() {
                sols[(i, pivots[j])] = (a[(j, free[i])] * b) % M;
            }
        }
        for i in 0..free.len() {
            sols[(i, free[i])] = M - 1;
        }
        sols
    }

    pub fn solve(
        &self,
        t: &Mat<M>,
        f: impl FnMut(usize),
        g: impl FnMut(usize),
    ) -> Option<[Mat<M>; 2]> {
        let a = self.concat_rows(t);
        let sols = a.ker(f, g);
        if sols.n < t.m {
            return None;
        }
        for i in 0..t.m {
            for j in 0..t.m {
                if sols[(sols.n - t.m + i, self.m + j)] % M != if i == j { M - 1 } else { 0 } {
                    return None;
                }
            }
        }
        let mut x_t = Mat::from_elem(t.m, self.m, 0);
        for i in 0..t.m {
            x_t[i]
                .iter_mut()
                .zip(&sols[sols.n - t.m + i])
                .for_each(|(i, &j)| *i = j);
        }
        let mut ker = Mat::from_elem(sols.n - t.m, self.m, 0);
        for i in 0..sols.n - t.m {
            ker[i].iter_mut().zip(&sols[i]).for_each(|(i, &j)| *i = j);
        }
        Some([x_t, ker])
    }
}

impl<const M: E> Debug for Mat<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}×{} matrix mod {}:", self.n, self.m, M)?;
        for i in 0..self.n {
            writeln!(f, "{:?}", &self[i])?;
        }
        Ok(())
    }
}

impl<const M: E> Index<usize> for Mat<M> {
    type Output = [E];

    fn index(&self, i: usize) -> &Self::Output {
        &self.elems[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: E> IndexMut<usize> for Mat<M> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.elems[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: E> Index<(usize, usize)> for Mat<M> {
    type Output = E;

    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.elems[i * self.m + j]
    }
}

impl<const M: E> IndexMut<(usize, usize)> for Mat<M> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.elems[i * self.m + j]
    }
}

impl<const M: E> PartialEq for Mat<M> {
    fn eq(&self, other: &Self) -> bool {
        for (a, b) in self.elements().zip(other.elements()) {
            if a != b {
                return false;
            }
        }
        true
    }
}

impl<const M: E> Eq for Mat<M> {}

impl<const M: E> AddAssign for Mat<M> {
    fn add_assign(&mut self, rhs: Self) {
        self.elements_mut()
            .zip(rhs.elements())
            .for_each(|(v, w)| *v += w);
    }
}

impl<const M: E> SubAssign for Mat<M> {
    fn sub_assign(&mut self, rhs: Self) {
        self.elements_mut().zip(rhs.elements()).for_each(|(v, w)| {
            *v += M - w;
        });
    }
}

impl<'a, const M: E> Mul<&'a Mat<M>> for &'a Mat<M> {
    type Output = Mat<M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut c = Mat::from_elem(self.n, rhs.m, 0);
        for i in 0..self.n {
            let row_a = &self[i];
            let row_c = &mut c[i];
            for k in 0..self.m {
                let a_ik = row_a[k];
                row_c
                    .iter_mut()
                    .zip(&rhs[k])
                    .for_each(|(i, &j)| *i += a_ik * j);
                if k & 7 == 0 {
                    row_c.iter_mut().for_each(|i| *i %= M);
                }
            }
        }
        c.normalize();
        c
    }
}
