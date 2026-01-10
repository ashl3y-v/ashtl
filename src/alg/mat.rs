use crate::alg::{
    fps::Poly,
    ops::{inv, inverse_euclidean},
};
use itertools::Itertools;
use rand::Rng;
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

    pub fn adjugate(&self) -> Self {
        let n = self.n;
        let mut rng = rand::rng();
        let a = Self::from_fn(n + 1, n + 1, |(i, j)| {
            if i == n && j == n {
                0
            } else if i == n || j == n {
                rng.random_range(0..M as E)
            } else {
                self[i][j]
            }
        });
        let (d, _, a) = a.inv(|_| {}, |_| {});
        if d == 0 {
            Self::from_vec(n, n, vec![0; n * n])
        } else {
            Self::from_fn(n, n, |(i, j)| {
                (a[n][n] * a[i][j] - a[i][n] * a[n][j]) % M as E * d % M as E
            })
        }
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

    pub fn minp_bb(n: usize, mut f: impl FnMut(Vec<E>) -> Vec<E>) -> Poly<M> {
        let m = 2 * n + 10;
        let mut rng = rand::rng();
        let (mut s, c, mut v) = (
            vec![0; m],
            (0..n)
                .map(|_| rng.random_range(0..M as E))
                .collect::<Vec<_>>(),
            (0..n)
                .map(|_| rng.random_range(0..M as E))
                .collect::<Vec<_>>(),
        );
        for k in 0..m {
            s[k] = c.iter().zip(&v).map(|(&a, &b)| a * b % M as E).sum();
            v = f(v);
            v.iter_mut().for_each(|a| *a %= M as E);
        }
        Poly::new(s).normalize().min_rec(m).reverse()
    }

    pub fn det_bb(n: usize, mut f: impl FnMut(Vec<E>) -> Vec<E>) -> E {
        let mut rng = rand::rng();
        let c = (0..n)
            .map(|_| rng.random_range(0..M as E))
            .collect::<Vec<_>>();
        let r = c.iter().fold(1, |a, b| a * b % M as E);
        let g = |mut v: Vec<E>| {
            v.iter_mut().zip(&c).for_each(|(a, b)| *a *= b);
            f(v)
        };
        let p = Self::minp_bb(n, g);
        let mut det = if p.len() == n + 1 { p[0] } else { 0 };
        if n & 1 != 0 {
            det = -det;
        }
        det % M as E * inv::<M>(r) % M as E
    }

    pub fn solve_bb(v: Vec<E>, mut f: impl FnMut(Vec<E>) -> Vec<E>) -> Vec<E> {
        let n = v.len();
        let m = 2 * n + 10;
        let mut rng = rand::rng();
        let (mut s, c, mut w) = (
            vec![0; m],
            (0..n)
                .map(|_| rng.random_range(0..M as E))
                .collect::<Vec<_>>(),
            v.clone(),
        );
        for k in 0..m {
            s[k] = c.iter().zip(&w).map(|(&a, &b)| a * b % M as E).sum();
            w = f(w);
            w.iter_mut().for_each(|a| *a %= M as E);
        }
        let p = Poly::<M>::new(s)
            .normalize()
            .min_rec(m)
            .reverse()
            .normalize();
        let m0 = p[0];
        let (p, d) = ((p >> 1) / -m0).truncate_deg_or_0();
        let mut res = v.clone();
        res.iter_mut().for_each(|a| *a = (*a * p.coeff[d]) % M as E);
        for i in (0..d).rev() {
            res = f(res);
            res.iter_mut()
                .zip(&v)
                .for_each(|(a, b)| *a = (*a + p.coeff[i] * b) % M as E);
        }
        res
    }

    pub fn hessenberg(&mut self) {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        for k in 0..n - 2 {
            for i in k + 1..n {
                if self[i][k] != 0 {
                    if i != k + 1 {
                        for j in 0..n {
                            self.elems.swap(i * n + j, (k + 1) * n + j);
                        }
                        for j in 0..n {
                            self.elems.swap(j * n + i, j * n + k + 1);
                        }
                    }
                    break;
                }
            }
            if self[k + 1][k] == 0 {
                continue;
            }
            for i in k + 2..n {
                let c = self[i][k] * inv::<M>(self[k + 1][k]) % M as E;
                for j in 0..n {
                    self[i][j] = (self[i][j] - self[k + 1][j] * c) % M as E;
                }
                for j in 0..n {
                    self[j][k + 1] = (self[j][k + 1] + self[j][i] * c) % M as E;
                }
            }
        }
    }

    /// O(n^3)
    pub fn charp(mut self) -> Poly<M> {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        self.hessenberg();
        let mut dp = vec![vec![]; n + 1];
        dp[0] = vec![1];
        for k in 0..n {
            dp[k + 1].resize(k + 2, 0);
            for i in 0..dp[k].len() {
                dp[k + 1][i + 1] += dp[k][i];
            }
            let c = self[k][k] % M as E;
            for i in 0..dp[k].len() {
                dp[k + 1][i] = (dp[k + 1][i] - dp[k][i] * c) % M as E;
            }
            let mut prod = 1;
            for i in (0..k).rev() {
                prod = prod * self[i + 1][i] % M as E;
                let c = prod * self[i][k] % M as E;
                for j in 0..dp[i].len() {
                    dp[k + 1][j] = (dp[k + 1][j] - dp[i][j] * c) % M as E;
                }
            }
        }
        Poly::<M>::new(std::mem::take(&mut dp[n]))
    }

    /// O(n^3)
    pub fn det_aff(mut self, mut rhs: Self) -> Poly<M> {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        let a = rand::rng().random_range(1..M as E);
        self.elems
            .iter_mut()
            .zip(&rhs.elems)
            .for_each(|(i, j)| *i = (*i + a * j) % M as E);
        let (d, _, inv) = self.inv(|_| {}, |_| {});
        if d == 0 {
            return Poly::<M>::new(vec![0; n + 1]);
        }
        rhs = rhs * inv;
        rhs.elems.iter_mut().for_each(|a| *a = -*a);
        (rhs.charp().reverse() * d).shift(-a)
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

    // https://maspypy.github.io/library/linalg/diagonalize_triangular_matrix.hpp

    // https://codeforces.com/blog/entry/124815
    /// O(n^3)
    pub fn frob(&self) -> (Vec<Poly<M>>, Self, Self) {
        let n = self.n;
        debug_assert_eq!(n, self.m);
        let mut charps: Vec<Poly<M>> = Vec::new();
        let (mut basis, mut basis_init): (Vec<Vec<E>>, Vec<Vec<E>>) =
            (Vec::with_capacity(n), Vec::with_capacity(n));
        let gen_block = |mut x: Vec<E>,
                         a: &Self,
                         basis: &mut Vec<Vec<E>>,
                         basis_init: &mut Vec<Vec<E>>,
                         n: usize| {
            loop {
                let mut y = x.clone();
                let l = y.len();
                y.resize(l + n + 1, 0);
                y[l + basis.len()] = 1;
                for v in &*basis {
                    Self::reduce_by(&mut y, &v);
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
        };
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

    // TODO: hafnian
    // https://maspypy.github.io/library/linalg/hafnian.hpp
    pub fn hafnian(mut self) -> Poly<M> {
        unimplemented!()
    }
}

impl<const M: u64> Debug for Mat<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
                    assert_eq!(b[(i, j)].rem_euclid(M as i64), 1024 % M as i64);
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
