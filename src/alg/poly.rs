use super::{
    lattice,
    ntt::{intt, ntt, ntt_conv, ntt_conv_self},
    ops::{
        inverse_euclidean, inverses, inverses_n_div, mod_fact, mod_k_rt, mod_pow, mod_pow_signed,
        mod_rfact, mod_sqrt,
    },
    prime,
    primitive::find_primitive_root,
    sieve::{self, sieve_complete},
    special,
};
use std::{
    fmt::Debug,
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

type E = i64;

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
    pub fn from_elem(a: E, n: usize) -> Self {
        Self { coeff: vec![a; n] }
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
    pub fn resize_max(mut self, n: usize) -> Self {
        self.coeff.resize(self.len().max(n), 0);
        self
    }

    #[inline]
    pub fn push(mut self, v: E) -> Self {
        self.coeff.push(v);
        self
    }

    #[inline]
    pub fn pop(mut self) -> Self {
        self.coeff.pop();
        self
    }

    #[inline]
    pub fn copy(mut self, rhs: &Self) -> Self {
        self.coeff.copy_from_slice(&rhs.coeff);
        self
    }

    #[inline]
    pub fn copy_n(mut self, n: usize, rhs: &Self) -> Self {
        let l = self.len();
        self.coeff[0..n.min(l)].copy_from_slice(&rhs.coeff[0..n.min(l)]);
        self
    }

    #[inline]
    pub fn truncate_deg(self) -> Self {
        let d = self.deg_or_0();
        self.mod_xn(d + 1)
    }

    #[inline]
    pub fn truncate_and_deg(self) -> (Self, Option<usize>) {
        let d = self.deg();
        (self.mod_xn(d.map(|i| i + 1).unwrap_or(0)), d)
    }

    #[inline]
    pub fn truncate_and_deg_or_0(self) -> (Self, usize) {
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
    pub fn normalize_n(mut self, n: usize) -> Self {
        self.coeff.iter_mut().take(n).for_each(|i| {
            *i = i.rem_euclid(M as E);
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
    pub fn mul_xn(mut self, n: usize) -> Self {
        if n == 0 {
            return self;
        }
        let old_len = self.coeff.len();
        self = self.resize(old_len + n);
        for i in (0..old_len).rev() {
            self.coeff[i + n] = self.coeff[i];
        }
        for i in 0..n {
            self.coeff[i] = 0;
        }
        self
    }

    #[inline]
    pub fn div_xn(mut self, n: usize) -> Self {
        if n == 0 {
            return self;
        }
        if self.coeff.len() <= n {
            self.coeff.clear();
            return self;
        }
        for i in 0..self.coeff.len() - n {
            self.coeff[i] = self.coeff[i + n];
        }
        self.coeff.truncate(self.coeff.len() - n);
        self
    }

    #[inline]
    pub fn reverse(mut self) -> Self {
        self = self.truncate_deg();
        self.coeff.reverse();
        self
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
    pub fn complement(mut self) -> Self {
        let n = self.coeff.len();
        for i in 0..n >> 1 {
            self.coeff.swap(i, i ^ (n - 1));
        }
        self
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
    pub fn bit_reverse(self) -> Self {
        let n = self.len();
        let l = n.trailing_zeros();
        self.permute(|i| i.reverse_bits() >> usize::BITS - l, n)
    }

    #[inline]
    pub fn bisect(&self, n: usize) -> (Self, Self) {
        let n = n.min(self.len());
        let (mut p0, mut p1) = (
            Self {
                coeff: Vec::with_capacity((n + 1) >> 1),
            },
            Self {
                coeff: Vec::with_capacity((n + 1) >> 1),
            },
        );
        let mut i = 1;
        while i < n {
            p0.coeff.push(self.coeff[i ^ 1]);
            p1.coeff.push(self.coeff[i]);
            i += 2;
        }
        if n & 1 != 0 {
            p0.coeff.push(self.coeff[n ^ 1]);
        }
        (p0, p1)
    }

    #[inline]
    pub fn even(mut self, n: usize) -> Self {
        let p = ((self.len() + 1) >> 1).min(n);
        for i in 0..p {
            self.coeff[i] = self.coeff[i << 1];
        }
        for i in p..self.len() {
            self.coeff[i] = 0;
        }
        self
    }

    #[inline]
    pub fn odd(mut self, n: usize) -> Self {
        let p = (self.len() >> 1).min(n);
        for i in 0..p {
            self.coeff[i] = self.coeff[i << 1 | 1];
        }
        for i in p..self.len() {
            self.coeff[i] = 0;
        }
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
    pub fn erase(mut self, range: impl Iterator<Item = usize>) -> Self {
        for i in range {
            self.coeff[i] = 0;
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

    /// O(k n log k (log k + log n))
    pub fn prod(mut ps: Vec<Self>) -> Self {
        fn prod<const M: u64>(l: usize, r: usize, ps: &mut Vec<Poly<M>>) -> Poly<M> {
            if l + 1 == r {
                return std::mem::take(&mut ps[l]);
            }
            let m = l + (r - l >> 1);
            prod(l, m, ps) * prod(m, r, ps)
        }
        prod(0, ps.len(), &mut ps)
    }

    /// O(n log^2 n)
    pub fn prod_linear(mut self) -> Self {
        fn prod<const M: u64>(l: usize, r: usize, x: &mut [E]) -> Poly<M> {
            if l + 1 == r {
                return Poly::<M>::new(vec![-std::mem::take(&mut x[l]), 1]);
            }
            let m = l + (r - l >> 1);
            prod(l, m, x) * prod(m, r, x)
        }
        prod(0, self.coeff.len(), &mut self.coeff)
    }

    /// O(n log n)
    pub fn prod_arithmetic(a: E, b: E, n: usize) -> Self {
        (Self::stirling1(n).mulx_a(inverse_euclidean::<M, _>(b))
            * mod_pow::<M>(b.rem_euclid(M as E) as u64, n as u64) as E)
            .shift(-a)
    }

    /// O(n)
    pub fn prod_geometric(a: E, b: E, n: usize) -> Self {
        Self::prod_1pzitx(b, -a, n, n + 1).reverse_k(n)
    }

    // TODO: half-gcd algorithm
    // https://codeforces.com/blog/entry/101850
    /// O(n log^2 n)
    pub fn half_gcd(self) {
        unimplemented!();
    }

    /// O(n log^2 n)
    pub fn full_gcd(self) {
        unimplemented!();
    }

    /// O(s log^2 s)
    pub fn convergent() {
        unimplemented!()
    }

    // https://codeforces.com/blog/entry/101628
    // https://judge.yosupo.jp/submission/196170
    /// O(d log^2 d)
    pub fn min_rec(self) {
        unimplemented!();
    }

    /// O(n log^2 n)
    pub fn inv_mod() {
        unimplemented!()
    }

    /// O(n log^2 n)
    #[inline]
    pub fn resultant(self) -> E {
        unimplemented!()
    }

    // https://judge.yosupo.jp/problem/polynomial_root_finding
    pub fn roots() {
        unimplemented!()
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
        let a0_inv = inverse_euclidean::<M, _>(a0);
        let mut r = Self::new(vec![a0_inv as E]).resize(n.next_power_of_two());
        let mut k = 1;
        while k < n {
            let g = r.clone_resize(k << 1).ntt();
            let f = self
                .clone_resize(k << 1)
                .ntt()
                .dot(&g)
                .intt()
                .erase_range(0..k)
                .normalize()
                .ntt()
                .dot(&g)
                .intt();
            for i in k..(k << 1).min(r.len()) {
                r[i] = -f[i] % M as E;
            }
            k <<= 1;
        }
        Some(r)
    }

    /// O(n log n)
    pub fn dir_inv(&self, n: usize) -> Option<Self> {
        if self.coeff[1] % M as E == 0 {
            return None;
        }
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let mut g = vec![0; n];
        let f1 = self.coeff[1];
        let f1_inv = inverse_euclidean::<M, _>(f1);
        g[1] = inverse_euclidean::<M, _>(f1);
        let mut p = vec![0; n];
        for i in 2..n.min(m) {
            p[i] = -g[1] * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            g[i] = p[i] * f1_inv % M as E * big_omega_invs[i - 2] % M as E;
            let v = g[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * (big_omega[j / i] * -g[i] % M as E - v) % M as E;
            }
        }
        Some(Self::new(g))
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
    pub fn lead(&self) -> E {
        self.coeff[self.deg_or_0()]
    }

    #[inline]
    pub fn lead_inv(&self) -> E {
        inverse_euclidean::<M, _>(self.coeff[self.deg_or_0()])
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        !self.coeff.iter().any(|&i| i % M as E != 0)
    }

    #[inline]
    pub fn diff(self) -> Self {
        self.diff_x() >> 1
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
    pub fn diff_k(self, k: usize) -> Self {
        (self.inv_borel() >> k).borel()
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
    pub fn integr(self) -> Self {
        (self << 1).integr_divx()
    }

    #[inline]
    pub fn integr_divx(mut self) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        self.coeff
            .iter_mut()
            .zip(inverses_n_div::<M>(d + 1))
            .for_each(|(v, inv)| *v = (*v * inv as E) % M as E);
        self
    }

    /// O(n)
    #[inline]
    pub fn integr_k(self, k: usize) -> Self {
        (self.inv_borel() << k).borel()
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
    pub fn trailing_xk(&self) -> Option<usize> {
        self.coeff.iter().position(|&i| i % M as E != 0)
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
        let mut g = vec![0; n];
        let f1 = self.coeff[1];
        self = (self / f1).normalize();
        g[1] = 0;
        let mut p = vec![0; n];
        for i in 2..n.min(m) {
            g[i] = (self.coeff[i] - p[i] * big_omega_invs[i - 2] % M as E) % M as E;
            let v = g[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * v % M as E;
            }
        }
        for i in n.min(m)..n {
            g[i] = -p[i] * big_omega_invs[i - 2] % M as E;
            let v = g[i] * big_omega[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * v % M as E;
            }
        }
        Some(Self::new(g))
    }

    /// O(n log n)
    pub fn exp(&self, n: usize) -> Option<Self> {
        if self.coeff.get(0).copied().unwrap_or(0) % M as E != 0 {
            return None;
        } else if self.len() <= 1 {
            return Some(Self::new(vec![1]));
        }
        let n = n.next_power_of_two();
        let mut e_k = Self::new(Vec::with_capacity(n)).push(1).push(self.coeff[1]);
        let mut e_k_inv = Self::new(Vec::with_capacity(n)).push(1);
        let mut e_k_ntt = Self::new(Vec::with_capacity(n)).resize(2);
        let mut e_k_inv_ntt = Self::new(Vec::with_capacity(n)).push(1).push(1);
        let mut i = 1;
        while i < n >> 1 {
            e_k_ntt = e_k_ntt.copy(&e_k).resize(i << 2).ntt();
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
            e_k_inv_ntt = e_k_inv_ntt.resize(i << 2).copy_n(i << 1, &e_k_inv).ntt();
            let mut e_d = ((self
                .clone_mod_xn(i << 1)
                .diff_x()
                .resize(i << 2)
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1))
                .resize(i << 2)
                .ntt()
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
                .resize(i << 2)
                .normalize()
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize();
            e_k = e_k.resize(i << 2);
            let e_k_upd = &mut e_k.coeff[i << 1..];
            for j in 0..i << 1 {
                e_k_upd[j] = e_d[j];
            }
            i <<= 1;
        }
        Some(e_k)
    }

    pub fn exp_and_inv(&self, n: usize) -> Option<(Self, Self)> {
        if self.coeff.get(0).copied().unwrap_or(0) % M as E != 0 {
            return None;
        } else if self.len() <= 1 {
            return Some((Self::new(vec![1]), Self::new(vec![1])));
        }
        let n = n.next_power_of_two();
        let mut e_k = Self::new(Vec::with_capacity(n)).push(1).push(self.coeff[1]);
        let mut e_k_inv = Self::new(Vec::with_capacity(n)).push(1);
        let mut e_k_ntt = Self::new(Vec::with_capacity(n)).resize(2);
        let mut e_k_inv_ntt = Self::new(Vec::with_capacity(n)).push(1).push(1);
        let mut i = 1;
        loop {
            e_k_ntt = e_k_ntt.copy(&e_k).resize(i << 2).ntt();
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
            e_k_inv_ntt = e_k_inv_ntt.resize(i << 2).copy_n(i << 1, &e_k_inv).ntt();
            let mut e_d = ((self
                .clone_mod_xn(i << 1)
                .diff_x()
                .resize(i << 2)
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1))
                .resize(i << 2)
                .ntt()
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
                .resize(i << 2)
                .normalize()
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize();
            e_k = e_k.resize(i << 2);
            let e_k_upd = &mut e_k.coeff[i << 1..];
            for j in 0..i << 1 {
                e_k_upd[j] = e_d[j];
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
        let mut g = vec![0; n];
        g[1] = 1;
        let mut p = vec![0; n];
        for i in 2..n.min(m) {
            p[i] = g[1] * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            g[i] = p[i] * big_omega_invs[i - 2] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += g[i] * self.coeff[j / i] % M as E * big_omega[j / i] % M as E;
            }
        }
        Some(Self::new(g))
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
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
        let (e0, e1) = (self.clone_mod_xn(n) * d).exp_and_inv(n)?;
        Some((e0 - e1) / (2 * d))
    }

    /// O(n log n)
    #[inline]
    pub fn asin(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
        (self.clone_mod_xn(n) * d).cosh(n)
    }

    /// O(n log n)
    #[inline]
    pub fn acos(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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
    pub fn tan(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
        let (e0, e1) = (self.clone_mod_xn(n) * d).exp_and_inv(n)?;
        Some((((e0 - e1) >> 1).inv(n)? * 2).normalize() * d)
    }

    /// O(n log n)
    #[inline]
    pub fn acsc_divx(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
        let (e0, e1) = (self.clone_mod_xn(n) * d).normalize().exp_and_inv(n)?;
        Some((e0 + e1).inv(n)? * 2)
    }

    /// O(n log n)
    #[inline]
    pub fn asec(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
        let p = (self.clone_mod_xn(n) * (2 * d)).normalize();
        let e = p.exp(n)?.normalize();
        Some((p.resize(e.len()).copy(&e) + 1) * ((e - 1) >> 1).inv(n)?.normalize() * d)
    }

    /// O(n log n)
    #[inline]
    pub fn acot_divx(&self, n: usize) -> Option<Self> {
        let d = mod_pow::<M>(find_primitive_root::<M>(), (M - 1) >> 2) as E;
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

    /// O(n log n)
    #[inline]
    pub fn mul_neg_self_even(&self, n: usize) -> Self {
        let (mut a0, mut a1) = self.bisect(n << 1);
        a0 = a0.square();
        a1 = a1.square();
        a1 = a1.mul_xn(1);
        let l = a0.len();
        a0.resize(l.max(a1.len())) - a1
    }

    /// O(n log n)
    #[inline]
    pub fn mul_even(&mut self, rhs: &Self, n: usize) -> Self {
        let (mut a0, mut a1) = self.bisect(n << 1);
        let (b0, b1) = rhs.bisect(n << 1);
        a0 *= b0;
        a1 *= b1;
        a1 = a1.mul_xn(1);
        let l = a0.len();
        a0.resize(l.max(a1.len())) + a1
    }

    /// O(n log n)
    #[inline]
    pub fn mul_odd(&mut self, rhs: &Self, n: usize) -> Self {
        let (mut a0, mut a1) = self.bisect(n << 1);
        let (b0, b1) = rhs.bisect(n << 1);
        a0 *= b1;
        a1 *= b0;
        let l = a0.len();
        a0.resize(l.max(a1.len())) + a1
    }

    /// O(n log n log k)
    #[inline]
    pub fn pow_bin(mut self, mut k: usize, n: usize) -> Self {
        let mut d = ((self.deg_or_0() << 1) + 1)
            .min((n << 1) + 1)
            .next_power_of_two();
        let mut ak = Self::from_elem(1, 1);
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
    }

    /// O(d k log (d k))
    #[inline]
    pub fn pow_all(mut self, mut k: usize) -> Self {
        let mut ak = Self::from_elem(1, 1);
        while k != 0 {
            if k & 1 != 0 {
                ak *= &self;
            }
            self = self.square();
            k >>= 1;
        }
        ak
    }

    /// O(k n log n)
    #[inline]
    pub fn pow_pow_two(mut self, k: usize) -> Self {
        for _ in 0..k {
            self = self.square();
        }
        self
    }

    /// O(n min(d, n))
    pub fn pow_dn(&self, k: usize, n: usize) -> Self {
        if n == 0 {
            return Self::from_elem(0, 1);
        }
        let mut q = Self::from_elem(0, n);
        let d = self.deg_or_0();
        q[0] = mod_pow_signed::<M>(self.coeff[0], k as u64);
        let mut k = k as E;
        if (M as E) >> 1 < k as E {
            k -= M as E;
        }
        let a0_inv = inverse_euclidean::<M, _>(self.coeff[0]);
        let invs = inverses_n_div::<M>(n + 1);
        for i in 1..n {
            for j in 1..=d.min(n).min(i) {
                q[i] += (self.coeff[j] % M as E * (q[i - j] % M as E)) % M as E
                    * (k * j as E % M as E - (i - j) as E)
                    % M as E;
            }
            q[i] %= M as E;
            q[i] *= invs[i] as E * a0_inv as E % M as E;
        }
        q
    }

    /// O(n log n)
    pub fn pow(self, k: usize, n: usize) -> Self {
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
        if k <= 1 << 10 && l >= 1 << 10 {
            self.pow_bin(k, n)
        } else if l <= 1 << 10 {
            self.pow_dn(k, n)
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

    /// O(n log n)
    pub fn dir_pow(&self, k: usize, n: usize) -> Self {
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let mut g = vec![0; n];
        let f1 = self.coeff[1];
        let f1_inv = inverse_euclidean::<M, _>(f1);
        g[1] = mod_pow_signed::<M>(f1, k as u64);
        let mut k = (k as E).rem_euclid(M as E);
        if (M as E) >> 1 < k {
            k -= M as E;
        }
        let mut p = vec![0; n];
        let v = k * g[1] % M as E;
        for i in 2..n.min(m) {
            p[i] = v * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            g[i] = p[i] * f1_inv % M as E * big_omega_invs[i - 2] % M as E;
            let v = g[i] * big_omega[i] % M as E;
            let w = k * g[i] % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * (big_omega[j / i] * w % M as E - v) % M as E;
            }
        }
        Self::new(g)
    }

    /// O(n log n)
    pub fn inv_pow(self, k: usize, n: usize) -> Option<Self> {
        let k = k % M as usize;
        let a0 = self.coeff.get(0).copied().unwrap_or(0);
        if a0 == 0 {
            return None;
        }
        let a0_inv = inverse_euclidean::<M, _>(a0);
        Some(
            (self * a0_inv).pow(M as usize - k, n).normalize()
                * mod_pow_signed::<M>(a0_inv, k as u64),
        )
    }

    /// a^b = e^{ln a * b}
    pub fn pow_poly(self, rhs: Self, n: usize) -> Option<Self> {
        (self.log(n)? * rhs).exp(n)
    }

    /// O(n log n)
    pub fn sqrt(&self, n: usize) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::from_elem(0, 0));
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
                    .pow(
                        inverse_euclidean::<M, _>(2_i64).rem_euclid(M as i64) as usize,
                        n,
                    )
                    .normalize()
                    * st,
            );
        }
        let half = inverse_euclidean::<M, _>(2);
        let st_inv = inverse_euclidean::<M, _>(st);
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::from_elem(st as E, 1),
            Self::from_elem(st_inv as E, 1),
            Self::from_elem(st as E, 1),
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
            if k << 1 >= n {
                break;
            }
            z = f.clone().ntt();
            let eps = gbuf
                .clone()
                .dot(&z)
                .intt()
                .erase_range(0..k)
                .normalize()
                .ntt()
                .dot(&gbuf)
                .intt();
            g = g.resize(k << 1);
            for i in k..k << 1 {
                g[i] = -eps[i] % M as E;
            }
            k <<= 1;
        }
        Some(f)
    }

    /// O(n log n)
    pub fn sqrt_and_inv(&self, n: usize) -> Option<(Self, Option<Self>)> {
        if self.is_zero() {
            return Some((Self::from_elem(0, 0), None));
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
        let half = inverse_euclidean::<M, _>(2);
        let st = mod_sqrt::<M>(self.coeff[0].rem_euclid(M as E) as u64)?;
        let st_inv = inverse_euclidean::<M, _>(st as E);
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::from_elem(st as E, 1),
            Self::from_elem(st_inv as E, 1),
            Self::from_elem(st as E, 1),
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
            let eps = gbuf
                .clone()
                .dot(&z)
                .intt()
                .erase_range(0..k)
                .normalize()
                .ntt()
                .dot(&gbuf)
                .intt();
            g = g.resize(k << 1);
            for i in k..k << 1 {
                g[i] = -eps[i] % M as E;
            }
            k <<= 1;
        }
        Some((f, Some(g)))
    }

    /// O(n log n)
    pub fn k_rt_pow(self, k: usize, i: usize, n: usize) -> Option<Self> {
        let j = self.trailing_xk_or_0();
        if j != 0 && j % k != 0 {
            return None;
        } else if j != 0 {
            let ans = self.clone().div_xn(j).k_rt_pow(k, i, n - j / k);
            return if let Some(mut ans) = ans {
                ans <<= j / k;
                Some(ans)
            } else {
                ans
            };
        }
        let a0 = self.coeff[0];
        let a0_k_rt_pow_i =
            mod_pow::<M>(mod_k_rt::<M>(a0.rem_euclid(M as i64) as u64, k)?, i as u64);
        Some(
            (self / a0)
                .pow(
                    (i as E * inverse_euclidean::<M, _>(k as E)).rem_euclid(M as E) as usize,
                    n,
                )
                .normalize()
                * a0_k_rt_pow_i as E,
        )
    }

    /// O(n log n)
    pub fn dir_k_rt(&self, k: usize, n: usize) -> Option<Self> {
        let m = self.coeff.len();
        let big_omega = sieve_complete::<E>(n, 0, |a, b| a + b, |_, _| 1).0;
        let big_omega_invs = inverses::<M, _>(&big_omega[2..]);
        let mut f = vec![0; n];
        let g1 = self.coeff[1];
        let g1_inv = inverse_euclidean::<M, _>(g1);
        let k_inv = inverse_euclidean::<M, _>(k as E);
        f[1] = mod_k_rt::<M>(g1.rem_euclid(M as E) as u64, k as usize)? as E;
        let mut p = vec![0; n];
        let v = k_inv as E * f[1] % M as E;
        for i in 2..n.min(m) {
            p[i] = v * self.coeff[i] % M as E * big_omega[i] % M as E;
        }
        for i in 2..n {
            f[i] = p[i] * g1_inv % M as E * big_omega_invs[i - 2] % M as E;
            let v = f[i] * big_omega[i] % M as E;
            let w = f[i] * k_inv as E % M as E;
            for j in (i << 1..n.min(i * m)).step_by(i) {
                p[j] += self.coeff[j / i] * (w * big_omega[j / i] % M as E - v) % M as E;
            }
        }
        Some(Self::new(f))
    }

    /// O(n log n)
    pub fn div_mod_ri(&self, q: &Self, qri: &Self) -> (Self, Self) {
        const MAGIC: i64 = 1 << 9;
        let q_d = q.deg_or_0();
        let d = self.deg_or_0() as i64 - q_d as i64;
        if d.min(q_d as i64) <= MAGIC {
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
            let q_rev = q.clone().reverse();
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
        let q_lead_inv = q.lead_inv();
        while r.deg_or_0() >= q.deg_or_0() {
            let coeff = (r.lead() * q_lead_inv).rem_euclid(M as E);
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
        (self, d) = self.truncate_and_deg_or_0();
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
        let mut ak = Self::from_elem(1, 1);
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
        let mut ak = Self::from_elem(1, 1);
        while k != 0 {
            if k & 1 != 0 {
                ak = (ak * &self).div_mod_ri(md, mdri).1.normalize();
            }
            self = self.square().div_mod_ri(md, mdri).1;
            k >>= 1;
        }
        ak
    }

    /// O(m log m log k)
    #[inline]
    pub fn pow_mod(self, k: usize, md: Self) -> Self {
        let d = md.deg_or_0();
        if md == Self::xn(d) {
            self.pow(k, d)
        } else if md == Self::xn(d) - 1 {
            self.pow_bin_mod_xnm1(k, d)
        } else {
            self.pow_mod_ri(k, &md, &md.clone().reverse_n(d + 1).inv(d + 1).unwrap())
        }
    }

    /// O(n log n)
    pub fn pows_cinv_xi(self, i: usize, n: usize) -> Self {
        let n = n.min(i);
        let a0_inv = inverse_euclidean::<M, _>(self.coeff[1]);
        let mut p = ((self >> 1) * a0_inv)
            .inv_pow(i, n)
            .unwrap()
            .reverse_k(i)
            .normalize()
            * mod_pow_signed::<M>(a0_inv, i as u64);
        let i_inv = inverse_euclidean::<M, _>(i as i64) as E;
        let l = p.len();
        for j in 0..l {
            p.coeff[j] %= M as E;
            p.coeff[j] *= j as E % M as E * i_inv % M as E;
        }
        p
    }

    /// O(n log n log i)
    #[inline]
    pub fn quot_xi(mut self, mut q: Self, mut i: usize) -> E {
        while i > 0 {
            q = q.n1pkmi(0);
            if i & 1 == 0 {
                self = self.mul_even(&q, i);
            } else {
                self = self.mul_odd(&q, i);
            }
            q = q.mul_neg_self_even(i);
            i >>= 1;
        }
        (self.coeff[0] * inverse_euclidean::<M, _>(q.coeff[0])) % M as E
    }

    #[inline]
    pub fn mulx_a(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let mut cur = 1;
        for i in 0..=d {
            self.coeff[i] = (self.coeff[i] * cur) % M as E;
            cur *= a;
            cur %= M as E;
        }
        self
    }

    #[inline]
    pub fn mulx_apic2(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let (mut cur, mut total) = (1, 1);
        for i in 0..=d {
            self.coeff[i] *= total;
            self.coeff[i] %= M as E;
            total *= cur;
            total %= M as E;
            cur *= a;
            cur %= M as E;
        }
        self
    }

    #[inline]
    pub fn mulx_apic2_ti(mut self, a: E, t: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
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

    #[inline]
    pub fn mulx_apip1c2(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let (mut cur, mut total) = (1, 1);
        for i in 0..=d {
            self.coeff[i] *= total;
            cur *= a;
            cur %= M as E;
            total *= cur;
            total %= M as E;
        }
        self
    }

    /// O(n log n)
    pub fn chirpz(mut self, z: E, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_and_deg();
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
            let mut z_inv = inverse_euclidean::<M, _>(z);
            if (z_inv - M as E).abs() < z_inv {
                z_inv = z_inv - M as E;
            }
            self.mulx_apic2(z_inv)
                .semicorr(Self::from_elem(1, k + d.unwrap_or(0)).mulx_apic2(z))
                .mod_xn(k)
                .mulx_apic2(z_inv)
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
            *l = inverse_euclidean::<M, _>(*l);
        }
        for i in (0..n - 1).rev() {
            p[i] = ((1 - zk[i + 1]) * p[i + 1]) % M as E;
        }
        Self::new(p)
    }

    /// O(n)
    /// ∏_{i < k} (1 + z^i t x) = ∑_{i=0}^k z^(i, 2) \[k,i\]_z t^i x^i mod x^n
    #[inline]
    pub fn prod_1pzitx(z: E, t: E, k: usize, n: usize) -> Self {
        Self::from_elem(1, n).kqci(k, z).mulx_apic2_ti(z, t)
    }

    /// O(n)
    /// ∏_{i < k} 1/(1 - z^i x) = ∑_{i=0}^k \[k+i-1,i\]_z mod x^n
    #[inline]
    pub fn prod_1o1mzix(z: E, k: usize, n: usize) -> Self {
        Self::from_elem(1, n).kpiqci(k - 1, z)
    }

    /// O(n)
    /// ∏_i (1 + z^i x) mod x^n = ∑_i z^(i,2)/(z;z)_i x^i
    #[inline]
    pub fn prod_inf_1pzix(z: E, n: usize) -> Self {
        Self::from_elem(1, n).mulx_apic2(z).q_poch_trans(z)
    }

    /// O(n)
    /// ∏_i 1/(1 - z^i x) = ∑_i x^i/(q; q)_i mod x^n
    #[inline]
    pub fn prod_inf_1o1mzix(z: E, n: usize) -> Self {
        Self::from_elem(1, n).q_poch_trans(z)
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
        let prods_neg = Self::pref_prod_1o1mzi(inverse_euclidean::<M, _>(z), k);
        let zk = inverse_euclidean::<M, _>(mod_pow_signed::<M>(z, k as u64 - 1));
        let mut zki = 1;
        for i in 0..k {
            y[i] *= ((zki * prods_neg[i]) % M as E * prods_pos[(k - 1) - i]) % M as E;
            y[i] %= M as E;
            zki = (zki * zk) % M as E;
        }
        let p_over_q = y.chirpz(z, k);
        let q = Self::prod_1pzitx(z, -1, k, k);
        (p_over_q * q).mod_xn(k).reverse_n(k)
    }

    /// O(n log^2 n)
    #[inline]
    pub fn build_eval_tree(
        tree: &mut [Self],
        pts: &mut impl FnMut(usize) -> E,
        v: usize,
        l: usize,
        r: usize,
    ) -> Self {
        if r - l == 1 {
            let res = Self::new(vec![-pts(l), 1]);
            tree[v] = res.clone();
            res
        } else {
            let m = l + (r - l >> 1);
            let res = Self::build_eval_tree(tree, pts, v << 1, l, m)
                * Self::build_eval_tree(tree, pts, v << 1 | 1, m, r);
            tree[v] = res.clone();
            res
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn eval_tree(&self, tree: &[Self], v: usize, l: usize, r: usize) -> Vec<E> {
        if r - l == 1 {
            vec![self.coeff[0]]
        } else {
            let m = l + (r - l >> 1);
            let mut a = (self % &tree[v << 1]).eval_tree(tree, v << 1, l, m);
            let b = (self % &tree[v << 1 | 1]).eval_tree(tree, v << 1 | 1, m, r);
            a.extend_from_slice(&b);
            a
        }
    }

    #[inline]
    fn to_newton_tree(&self, tree: &[Self], v: usize, l: usize, r: usize) -> Self {
        if r - l == 1 {
            self.clone()
        } else {
            let m = l + (r - l >> 1);
            let (c, d) = self.div_mod(&tree[v << 1]);
            let a = d.to_newton_tree(tree, v << 1, l, m);
            let b = c.to_newton_tree(tree, v << 1 | 1, m, r) << (m - l);
            a.resize_max(b.len()) + b
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn to_newton(mut self, mut p: impl FnMut(usize) -> E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg();
        if let Some(d) = d {
            let n = d + 1;
            let mut tree = vec![Self::new(vec![]); n.next_power_of_two() << 1];
            Self::build_eval_tree(&mut tree, &mut p, 1, 0, n);
            self.to_newton_tree(&tree, 1, 0, n)
        } else {
            Self::new(vec![])
        }
    }

    /// O(n log^2 n)
    pub fn to_fall(self) -> Self {
        self.to_newton(|i| i as E)
    }

    /// O(n log^2 n)
    pub fn to_binom(self) -> Self {
        self.to_newton(|i| i as E).inv_borel()
    }

    /// O(n log^2 n)
    #[inline]
    pub fn evals(&self, n: usize, mut x: impl FnMut(usize) -> E) -> Self {
        if self.is_zero() {
            return Self::from_elem(0, n);
        }
        let mut tree = vec![Self::new(vec![]); n.next_power_of_two() << 1];
        Self::build_eval_tree(&mut tree, &mut x, 1, 0, n);
        Self::new(self.eval_tree(&tree, 1, 0, n))
    }

    /// O(M log M)
    #[inline]
    pub fn evals_z_mz(self) -> Self {
        self.chirpz(find_primitive_root::<M>() as i64, M as usize)
    }

    /// O(n log^2 n)
    pub fn interp_tree(&self, tree: &[Self], y: &[E], v: usize, l: usize, r: usize) -> Self {
        if r - l == 1 {
            Self::new(vec![
                (y[l] * inverse_euclidean::<M, _>(self.coeff[0])) % M as E,
            ])
        } else {
            let m = l + (r - l >> 1);
            let mut a = (self % &tree[v << 1]).interp_tree(tree, y, v << 1, l, m);
            let mut b = (self % &tree[v << 1 | 1]).interp_tree(tree, y, v << 1 | 1, m, r);
            a *= &tree[v << 1 | 1];
            b *= &tree[v << 1];
            a += &b;
            a
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn interp(n: usize, mut x: impl FnMut(usize) -> E, y: &[E]) -> Self {
        let mut tree = vec![Self::new(vec![]); n.next_power_of_two() << 1];
        Self::build_eval_tree(&mut tree, &mut x, 1, 0, n)
            .diff()
            .interp_tree(&tree, &y, 1, 0, y.len())
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
    pub fn xn(n: usize) -> Self {
        Self::new(vec![0; n]).push(1)
    }

    #[inline]
    pub fn txnpz(t: E, z: E, n: usize) -> Self {
        let mut s = Self::new(vec![0; n]).push(t);
        s[0] = z;
        s
    }

    /// O(n)
    pub fn fact2(mut self) -> Self {
        let n = self.coeff.len();
        let mut a = 1;
        let mut b = 1;
        for i in (1..n - 1).step_by(2) {
            a = (a * i as u64) % M;
            b = (b * (i as u64 + 1)) % M;
            self.coeff[i] *= a as E;
            self.coeff[i + 1] *= b as E;
        }
        if n & 1 == 0 {
            a = (a * (n - 1) as u64) % M;
            self.coeff[n - 1] *= a as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn exp_xkoa(k: u64, a: E, n: usize) -> Self {
        if n as u64 <= k {
            return Self::new(vec![1]);
        }
        let mut p = vec![0; n];
        p[0] = 1;
        let mut b = inverse_euclidean::<M, _>(
            mod_pow_signed::<M>(a, (n - 1) as u64 / k) * mod_fact::<M>((n - 1) as u64 / k) as E,
        );
        for i in (1..=(n - 1) / k as usize).rev() {
            p[i * k as usize] = b as E;
            b = (b * (i as E)) % M as E * a % M as E;
        }
        Self::new(p)
    }

    /// O(n k)
    #[inline]
    pub fn exp_k_rt_x_oa(k: u64, a: E, n: usize) -> Self {
        let mut p = vec![0; n];
        p[0] = 1;
        let mut b = inverse_euclidean::<M, _>(
            mod_pow_signed::<M>(a, (n - 1) as u64 * k) * mod_fact::<M>((n - 1) as u64 * k) as E,
        );
        for i in (1..=(n - 1) * k as usize).rev() {
            p[i / k as usize] = b as E;
            b = (b * (i as E)) % M as E * a % M as E;
        }
        Self::new(p)
    }

    /// O(n)
    #[inline]
    pub fn cosh_xkoa(k: u64, a: E, n: usize) -> Self {
        if n as u64 <= k {
            return Self::new(vec![1]);
        }
        let mut p = vec![0; n];
        p[0] = 1;
        let mut b = inverse_euclidean::<M, _>(
            mod_pow_signed::<M>(a, (n - 1) as u64 / k) * mod_fact::<M>((n - 1) as u64 / k) as E,
        );
        for i in (1..=(n - 1) / k as usize).rev() {
            if i & 1 == 0 {
                p[i * k as usize] = b as E;
            }
            b = (b * (i as E)) % M as E * a % M as E;
        }
        Self::new(p)
    }

    /// O(n)
    #[inline]
    pub fn sinh_xkoa(k: u64, a: E, n: usize) -> Self {
        if n as u64 <= k {
            return Self::new(vec![]);
        }
        let mut p = vec![0; n];
        let mut b = inverse_euclidean::<M, _>(
            mod_pow_signed::<M>(a, (n - 1) as u64 / k) * mod_fact::<M>((n - 1) as u64 / k) as E,
        );
        for i in (1..=(n - 1) / k as usize).rev() {
            if i & 1 != 0 {
                p[i * k as usize] = b as E;
            }
            b = (b * (i as E)) % M as E * a % M as E;
        }
        Self::new(p)
    }

    /// O(n)
    #[inline]
    pub fn kn_matchings(n: usize) -> Self {
        Poly::<M>::exp_xkoa(2, 2, n).inv_borel().pos_normalize()
    }

    /// O(n)
    #[inline]
    pub fn exp_x(n: usize) -> Self {
        Self::new(vec![1; n]).borel()
    }

    /// O(n)
    pub fn telephone(mut self) -> Self {
        let n = self.coeff.len();
        let mut a = 1;
        let mut b = 1;
        for i in 2..n {
            (a, b) = (b, (b + (i as u64 - 1) * a) % M);
            self.coeff[i] *= b as E;
        }
        self
    }

    /// O(n log n)
    pub fn necklaces(mut self, k: u64) -> Self {
        let n = self.coeff.len();
        let invs = inverses_n_div::<M>(n);
        let totient = sieve::j_k(1, n).0;
        let mut f = vec![0; n];
        for i in 1..n {
            let mut kjoi = k;
            for j in (i..n).step_by(i) {
                f[j] = (f[j] + totient[i] as u64 * kjoi) % M;
                kjoi = (kjoi * k) % M;
            }
        }
        for i in 0..n {
            self.coeff[i] *= (invs[i] * f[i] % M) as E;
        }
        self
    }

    /// O(n log n)
    pub fn necklaces_aperiodic(mut self, k: u64) -> Self {
        let n = self.coeff.len();
        let invs = inverses_n_div::<M>(n);
        let mobius = sieve::mobius(n).0;
        let mut f = vec![0; n];
        for i in 1..n {
            let mi = mobius[i];
            if mi == 0 {
                continue;
            } else if mi == 1 {
                let mut kjoi = k;
                for j in (i..n).step_by(i) {
                    f[j] += kjoi;
                    kjoi = (kjoi * k) % M;
                }
            } else if mi == -1 {
                let mut kjoi = k;
                for j in (i..n).step_by(i) {
                    f[j] -= kjoi;
                    kjoi = (kjoi * k) % M;
                }
            }
        }
        for i in 0..n {
            self.coeff[i] *= (invs[i] * f[i] % M) as E;
        }
        self
    }

    /// O(n log n)
    pub fn s_i_kth_unity(k: usize, n: usize) -> Self {
        let mut p = vec![0; n];
        let invs = inverses_n_div::<M>(n);
        if n <= k {
            for i in (1..=n).filter(|&i| k.is_multiple_of(i)) {
                p[i] = invs[i] as i64;
            }
        } else {
            for i in prime::divisors(k).0 {
                p[i] = invs[i] as i64;
            }
        }
        Self::new(p).exp(n).unwrap()
    }

    // sum_{d | k} μ(k/d) exp(sum_{m | d} z^m/m)
    // = sum_{d | k} μ(k/d) |Hom(Z_k, S_n)| z^n/n!

    /// O(k^1/4 + d(k) n log n) = O(k^1/4 + exp(O(log k / log log k)) n log n) = O(n^{1 + log 2 / log log n} log n)
    pub fn s_i_order_k(k: usize, n: usize) -> Self {
        let mut p = Self::from_elem(0, n);
        let mobius = sieve::mobius(k + 1).0;
        for d in prime::divisors(k).0 {
            p += Self::s_i_kth_unity(d, n) * mobius[k / d] as i64;
        }
        p
    }

    /// O(n log n)
    pub fn s_i_odd_cyc(n: usize) -> Self {
        (Self::new(vec![1, 1]) * Self::new(vec![1, -1]).inv(n).unwrap())
            .sqrt(n)
            .unwrap()
    }

    /// O(n^2 log n)
    pub fn s_i_square(n: usize) -> Self {
        let mut p = Self::s_i_odd_cyc(n).normalize();
        for i in 1..n >> 2 {
            p = (p * Self::cosh_xkoa((i as u64) << 1, (i as E) << 1, n))
                .mod_xn(n.next_power_of_two());
        }
        p
    }

    /// O(n)
    #[inline]
    pub fn exp_ax(a: E, n: usize) -> Self {
        let a = a % M as E;
        let mut coeff = Vec::with_capacity(n);
        coeff.push(1);
        let mut an = a;
        for _ in 1..n {
            coeff.push(an);
            an *= a;
            an %= M as E;
        }
        Self::new(coeff).borel()
    }

    /// O(n log n)
    pub fn z_cn(&self, n: usize) -> Self {
        let totient = sieve::j_k(1, n).0;
        let mut f = vec![0; n];
        for i in 1..n.min(self.coeff.len()) {
            let a = self.coeff[i] % M as E;
            let mut ai_joi = a;
            for j in (i..n).step_by(i) {
                f[j] = (f[j] + totient[i] as E * ai_joi) % M as E;
                ai_joi = (ai_joi * a) % M as E;
            }
        }
        Self::new(f).integr_divx().resize(n)
    }

    /// O(n log n)
    pub fn z_dn(&self, n: usize) -> Self {
        let mut s = self.z_cn(n) / 2;
        let fourth = inverse_euclidean::<M, _>(4);
        let half = (2 * fourth) % M as E;
        for i in (2..n).step_by(2) {
            s[i] += (self.coeff[1] * self.coeff[1] % M as E
                * mod_pow::<M>(self.coeff[2].rem_euclid(M as E) as u64, (i as u64 - 2) >> 1) as E
                % M as E
                + mod_pow::<M>(self.coeff[2].rem_euclid(M as E) as u64, i as u64 >> 1) as E)
                * fourth
                % M as E;
        }
        for i in (1..n).step_by(2) {
            s[i] += self.coeff[1]
                * mod_pow::<M>(self.coeff[2].rem_euclid(M as E) as u64, (n as u64 - 1) >> 1) as E
                % M as E
                * half
                % M as E;
        }
        s
    }

    /// O(n log n)
    #[inline]
    pub fn z_sn(self, n: usize) -> Self {
        self.mod_xn(n).integr_divx().exp(n).unwrap()
    }

    /// O(n)
    #[inline]
    pub fn fall_fact_k(self, k: usize) -> Self {
        self.ick(k) * mod_fact::<M>(k as u64) as E
    }

    /// O(n)
    #[inline]
    pub fn fall_fact_a(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let mut b = 1;
        for i in 0..=d {
            self.coeff[i] *= b;
            b *= a - i as E;
            b %= M as E;
        }
        self
    }

    /// O(n + k)
    #[inline]
    pub fn rise_fact_k(self, k: usize) -> Self {
        self.ipzck(k as isize - 1, k) * mod_fact::<M>(k as u64) as E
    }

    /// O(n)
    #[inline]
    pub fn rise_fact_a(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let mut b = 1;
        for i in 0..=d {
            self.coeff[i] *= b;
            b *= a + i as E;
            b %= M as E;
        }
        self
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
        (self, d) = self.truncate_and_deg_or_0();
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

    /// O(n + z)
    #[inline]
    pub fn kcipz(self, k: usize, z: isize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kci(k) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kci(k) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn kpici(mut self, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
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

    /// O(n + z)
    #[inline]
    pub fn kpipzcipz(self, z: isize, k: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kpici(k) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kpici(k) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn ick(mut self, k: usize) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
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

    /// O(n + z)
    #[inline]
    pub fn ipzck(self, z: isize, k: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).ick(k) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).ick(k) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn i2ci(mut self) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
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

    /// O(n + z)
    #[inline]
    pub fn i2pzcipz(self, z: isize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).i2ci() >> z
        } else {
            let z = (-z) as usize;
            (self >> z).i2ci() << z
        }
    }

    /// O(n)
    #[inline]
    pub fn i2qci(mut self, q: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
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

    /// O(n)
    #[inline]
    pub fn i2pzqcipz(self, z: isize, q: E) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).i2qci(q) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).i2qci(q) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn sum_pows(mut self, p: usize, n: usize) -> Self {
        let mut pws = sieve_complete(
            n,
            1,
            |a, b| a * b % M,
            |q, _| mod_pow::<M>(q as u64, p as u64),
        )
        .0;
        pws[0] = if p == 0 { 1 } else { 0 };
        let mut ppw = 0;
        for i in 0..n {
            ppw += pws[i];
            ppw %= M;
            self.coeff[i] *= ppw as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(p log p)
    #[inline]
    pub fn faulhaber_kp(k: u64, p: usize) -> E {
        let mut a = 0;
        let b = Self::bernoulli_plus(p + 1).inv_borel().kci(p + 1);
        let mut kp1mr = k;
        for i in (0..=p).rev() {
            a += b[i] * kp1mr as E;
            a %= M as E;
            kp1mr = (kp1mr * k) % M;
        }
        a / (p as E + 1)
    }

    /// O(p log p)
    #[inline]
    pub fn faulhaber_xp(p: usize) -> Self {
        let b = Self::bernoulli_plus(p + 1)
            .inv_borel()
            .kci(p + 1)
            .reverse_k(p + 1);
        let mut s = b / (p as E + 1);
        s[0] = 0;
        s
    }

    /// O(n log n)
    #[inline]
    pub fn pref_x(mut self) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let b = Self::bernoulli_plus(d + 1).reverse_k(d);
        let p0 = self.coeff[0] % M as E;
        let mut s = ((self.inv_borel() * b) >> d - 1).borel().mod_xn(d + 2);
        s[0] = p0;
        s
    }

    /// O(n)
    #[inline]
    pub fn linp(mut self, p: usize, n: usize) -> Self {
        let mut pws = sieve_complete(
            n,
            1,
            |a, b| a * b % M,
            |q, _| mod_pow::<M>(q as u64, p as u64),
        )
        .0;
        pws[0] = if p == 0 { 1 } else { 0 };
        self.coeff
            .iter_mut()
            .zip(pws)
            .for_each(|(i, j)| *i *= j as E);
        self
    }

    /// O(n)
    #[inline]
    pub fn pref(mut self, n: usize) -> Self {
        let mut p = 0;
        for i in 0..n {
            p += self.coeff[i];
            p %= M as E;
            self.coeff[i] = p;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn sum_pows_k(k: usize, n: usize) -> Self {
        let mut e = Self::exp_x(n + 1);
        e = ((-e.clone() + 1) >> 1).inv(n).unwrap().normalize()
            * ((e - Self::exp_ax(k as E + 1, n + 1)) >> 1).normalize();
        if e.is_zero() {
            e.coeff.push(0);
        }
        e
    }

    /// O(n^1/2)
    /// + O(n) for initialization
    #[inline]
    pub fn pent(n: usize) -> Self {
        let mut p = vec![0; n];
        p[0] = 1;
        let mut i = 1;
        let mut p0 = 1;
        let mut p1 = 2;
        let mut sign = 1;
        while p0 < n {
            sign = -sign;
            p[p0] = sign;
            p0 += 3 * i + 1;
            if p1 > n {
                continue;
            }
            p[p1] = sign;
            p1 += 3 * i + 2;
            i += 1;
        }
        Self::new(p)
    }

    /// O(n^1/2 F)
    #[inline]
    pub fn pent_fn(n: usize, mut f: impl FnMut(usize, i8)) {
        f(0, 1);
        let mut i = 1;
        let mut p0 = 1;
        let mut p1 = 2;
        let mut sign = 1;
        while p0 < n {
            sign = -sign;
            f(p0, sign);
            p0 += 3 * i + 1;
            if p1 > n {
                continue;
            }
            f(p1, sign);
            p1 += 3 * i + 2;
            i += 1;
        }
    }

    /// O(n^3/2)
    #[inline]
    pub fn partition_pent(n: usize) -> Self {
        let mut p = vec![0; n];
        p[0] = 1;
        for i in 1..n {
            let mut acc = 0;
            for k in 1.. {
                let pent1 = k * (3 * k - 1) >> 1;
                if pent1 > i {
                    break;
                }
                let sign = if k & 1 == 1 { 1 } else { -1 };
                acc += &p[i - pent1] * sign;
                let pent2 = k * (3 * k + 1) >> 1;
                if pent2 > i {
                    continue;
                }
                acc += &p[i - pent2] * sign;
                acc %= M as E;
            }
            p[i] = acc;
        }
        Self::new(p)
    }

    /// O(n log n)
    #[inline]
    pub fn log_q_fact(k: usize, n: usize) -> Self {
        let n = (n.min((k * (k - 1) >> 1) + 1)).next_power_of_two();
        let mut p = vec![0; n];
        for d in 1..=k.min(n - 1) {
            for j in (d..n).step_by(d) {
                p[j] += d as E;
            }
        }
        p.iter_mut()
            .zip(inverses_n_div::<M>(n))
            .for_each(|(v, j)| *v = ((k as E - *v) * j as E) % M as E);
        Self::new(p)
    }

    /// O(n log n)
    /// assumes a is sorted
    #[inline]
    pub fn log_q_multinom(a: &[usize], n: usize) -> Self {
        let k = a.iter().sum::<usize>();
        let mut d = k * (k - 1) >> 1;
        for &k in a {
            d -= k * (k - 1) >> 1;
        }
        let n = (n.min(d + 1)).next_power_of_two();
        let mut p = vec![0; n];
        let mut s = a.len() as E - 1;
        let mut l = 1;
        for i in 0..a.len() - 1 {
            if s != 0 {
                for d in l..=a[i] {
                    for j in (d..n).step_by(d) {
                        p[j] += s * d as E;
                    }
                }
            }
            l = a[i] + 1;
            s -= 1;
            if l > n {
                break;
            }
        }
        for d in a[a.len() - 1] + 1..=k {
            for j in (d..n).step_by(d) {
                p[j] -= d as E;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(n log n)
    #[inline]
    pub fn log_q_binom(k: usize, i: usize, n: usize) -> Self {
        let n = (n.min(i * (k - i) + 1)).next_power_of_two();
        let mut p = vec![0; n];
        let (alpha, beta) = if i << 1 < k { (i, k - i) } else { (k - i, i) };
        for d in 1..=alpha.min(n - 1) {
            for j in (d..n).step_by(d) {
                p[j] += d as E;
            }
        }
        for d in beta + 1..=k.min(n - 1) {
            for j in (d..n).step_by(d) {
                p[j] -= d as E;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(n log n)
    #[inline]
    pub fn partition(n: usize) -> Self {
        Self::pent(n).inv(n).unwrap()
    }

    /// O(n log n + |k|)
    /// log ∏_{i ∈ k} (1 + x^i t)
    #[inline]
    pub fn log_prod_1pxit(k: impl Iterator<Item = usize>, t: E, n: usize) -> Self {
        let n = n.next_power_of_two();
        let mut p = vec![0; n];
        for i in k.filter(|&j| j < n) {
            let mut x = t;
            for j in (i..n).step_by(i) {
                p[j] += x * i as E;
                x = (-t * x) % M as E;
            }
        }
        Self::new(p).integr_divx()
    }

    /// O(√n)
    /// + O(n) for initialization
    pub fn squares(n: usize) -> Self {
        let mut s = Self::from_elem(0, n);
        s.coeff[0] = 1;
        let r = n.isqrt();
        for i in 1..if r * r == n { r } else { r + 1 } {
            s.coeff[i * i] += 2;
        }
        s
    }

    /// O(n log n)
    /// ((∑_i x^{i^2})^k = ∏_i (1 - x^{2i})^k (1 + x^{2m-1})^{2k})
    pub fn log_squares_k(k: usize, n: usize) -> Self {
        if k <= 5 {
            return Self::squares(n).pow(k, n);
        }
        let n = n.next_power_of_two();
        let mut p = vec![0; n];
        for i in (1..n).step_by(2) {
            let v = ((k << 1) * i) as E;
            let mut sign = 1;
            for j in (i..n).step_by(i) {
                sign = -sign;
                p[j] -= v * sign;
            }
        }
        for i in (2..n).step_by(2) {
            let v = (k * i) as E;
            for j in (i..n).step_by(i) {
                p[j] -= v;
            }
        }
        p.iter_mut().zip(inverses_n_div::<M>(n)).for_each(|(i, j)| {
            *i *= j as E;
            *i %= M as E
        });
        Self::new(p)
    }

    /// O(n log n log k)
    pub fn sum_i_r_mod_n_kci(r: usize, n: usize, k: usize) -> u64 {
        Self::new(vec![1, 1])
            .pow_bin_mod_xnm1(k, n)
            .shl_mod_xnm1(n - r, n)
            .coeff[0]
            .rem_euclid(M as i64) as u64
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

    /// O(n + max(z,0))
    #[inline]
    pub fn kqcipz(self, k: usize, z: isize, q: E) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kpiqci(k, q) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kpiqci(k, q) << z
        }
    }

    /// O(n + max(z,0))
    #[inline]
    pub fn kpipzqcipz(self, k: usize, z: isize, q: E) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kpiqci(k, q) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kpiqci(k, q) << z
        }
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

    /// O(n + max(z,0))
    #[inline]
    pub fn ipzqck(self, k: usize, z: isize, q: E) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).iqck(k, q) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).iqck(k, q) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn q_diff_x(mut self, q: E) -> Self {
        self.coeff[0] = 0;
        let mut qi = (q * q) % M as E;
        let qmii = inverse_euclidean::<M, _>(q - 1);
        for i in 2..self.len() {
            self.coeff[i] *= ((qi - 1) * qmii) % M as E;
            self.coeff[i] %= M as E;
            qi = (qi * q) % M as E;
        }
        self
    }

    #[inline]
    pub fn q_diff(self, q: E) -> Self {
        self.q_diff_x(q) >> 1
    }

    /// O(n)
    #[inline]
    pub fn q_diff_k(self, k: usize, q: E) -> Self {
        (self.inv_q_borel(q) >> k).q_borel(q)
    }

    /// O(n)
    #[inline]
    pub fn q_integr_divx(mut self, q: E) -> Self {
        let n = self.coeff.len();
        self.coeff[0] = 0;
        let mut qi = (q * q) % M as E;
        let qmii = inverse_euclidean::<M, _>(q - 1);
        let mut a = Vec::with_capacity(n);
        for _ in 2..n {
            a.push(((qi - 1) * qmii) % M as E);
            qi = (qi * q) % M as E;
        }
        a = inverses::<M, _>(&a);
        let mut i = 0;
        for j in 2..n {
            self.coeff[j] *= a[i] as E;
            self.coeff[j] %= M as E;
            i += 1;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn q_integr(self, q: E) -> Self {
        (self << 1).q_integr_divx(q)
    }

    /// O(n)
    #[inline]
    pub fn q_integr_k(self, k: usize, q: E) -> Self {
        (self.inv_q_borel(q) << k).q_borel(q)
    }

    /// O(n)
    #[inline]
    pub fn inv_q_borel(mut self, q: E) -> Self {
        self = self.truncate_deg();
        let mut q_fact = 1;
        let mut qi = (q * q) % M as E;
        let qmii = inverse_euclidean::<M, _>(q - 1);
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
        self = self.truncate_deg();
        let mut qi = (q * q) % M as E;
        let qmii = inverse_euclidean::<M, _>(q - 1);
        let mut q_fact = 1;
        for _ in 2..self.len() {
            q_fact *= (qi - 1) * qmii % M as E;
            q_fact %= M as E;
            qi = (qi * q) % M as E;
        }
        q_fact = inverse_euclidean::<M, _>(q_fact);
        let q_inv = inverse_euclidean::<M, _>(q);
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
    pub fn inv_q_poch_trans(mut self, q: E) -> Self {
        self = self.truncate_deg();
        let q = q.rem_euclid(M as E) as u64;
        let mut q_poch = 1;
        let mut qi = q;
        self.coeff.iter_mut().skip(1).for_each(|v| {
            q_poch *= (1 - qi as E) % M as E;
            q_poch %= M as E;
            *v *= q_poch as E;
            *v %= M as E;
            qi = (qi * q) % M;
        });
        self
    }

    /// O(n)
    #[inline]
    pub fn q_poch_trans(mut self, q: E) -> Self {
        self = self.truncate_deg();
        let mut q_poch = 1;
        let mut qi = q;
        for _ in 1..self.len() {
            q_poch *= (1 - qi as E) % M as E;
            q_poch %= M as E;
            qi = (qi * q) % M as E;
        }
        q_poch = inverse_euclidean::<M, _>(q_poch);
        let q_inv = inverse_euclidean::<M, _>(q);
        self.coeff.iter_mut().skip(1).rev().for_each(|v| {
            qi = (qi * q_inv) % M as E;
            *v *= q_poch;
            *v %= M as E;
            q_poch *= (1 - qi as E) % M as E;
            q_poch %= M as E;
        });
        self
    }

    /// O(n log n)
    pub fn mat_rank_i_fq(k: u64, n: usize, q: u64) -> Self {
        (Self::from_elem(1, n)
            .mulx_a(mod_pow::<M>(q, k) as E)
            .q_borel(q as E)
            * Self::from_elem(1, n)
                .n1pkmi(0)
                .mulx_apic2(q as E)
                .q_borel(q as E))
        .mod_xn(n)
        .inv_q_borel(q as E)
        .kqci(k as usize, q as E)
    }

    /// O(n)
    pub fn gl_i_fq(self, q: E) -> Self {
        self.mulx_apic2_ti(q, q - 1).inv_q_borel(q)
    }

    /// O(n)
    pub fn sl_i_fq(self, q: E) -> Self {
        let mut s = self.gl_i_fq(q) / (q - 1);
        s[0] = 1;
        s
    }

    /// O(n)
    pub fn pgl_i_fq(self, q: E) -> Self {
        self.sl_i_fq(q)
    }

    /// O(n)
    pub fn psl_i_fq(self, q: E) -> Self {
        let mut s = self.gl_i_fq(q);
        let qm1_inv = inverse_euclidean::<M, _>(q - 1);
        let n = s.len();
        let k = q.rem_euclid(M as E) as usize - 1;
        let fs = prime::factor_mult(k);
        s.coeff
            .iter_mut()
            .zip(
                sieve::sieve(
                    n,
                    1,
                    |a, b| a * b,
                    |p, k, _| {
                        if let Ok(i) = fs.binary_search_by_key(&p, |&(p, _)| p) {
                            mod_pow::<M>(p as u64, M - 1 - k.min(fs[i].1) as u64) as E
                        } else {
                            1
                        }
                    },
                )
                .0,
            )
            .for_each(|(i, j)| *i = *i * qm1_inv % M as E * j % M as E);
        s.coeff[0] = 1;
        s
    }

    /// O(n log n)
    pub fn cyclotomic(n: usize) -> Self {
        if n == 0 {
            return Self::new(vec![]);
        } else if n == 1 {
            return Self::new(vec![-1, 1]);
        } else if n > 2 && n & 1 == 0 && ((n >> 1) & 1 != 0) {
            let p = Self::cyclotomic(n >> 1);
            return p.n1pkmi(0);
        }
        let d = special::totient(n as u64) as usize;
        if d == n - 1 {
            return Self::new(vec![1; n]);
        }
        let (divs, ps) = prime::divisors(n);
        if ps.len() == 1 {
            let (p, i) = ps[0];
            return if i == 1 {
                Self::from_elem(1, n)
            } else {
                Self::from_elem(1, p).sub_xk_n(p.pow(i - 1), d + 1)
            };
        } else if ps.len() == 2 && ps[0].0 == 2 {
            let (_, i) = ps[0];
            let (p, j) = ps[1];
            return Self::from_elem(1, d + 1)
                .n1pkmi(0)
                .sub_xk_n(2_usize.pow(i - 1) * p.pow(j - 1), d + 1);
        }
        let rad = ps.iter().fold(1, |acc, (p, _)| acc * p);
        if rad != n {
            return Self::cyclotomic(rad).sub_xk(n / rad);
        }
        let mut p = Self::new(vec![0; d + 1]);
        let mut q = Self::new(vec![0; d + 1]);
        (p[0], q[0]) = (1, 1);
        let mobius = sieve::mobius(n + 1).0;
        for i in divs {
            if mobius[n / i] == 1 {
                for j in (i..d + 1).rev() {
                    p[j] -= p[j - i];
                }
            } else if mobius[n / i] == -1 {
                for j in (i..d + 1).rev() {
                    q[j] -= q[j - i];
                }
            }
        }
        p = (p * q.inv(d + 1).unwrap()).mod_xn(d + 1).neg_normalize();
        if p.coeff[0] == -1 { -p } else { p }
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

    /// O(n)
    #[inline]
    pub fn log_1o1px(n: usize) -> Self {
        Self::log_1o1mx(n).n1pkmi(0)
    }

    /// O(n)
    #[inline]
    pub fn log_1mx(n: usize) -> Self {
        -Self::log_1o1mx(n)
    }

    /// O(n)
    #[inline]
    pub fn log_1px(n: usize) -> Self {
        Self::log_1o1mx(n).n1pkmi(1)
    }

    /// O(n log n)
    #[inline]
    pub fn bernoulli(n: usize) -> Self {
        (Self::exp_x(n + 1) >> 1).inv(n).unwrap()
    }

    /// O(n log n)
    #[inline]
    pub fn bernoulli_plus(n: usize) -> Self {
        let mut s = Self::bernoulli(n);
        s[1] = -s[1];
        s
    }

    /// O(n)
    #[inline]
    pub fn fibonacci(mut self, n: usize) -> Self {
        let mut coeff = Vec::with_capacity(n);
        coeff.push(0);
        coeff.push(1);
        let mut f0 = 0;
        let mut f1 = 1;
        self.coeff[0] = 0;
        for i in 2..n {
            (f0, f1) = (f1, f0 + f1 % M);
            self.coeff[i] *= f1 as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn lucas(mut self, n: usize) -> Self {
        let mut coeff = Vec::with_capacity(n);
        coeff.push(2);
        coeff.push(-1);
        let mut f0 = 2;
        let mut f1 = 1;
        self.coeff[0] *= 2;
        for i in 2..n {
            (f0, f1) = (f1, f0 + f1 % M as E);
            self.coeff[i] *= f1;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn euler(n: usize) -> Self {
        (Self::exp_x(n) + Self::exp_ax(-1, n)).inv(n).unwrap() * 2
    }

    /// O(n log n)
    #[inline]
    pub fn euler_x2(n: usize) -> Self {
        (Self::exp_k_rt_x_oa(2, 1, n) + Self::exp_k_rt_x_oa(2, 1, n))
            .inv(n)
            .unwrap()
            * 2
    }

    /// O(n)
    #[inline]
    pub fn catalan(mut self, n: usize) -> Self {
        let mut a = 1;
        let invs = inverses_n_div::<M>(n + 1);
        for i in 1..n {
            a *= ((((i as u64) << 1) - 1) << 1) * invs[i] % M;
            a %= M;
            self.coeff[i] *= (a * invs[i + 1]) as E;
            self.coeff[i] %= M as E;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn catalan_poly(self, n: usize) -> Option<Self> {
        Some(((self * -4 + 1).sqrt(n)? + 1).inv(n)? * 2)
    }

    /// O(n log n)
    #[inline]
    pub fn bell(n: usize) -> Self {
        (Self::exp_x(n) - 1).exp(n).unwrap()
    }

    /// O(n)
    #[inline]
    pub fn derangements(mut self, n: usize) -> Self {
        let mut a = 1;
        for i in 1..n {
            a *= i as E;
            a += if i & 1 == 0 { 1 } else { -1 };
            self.coeff[i] *= a;
            self.coeff[i] %= M as E;
        }
        self
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

    // [n,k] = (n-1)! 1/(k-1)! [z^{n-k}] (z/(1-e^-z))^n
    /// O(n log n)
    #[inline]
    pub fn stirling1_new(n: usize) -> Self {
        let p = ((Self::bernoulli(n).pow(n, n + 1).reverse_k(n) >> 1).borel())
            * mod_fact::<M>(n as u64 - 1) as E;
        p
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_unsigned(n: usize) -> Self {
        Self::stirling1(n).n1pkmi(0)
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_k(k: usize, n: usize) -> Self {
        Self::log_1px(n).pow(k, n) * mod_rfact::<M>(k as u64) as E
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

    /// O(n log^2 n)
    pub fn elem_symm_linear(self) -> Self {
        self.prod_linear().reverse().n1pkmi(0)
    }

    /// O(n log n)
    pub fn elem_symm_arithmetic(a: E, b: E, n: usize) -> Self {
        Self::prod_arithmetic(a, b, n).reverse().n1pkmi(0)
    }

    /// O(n)
    pub fn elem_symm_geometric(a: E, b: E, n: usize) -> Self {
        Self::prod_geometric(a, b, n).reverse().n1pkmi(0)
    }

    /// O(n log n)
    pub fn elem_symm_to_pow_sum(self) -> Self {
        let n = self.len();
        (self.inv(n).unwrap() * self.diff_x()).mod_xn(n).n1pkmi(1)
    }

    /// O(n log n)
    pub fn pow_sum_to_elem_symm(self) -> Self {
        let n = self.len();
        self.n1pkmi(1)
            .integr_divx()
            .normalize()
            .exp(n)
            .unwrap()
            .mod_xn(n)
    }

    /// O(n log n)
    pub fn pow_sum_to_complete_homo(self) -> Self {
        let n = self.len();
        self.integr_divx().normalize().exp(n).unwrap().mod_xn(n)
    }

    /// O(n log n)
    pub fn complete_homo_to_pow_sum(self) -> Self {
        let n = self.len();
        (self.inv(n).unwrap() * self.diff_x()).mod_xn(n)
    }

    /// O(n log n)
    #[inline]
    pub fn corr(self, rhs: Self) -> Self {
        self.reverse() * rhs
    }

    /// O(n log n)
    #[inline]
    pub fn semicorr(mut self, rhs: Self) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        self.corr(rhs) >> d
    }

    /// O(n log n)
    #[inline]
    pub fn diff_mul(self, rhs: Self) -> Self {
        self.semicorr(rhs.inv_borel()).borel()
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
        self = self.truncate_deg();
        let mut a = 1;
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
        (self, d) = self.truncate_and_deg_or_0();
        let mut a = mod_rfact::<M>(d as u64);
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

    /// O(n log n)
    #[inline]
    pub fn binom_trans(self, n: usize) -> Self {
        (Self::exp_x(n) * self.mod_xn(n).borel().n1pkmi(0))
            .mod_xn(n)
            .inv_borel()
            .resize(n)
    }

    /// O(n log n)
    #[inline]
    pub fn delta_0_i(self, n: usize) -> Self {
        (Self::exp_x(n).n1pkmi(0) * self.mod_xn(n).borel())
            .mod_xn(n)
            .inv_borel()
            .resize(n)
    }

    /// O(n log n)
    #[inline]
    pub fn shift(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        Self::exp_ax(a, d + 1 as usize)
            .semicorr(self.inv_borel())
            .borel()
    }

    /// O(n log n)
    #[inline]
    pub fn shift_fall(mut self, a: E) -> Self {
        let d;
        (self, d) = self.truncate_and_deg_or_0();
        let mut a = a.rem_euclid(M as E);
        if (a - M as E).abs() < a {
            a = a - M as E;
        }
        let lhs = if a == 0 {
            return self;
        } else if a > 0 {
            Self::from_elem(1, d + 1).kci(a as usize)
        } else {
            Self::from_elem(1, d + 1).kpici((-a) as usize - 1).n1pkmi(0)
        };
        lhs.diff_mul(self)
    }

    // TODO: shift points
    #[inline]
    pub fn shift_pts(self, a: E) -> Self {
        unimplemented!()
    }

    // TODO: power projection
    // https://maspypy.com/fps-composition-and-compositional-inverse-part-1-compositional-inverse-and-power-projection
    pub fn pow_proj() {
        unimplemented!()
    }

    // TODO: composition
    // https://maspypy.com/fps-composition-and-compositional-inverse-part-1-compositional-inverse-and-power-projection
    // https://maspypy.com/fps-composition-and-compositional-inverse-part-2
    // https://judge.yosupo.jp/problem/composition_of_formal_power_series
    // https://judge.yosupo.jp/problem/composition_of_formal_power_series_large
    // https://codeforces.com/blog/entry/127674
    // https://codeforces.com/blog/entry/128204
    // https://codeforces.com/blog/entry/126124
    // TODO: composition special case low degree?
    // https://codeforces.com/blog/entry/126124
    pub fn comp(&self, b: &Self, n: usize) -> Self {
        let q = n.isqrt();
        let mut b_k = Vec::with_capacity(q);
        let b_q = b.clone().pow(q, n);
        b_k.push(Self::new(vec![1]));
        for i in 1..q {
            b_k.push((b.clone() * &b_k[i - 1]).mod_xn(n).normalize())
        }
        let mut b_qk = Self::new(vec![1]);
        let mut ans = Self::new(vec![0; n]);
        for i in 0..=n / q {
            let mut cur = Self::new(vec![0; n]);
            for j in 0..q {
                if i * q + j < self.len() {
                    cur += b_k[j].clone() * self.coeff[i * q + j];
                }
            }
            cur = cur.normalize();
            ans = (ans + cur * &b_qk).normalize();
            b_qk = (b_qk * &b_q).mod_xn(n);
        }
        ans.normalize()
    }

    // TODO: compositional inverse
    // https://maspypy.com/fps-composition-and-compositional-inverse-part-2
    // https://judge.yosupo.jp/problem/compositional_inverse_of_formal_power_series
    // https://judge.yosupo.jp/problem/compositional_inverse_of_formal_power_series_large
    // https://codeforces.com/blog/entry/128814
    pub fn cinv() -> Self {
        unimplemented!()
    }

    /// O(n log log n)
    pub fn divisor(mut self, primes: &[usize]) -> Self {
        lattice::divisor(&mut self.coeff, primes);
        self
    }

    /// O(n log log n)
    pub fn divisor_inv(mut self, primes: &[usize]) -> Self {
        lattice::divisor_inv(&mut self.coeff, primes);
        self
    }

    /// O(n log log n)
    pub fn lcm_conv(self, rhs: Self, primes: &[usize]) -> Self {
        self.divisor(&primes)
            .normalize()
            .dot(&rhs.divisor(&primes).normalize())
            .normalize()
            .divisor_inv(&primes)
    }

    /// O(n log log n)
    pub fn multiple(mut self, primes: &[usize]) -> Self {
        lattice::multiple(&mut self.coeff, primes);
        self
    }

    /// O(n log log n)
    pub fn multiple_inv(mut self, primes: &[usize]) -> Self {
        lattice::multiple_inv(&mut self.coeff, primes);
        self
    }

    /// O(n log log n)
    pub fn gcd_conv(self, rhs: Self, primes: &[usize]) -> Self {
        self.multiple(&primes)
            .normalize()
            .dot(&rhs.multiple(&primes).normalize())
            .normalize()
            .multiple_inv(&primes)
    }

    /// O(2^n n)
    pub fn subset(mut self) -> Self {
        lattice::subset(&mut self.coeff);
        self
    }

    /// O(2^n n)
    pub fn subset_inv(mut self) -> Self {
        lattice::subset_inv(&mut self.coeff);
        self
    }

    /// O(2^n n)
    pub fn and_conv(self, rhs: Self) -> Self {
        self.subset()
            .normalize()
            .dot(&rhs.subset().normalize())
            .normalize()
            .subset_inv()
    }

    /// O(2^n n^2)
    pub fn sps_mul_slice(a: &[i64], b: &[i64], o: &mut [i64]) {
        let n = a.len().trailing_zeros() as usize;
        let mut ahat = vec![vec![0; 1 << n]; n + 1];
        let mut bhat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            ahat[m.count_ones() as usize][m] = a[m];
            bhat[m.count_ones() as usize][m] = b[m];
        }
        for i in 0..=n {
            lattice::superset(&mut ahat[i]);
            lattice::superset(&mut bhat[i]);
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
            lattice::superset_inv(&mut h[i]);
        }
        for m in 0..1 << n {
            o[m] = h[m.count_ones() as usize][m] % M as E;
        }
    }

    /// O(2^n n^2)
    pub fn sps_mul(self, rhs: &Self) -> Self {
        let mut r = vec![0; self.coeff.len()];
        Self::sps_mul_slice(&self.coeff, &rhs.coeff, &mut r);
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
            lattice::superset(&mut fhat[i]);
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
            lattice::superset_inv(&mut h[i]);
        }
        for m in 0..1 << n {
            self.coeff[m] = h[m.count_ones() as usize][m];
        }
        self
    }

    /// O(2^n n)
    pub fn superset(mut self) -> Self {
        lattice::superset(&mut self.coeff);
        self
    }

    /// O(n 2^n)
    pub fn superset_inv(mut self) -> Self {
        lattice::superset_inv(&mut self.coeff);
        self
    }

    /// O(2^n n)
    pub fn or_conv(self, rhs: Self) -> Self {
        self.superset()
            .normalize()
            .dot(&rhs.superset().normalize())
            .normalize()
            .superset_inv()
    }

    /// O(2^n n)
    pub fn xor(mut self) -> Self {
        lattice::xor(&mut self.coeff);
        self
    }

    /// O(2^n n)
    pub fn xor_inv(self) -> Self {
        let n = self.len();
        self.xor() / n as E
    }

    /// O(2^n n)
    pub fn xor_conv(self, rhs: Self) -> Self {
        self.xor()
            .normalize()
            .dot(&rhs.xor().normalize())
            .normalize()
            .xor_inv()
    }

    // TODO: SPS pow proj
    // https://judge.yosupo.jp/submission/244[38
    pub fn sps_pow_proj() -> Self {
        unimplemented!()
    }

    /// O(2^n n^2)
    pub fn sps_inv(&self) -> Self {
        let n = self.len().trailing_zeros() as usize;
        let a0_inv = inverse_euclidean::<M, _>(self.coeff[0]);
        let mut res = vec![0; 1 << n];
        let mut res_hat = vec![vec![0; 1 << n]; n + 1];
        let mut self_hat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            self_hat[m.count_ones() as usize][m] = self.coeff[m];
        }
        for i in 0..=n {
            lattice::superset(&mut self_hat[i]);
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
            lattice::superset_inv(&mut res_hat[l]);
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
            lattice::superset(&mut res_hat[l]);
            res_hat[l].iter_mut().for_each(|i| *i %= M as E);
        }
        Self::new(res)
    }

    /// O(2^n n^2)
    pub fn sps_quot_slice(a: &[i64], b: &[i64], o: &mut [i64]) {
        let n = a.len().trailing_zeros() as usize;
        let a0_inv = inverse_euclidean::<M, _>(b[0]);
        let mut res_hat = vec![vec![0; 1 << n]; n + 1];
        let mut b_hat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            b_hat[m.count_ones() as usize][m] = b[m];
        }
        for i in 0..=n {
            lattice::superset(&mut b_hat[i]);
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
            lattice::superset_inv(&mut res_hat[l]);
            for x in 0..1_usize << n {
                if x.count_ones() as usize == l {
                    res_hat[l][x] = (a[x] - res_hat[l][x]) * a0_inv % M as E;
                    o[x] = res_hat[l][x];
                }
            }
            lattice::superset(&mut res_hat[l]);
            res_hat[l].iter_mut().for_each(|i| *i %= M as E);
        }
    }

    /// O(2^n n^2)
    pub fn sps_quot(self, rhs: &Self) -> Self {
        let mut r = vec![0; self.coeff.len()];
        Self::sps_mul_slice(&self.coeff, &rhs.coeff, &mut r);
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
            Self::sps_quot_slice(
                &self.coeff[1 << i..2 << i],
                &self.coeff[..1 << i],
                &mut l[1 << i..2 << i],
            );
        }
        Some(Self::new(l))
    }

    /// O(2^n n^2 log k)
    #[inline]
    pub fn sps_pow_bin(mut self, mut k: usize) -> Self {
        let mut ak = Self::from_elem(0, self.coeff.len());
        ak[0] = 1;
        while k != 0 {
            if k & 1 != 0 {
                ak = ak.sps_mul(&self);
            }
            self = self.sps_square();
            k >>= 1;
        }
        ak
    }

    // TODO: make it so that the constant term doesn't have to be 1 if possible
    /// O(2^n n^2)
    #[inline]
    pub fn sps_pow(self, k: usize) -> Self {
        (self.sps_log().unwrap() * k as E)
            .normalize()
            .sps_exp()
            .unwrap()
    }

    // TODO: comp SPS
    // https://judge.yosupo.jp/submission/140530
    // https://codeforces.com/blog/entry/92183
    pub fn comp_sps() {}

    // TODO: min plus convolution
    // https://judge.yosupo.jp/submission/296643
    // https://judge.yosupo.jp/submission/152464
    // https://judge.yosupo.jp/submission/261406
    // https://codeforces.com/blog/entry/98663
    pub fn min_plus() -> Self {
        unimplemented!()
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
            let mut res = vec![0; n + m - 1];
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
    fn mul_assign(&mut self, rhs: E) {
        if rhs == 1 {
            return;
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
        *self *= inverse_euclidean::<M, _>(rhs);
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

// TODO: bivariable genfuncs
#[derive(Clone)]
pub struct Poly2<const M: u64> {
    pub n: usize,
    pub m: usize,
    pub coeff: Vec<E>,
}

impl<const M: u64> Poly2<M> {
    #[inline]
    pub fn from_slice(n: usize, m: usize, coeff: Vec<E>) -> Self {
        Self { n, m, coeff }
    }

    #[inline]
    pub fn from_elem(n: usize, m: usize, a: E) -> Self {
        Self {
            n,
            m,
            coeff: vec![a; n * m],
        }
    }

    #[inline]
    pub fn from_fn(n: usize, m: usize, mut f: impl FnMut((usize, usize)) -> E) -> Self {
        let mut coeff = vec![0; n * m];
        for i in 0..n {
            for j in 0..m {
                coeff[i * m + j] = f((i, j));
            }
        }
        Self { n, m, coeff }
    }

    #[inline]
    pub fn enumerate_coeff(&self) -> impl Iterator<Item = (usize, usize, &E)> {
        self.coeff
            .iter()
            .enumerate()
            .map(|(i, v)| (i / self.m, i % self.m, v))
    }

    #[inline]
    pub fn enumerate_coeff_mut(&mut self) -> impl Iterator<Item = (usize, usize, &mut E)> {
        self.coeff
            .iter_mut()
            .enumerate()
            .map(|(i, v)| (i / self.m, i % self.m, v))
    }

    #[inline]
    pub fn yi(&self, i: usize) -> impl Iterator<Item = &E> {
        self.coeff.iter().skip(i).step_by(self.n)
    }

    #[inline]
    pub fn yi_mut(&mut self, i: usize) -> impl Iterator<Item = &mut E> {
        self.coeff.iter_mut().skip(i).step_by(self.n)
    }

    #[inline]
    pub fn transpose(self) -> Self {
        Self::from_fn(self.m, self.n, |(i, j)| self[(j, i)])
    }

    #[inline]
    pub fn resize_x(&mut self, n: usize) -> &mut Self {
        self.coeff.resize(self.m * n, 0);
        self.n = n;
        self
    }

    #[inline]
    pub fn resize_y(&mut self, m: usize) -> &mut Self {
        if m == self.m {
            return self;
        }
        if m < self.m {
            let mut write_idx = 0;
            for row in 0..self.n {
                let row_start = row * self.m;
                for col in 0..m {
                    self.coeff[write_idx] = self.coeff[row_start + col];
                    write_idx += 1;
                }
            }
            self.coeff.truncate(self.n * m);
        } else {
            self.coeff.resize(self.n * m, 0);
            for i in (0..self.n).rev() {
                for j in (0..self.m).rev() {
                    self.coeff[i * m + j] = self.coeff[i * self.m + j];
                }
                for j in self.m..m {
                    self.coeff[i * m + j] = 0;
                }
            }
        }
        self.m = m;
        self
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
    pub fn deg_x(&self) -> Option<usize> {
        self.coeff
            .iter()
            .rposition(|&i| i % M as E != 0)
            .map(|i| i / self.m)
    }

    #[inline]
    pub fn deg_y(&self) -> Option<usize> {
        (0..self.m).rposition(|i| self.yi(i).any(|&i| i % M as E != 0))
    }

    #[inline]
    pub fn deg_or_0_x(&self) -> usize {
        self.coeff
            .iter()
            .rposition(|&i| i % M as E != 0)
            .map_or(0, |i| i / self.m)
    }

    #[inline]
    pub fn deg_or_0_y(&self) -> usize {
        (0..self.m)
            .rposition(|i| self.yi(i).any(|&i| i % M as E != 0))
            .unwrap_or(0)
    }

    #[inline]
    pub fn dot(mut self, rhs: &Self) -> Self {
        for i in 0..self.n.min(rhs.n) {
            self.coeff[i * self.m..(i + 1) * self.m]
                .iter_mut()
                .zip(&rhs[i])
                .for_each(|(i, j)| *i *= j);
        }
        self
    }

    #[inline]
    pub fn dot_nm(mut self, n: usize, m: usize, rhs: &Self) -> Self {
        let n = n.min(self.n.min(rhs.n));
        let m = m.min(self.m.min(rhs.m));
        for i in 0..n {
            self.coeff[i * self.m..i * self.m + m]
                .iter_mut()
                .zip(&rhs[i])
                .for_each(|(i, j)| *i *= j);
        }
        self
    }

    #[inline]
    pub fn mod_xn(mut self, n: usize) -> Self {
        self.coeff.truncate(n * self.m);
        self.n = n;
        self
    }

    #[inline]
    pub fn mod_yn(mut self, m: usize) -> Self {
        if m >= self.m {
            return self;
        }
        let mut write_idx = 0;
        for row in 0..self.n {
            let row_start = row * self.m;
            for col in 0..m {
                self.coeff[write_idx] = self.coeff[row_start + col];
                write_idx += 1;
            }
        }
        self.coeff.truncate(self.n * m);
        self.m = m;
        self
    }

    // #[inline]
    // pub fn pow(self, mut rhs: u32) -> Self {
    //     let mut res = Self::eye(self.n, self.m);
    //     let mut a = self;
    //     while rhs != 0 {
    //         if rhs & 1 != 0 {
    //             res = &res * &a;
    //         }
    //         a = &a * &a;
    //         rhs >>= 1;
    //     }

    //     res
    // }

    /// O(n^2 log n)
    pub fn s_i_order_j(n: usize) -> Self {
        let mut p = vec![0; n * n];
        let mobius = sieve::mobius(n + 1).0;
        for i in 1..n {
            let q = Poly::<M>::s_i_kth_unity(i, n).inv_borel();
            for j in (i..n).step_by(i) {
                if mobius[j / i] == 1 {
                    p[j * n..(j + 1) * n]
                        .iter_mut()
                        .zip(&q.coeff)
                        .for_each(|(i, j)| *i += j);
                } else if mobius[j / i] == -1 {
                    p[j * n..(j + 1) * n]
                        .iter_mut()
                        .zip(&q.coeff)
                        .for_each(|(i, j)| *i -= j);
                }
            }
        }
        Self::from_slice(n, n, p)
    }
}

impl<const M: u64> Debug for Poly2<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..self.n {
            writeln!(f, "{:?}", &self[i])?;
        }
        Ok(())
    }
}

impl<const M: u64> Index<usize> for Poly2<M> {
    type Output = [E];

    fn index(&self, i: usize) -> &Self::Output {
        &self.coeff[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: u64> IndexMut<usize> for Poly2<M> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.coeff[i * self.m..(i + 1) * self.m]
    }
}

impl<const M: u64> Index<(usize, usize)> for Poly2<M> {
    type Output = E;

    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.coeff[i * self.m + j]
    }
}

impl<const M: u64> IndexMut<(usize, usize)> for Poly2<M> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.coeff[i * self.m + j]
    }
}

impl<const M: u64> PartialEq for Poly2<M> {
    fn eq(&self, other: &Self) -> bool {
        let dx0 = self.deg_x();
        let dx1 = other.deg_x();
        let dy0 = self.deg_y();
        let dy1 = other.deg_y();
        match (dx0, dx1, dy0, dy1) {
            (None, None, None, None) => true,
            (Some(dx0), Some(dx1), Some(dy0), Some(dy1)) => {
                if dx0 != dx1 || dy0 != dy1 {
                    return false;
                }
                for i in 0..=dx0 {
                    if self[i]
                        .iter()
                        .zip(&other[i])
                        .take(dy0)
                        .any(|(&i, &j)| (i - j) % M as E != 0)
                    {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl<const M: u64> Eq for Poly2<M> {}

impl<const M: u64> Neg for Poly2<M> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        self.coeff.iter_mut().for_each(|v| *v = -*v);
        self
    }
}

impl<const M: u64> Add<Self> for &Poly2<M> {
    type Output = Poly2<M>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut s = self.clone();
        s += rhs;
        s
    }
}

impl<const M: u64> Add<Self> for Poly2<M> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += &rhs;
        self
    }
}

impl<const M: u64> Add<&Self> for Poly2<M> {
    type Output = Self;

    fn add(mut self, rhs: &Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const M: u64> AddAssign<&Self> for Poly2<M> {
    fn add_assign(&mut self, rhs: &Self) {
        for i in 0..self.n.min(rhs.n) {
            self.coeff[i * self.m..(i + 1) * self.m]
                .iter_mut()
                .zip(&rhs[i])
                .for_each(|(i, j)| *i += j);
        }
    }
}

impl<const M: u64> AddAssign<Self> for Poly2<M> {
    fn add_assign(&mut self, rhs: Self) {
        *self += &rhs;
    }
}

impl<const M: u64> Sub<Self> for Poly2<M> {
    type Output = Poly2<M>;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const M: u64> SubAssign<&Self> for Poly2<M> {
    fn sub_assign(&mut self, rhs: &Self) {
        for i in 0..self.n.min(rhs.n) {
            self.coeff[i * self.m..(i + 1) * self.m]
                .iter_mut()
                .zip(&rhs[i])
                .for_each(|(i, j)| *i -= j);
        }
    }
}

impl<const M: u64> SubAssign<Self> for Poly2<M> {
    fn sub_assign(&mut self, rhs: Self) {
        *self -= &rhs;
    }
}

impl<const M: u64> Mul<Self> for Poly2<M> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64> Mul<&Self> for Poly2<M> {
    type Output = Self;

    fn mul(mut self, rhs: &Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64> MulAssign<&Self> for Poly2<M> {
    fn mul_assign(&mut self, rhs: &Self) {
        let rhs = rhs.clone();
        *self *= rhs;
    }
}

impl<const M: u64> MulAssign<Self> for Poly2<M> {
    fn mul_assign(&mut self, rhs: Self) {
        unimplemented!()
    }
}

// TODO: CDQ convolution
// https://codeforces.com/blog/entry/11139
// https://robert1003.github.io/2020/01/31/cdq-divide-and-conquer.html

#[derive(Clone)]
pub struct Affine<const M: u64> {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

impl<const M: u64> PartialEq for Affine<M> {
    fn eq(&self, other: &Self) -> bool {
        (
            self.a - other.a % M,
            self.b - other.b % M,
            self.c - other.c % M,
        ) == (0, 0, 0)
    }
}

impl<const M: u64> Eq for Affine<M> {}

impl<const M: u64> PartialOrd for Affine<M> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (
            self.a - other.a % M,
            self.b - other.b % M,
            self.c - other.c % M,
        )
            .partial_cmp(&(0, 0, 0))
    }
}

impl<const M: u64> Ord for Affine<M> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            self.a - other.a % M,
            self.b - other.b % M,
            self.c - other.c % M,
        )
            .cmp(&(0, 0, 0))
    }
}

impl<const M: u64> Affine<M> {
    pub fn new(a: u64, b: u64, c: u64) -> Self {
        Affine {
            a: a % M,
            b: b % M,
            c: c % M,
        }
    }

    pub fn eval(&self, x: u64) -> u64 {
        self.a + self.b * x
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

impl<const M: u64> MulAssign<Self> for Affine<M> {
    fn mul_assign(&mut self, rhs: Self) {
        *self *= &rhs;
    }
}

impl<const M: u64> Mul<Self> for &Affine<M> {
    type Output = Affine<M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut s = self.clone();
        s *= rhs;
        s
    }
}

impl<const M: u64> Mul<Self> for Affine<M> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= &rhs;
        self
    }
}
