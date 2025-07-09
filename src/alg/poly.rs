use super::{
    lattice,
    ntt::{intt, ntt, ntt_conv, ntt_conv_self},
    ops::{
        inverse_euclidean, inverses, inverses_n_div, mod_pow, mod_pow_signed, mod_rfact, mod_sqrt,
    },
    sieve::sieve_complete,
};
use std::{
    fmt::Debug,
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

#[derive(Clone)]
pub struct Poly<const M: u64> {
    pub coeff: Vec<i64>,
}

impl<const M: u64> Poly<M> {
    #[inline]
    pub fn new(coeff: Vec<i64>) -> Self {
        Self { coeff }
    }

    #[inline]
    pub fn from_elem(a: i64, n: usize) -> Self {
        Self { coeff: vec![a; n] }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.coeff.len()
    }

    #[inline]
    pub fn deg_or_0(&self) -> usize {
        self.coeff.iter().rposition(|&i| i != 0).unwrap_or_else(|| {
            self.coeff
                .first()
                .map_or(0, |&v| if v != 0 { self.len() } else { 0 })
        })
    }

    #[inline]
    pub fn deg(&self) -> Option<usize> {
        self.coeff.iter().rposition(|&i| i != 0).or_else(|| {
            self.coeff
                .first()
                .map_or(None, |&v| if v != 0 { Some(self.len() - 1) } else { None })
        })
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
    pub fn push(mut self, v: i64) -> Self {
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
    pub fn normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i %= M as i64;
        });
        self
    }

    #[inline]
    pub fn pos_normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i = i.rem_euclid(M as i64);
        });
        self
    }

    #[inline]
    pub fn neg_normalize(mut self) -> Self {
        self.coeff.iter_mut().for_each(|i| {
            *i = i.rem_euclid(M as i64);
            if (*i - M as i64).abs() < i.abs() {
                *i = *i - M as i64;
            }
        });
        self
    }

    #[inline]
    pub fn normalize_n(mut self, n: usize) -> Self {
        self.coeff.iter_mut().take(n).for_each(|i| {
            *i = i.rem_euclid(M as i64);
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
    pub fn fill(mut self, v: i64) -> Self {
        self.coeff.fill(v);
        self
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
    pub fn resultant(self, rhs: Self) -> i64 {
        unimplemented!()
    }

    pub fn roots() {
        unimplemented!()
    }

    #[inline]
    pub fn sub_xk(mut self, k: usize) -> Self {
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

    /// O(n log n)
    pub fn inv(&self, n: usize) -> Option<Self> {
        let a0 = self.coeff.get(0).copied().unwrap_or(0).rem_euclid(M as i64) as u64;
        if a0 == 0 {
            return None;
        }
        let a0_inv = inverse_euclidean::<M>(a0);
        let mut r = Self::new(vec![a0_inv as i64]).resize(n.next_power_of_two());
        let mut k = 1;
        while k < n {
            let g = Self::new(r.coeff.clone()).resize(k << 1).ntt();
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
                r[i] = -f[i] % M as i64;
            }
            k <<= 1;
        }
        Some(r)
    }

    #[inline]
    pub fn eval(&self, x: i64) -> i64 {
        let mut res = 0;
        for i in (0..=self.deg_or_0()).rev() {
            res *= x;
            res += self.coeff[i];
            res %= M as i64;
        }
        res
    }

    #[inline]
    pub fn lead(&self) -> i64 {
        self.coeff[self.deg_or_0()]
    }

    #[inline]
    pub fn lead_inv(&self) -> i64 {
        inverse_euclidean::<M>(self.coeff[self.deg_or_0()].rem_euclid(M as i64) as u64) as i64
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.deg().is_none()
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
            .for_each(|(i, v)| *v *= i as i64);
        self
    }

    /// O(n)
    #[inline]
    pub fn diff_k(self, k: usize) -> Self {
        (self.inv_borel() >> k).borel()
    }

    #[inline]
    pub fn integr(self) -> Self {
        (self << 1).integr_divx()
    }

    #[inline]
    pub fn integr_n(self, n: usize) -> Self {
        (self << 1).integr_divx_n(n)
    }

    #[inline]
    pub fn integr_divx(self) -> Self {
        let d = self.deg_or_0();
        self.integr_divx_n(d + 1)
    }

    #[inline]
    pub fn integr_divx_n(mut self, n: usize) -> Self {
        self.coeff.truncate(n);
        self.coeff
            .iter_mut()
            .take(n)
            .zip(inverses_n_div::<M>(n + 1))
            .for_each(|(v, inv)| *v *= inv as i64);
        self
    }

    /// O(n)
    #[inline]
    pub fn integr_k(self, k: usize) -> Self {
        (self.inv_borel() << k).borel()
    }

    #[inline]
    pub fn trailing_xk(&self) -> usize {
        self.coeff.iter().position(|&i| i != 0).unwrap_or(0)
    }

    /// O(n log n)
    #[inline]
    pub fn log(self, n: usize) -> Option<Self> {
        if let Some(v) = self.inv(n) {
            Some(
                (self.mod_xn(n).diff_x().normalize() * v)
                    .mod_xn(n)
                    .integr_divx(),
            )
        } else {
            None
        }
    }

    /// O(n log n)
    pub fn exp(&self, n: usize) -> Option<Self> {
        if self.len() == 1 {
            return Some(Self::new(vec![1]));
        }
        if self.coeff.get(0).copied().unwrap_or(0) != 0 {
            return None;
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
                e_k_inv[i] = -eps[i] % M as i64;
            }
            e_k_inv_ntt = e_k_inv_ntt.resize(i << 2).copy_n(i << 1, &e_k_inv).ntt();
            let mut e_d = ((self
                .clone_mod_xn(i << 1)
                .diff()
                .normalize()
                .resize(i << 2)
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1) - 1)
                .resize(i << 2)
                .ntt()
                .dot(&e_k_inv_ntt)
                .intt()
                .normalize()
                << (i << 1) - 1)
                .resize(i << 2)
                .pop()
                .integr()
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

    /// O(n log n)
    pub fn exp_and_inv(&self, n: usize) -> Option<(Self, Self)> {
        if self.len() == 1 {
            return Some((Self::new(vec![1]), Self::new(vec![1])));
        }
        if self.coeff.get(0).copied().unwrap_or(0) != 0 {
            return None;
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
                e_k_inv[i] = -eps[i] % M as i64;
            }
            if i >= n >> 1 {
                break Some((e_k, e_k_inv));
            }
            e_k_inv_ntt = e_k_inv_ntt.resize(i << 2).copy_n(i << 1, &e_k_inv).ntt();
            let mut e_d = ((self
                .clone_mod_xn(i << 1)
                .diff()
                .resize(i << 2)
                .ntt()
                .dot(&e_k_ntt)
                .intt()
                .normalize()
                >> (i << 1) - 1)
                .resize(i << 2)
                .ntt()
                .dot(&e_k_inv_ntt)
                .intt()
                .normalize()
                << (i << 1) - 1)
                .resize(i << 2)
                .pop()
                .integr()
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
    #[inline]
    pub fn sinh(&self, n: usize) -> Option<Self> {
        let (mut e0, e1) = self.exp_and_inv(n)?;
        e0 -= &e1;
        e0 *= inverse_euclidean::<M>(2) as i64;
        Some(e0)
    }

    /// O(n log n)
    #[inline]
    pub fn cosh(&self, n: usize) -> Option<Self> {
        let (mut e0, e1) = self.exp_and_inv(n)?;
        e0 += &e1;
        e0 *= inverse_euclidean::<M>(2) as i64;
        Some(e0)
    }

    /// O(n log n)
    #[inline]
    pub fn tanh(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n) * 2;
        let mut e = p.exp(n)?;
        p = p.resize(e.len());
        p.coeff.copy_from_slice(&e.coeff);
        p -= 1;
        e += 1;
        Some(p * e.inv(n)?)
    }

    /// O(n log n)
    #[inline]
    pub fn coth(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n) * 2;
        let mut e = p.exp(n)?;
        p = p.resize(e.len());
        p.coeff.copy_from_slice(&e.coeff);
        p += 1;
        e -= 1;
        e >>= 1;
        p *= e.inv(n)?;
        p >>= 1;
        Some(p)
    }

    /// O(n log n)
    #[inline]
    pub fn sech(&self, n: usize) -> Option<Self> {
        let (mut e0, e1) = self.exp_and_inv(n)?;
        e0 += e1;
        let mut d = e0.inv(n)?;
        d *= 2;
        Some(d)
    }

    /// O(n log n)
    #[inline]
    pub fn csch(&self, n: usize) -> Option<Self> {
        let (mut e0, e1) = self.exp_and_inv(n)?;
        e0 -= e1;
        e0 >>= 1;
        let mut d = e0.inv(n)?;
        d *= 2;
        d >>= 1;
        Some(d)
    }

    /// O(n log n)
    #[inline]
    pub fn asinh(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        let q = p.clone();
        p = p.square() + 1;
        let mut p = p.sqrt(n)?;
        p += q;
        p.log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn acosh(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        let q = p.clone();
        p = p.square() - 1;
        let mut p = p.sqrt(n)?;
        p += q;
        p.log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn atanh(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        let q = -p.clone() + 1;
        p += 1;
        p *= q.inv(n)?;
        p = p.log(n)?.normalize();
        p *= inverse_euclidean::<M>(2) as i64;
        Some(p)
    }

    /// O(n log n)
    #[inline]
    pub fn acoth(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        let q = p.clone() - 1;
        Some(((p + 1) * q.inv(n)?).log(n)?.normalize() * inverse_euclidean::<M>(2) as i64)
    }

    /// O(n log n)
    #[inline]
    pub fn asech(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        let q = p.inv(n)?;
        (((-p + 1).sqrt(n)? + 1) * q).log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn acsch(&self, n: usize) -> Option<Self> {
        let mut p = self.clone_mod_xn(n);
        let q = p.inv(n)?;
        p += 1;
        p = p.sqrt(n)?;
        p += 1;
        p *= q;
        p.log(n)
    }

    /// O(n log n)
    #[inline]
    pub fn asin(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        Some(
            ((-p.clone().square() + 1).sqrt_and_inv(n)?.1? * p.clone().diff())
                .integr()
                .mod_xn(n),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn acos(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        Some(
            ((-p.clone().square() + 1).sqrt_and_inv(n)?.1? * -p.diff())
                .normalize()
                .integr()
                .mod_xn(n),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn atan(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        Some(
            ((p.clone().square() + 1).inv(n)? * p.diff())
                .integr()
                .mod_xn(n),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn acot(&self, n: usize) -> Option<Self> {
        let p = self.clone_mod_xn(n);
        Some(
            ((p.clone().square() + 1).inv(n)? * -p.diff())
                .normalize()
                .integr()
                .mod_xn(n),
        )
    }

    /// O(n log n)
    #[inline]
    pub fn square(mut self) -> Self {
        ntt_conv_self::<M>(&mut self.coeff);
        self.normalize()
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
        q[0] = mod_pow::<M>(self.coeff[0].rem_euclid(M as i64) as u64, k as u64) as i64;
        let a0_inv = inverse_euclidean::<M>(self.coeff[0].rem_euclid(M as i64) as u64);
        for i in 1..n {
            for j in 1..=d.min(n).min(i) {
                q[i] += (self.coeff[j] % M as i64 * (q[i - j] % M as i64)) % M as i64
                    * (k as i64 * j as i64 % M as i64 - (i - j) as i64)
                    % M as i64;
            }
            q[i] %= M as i64;
            q[i] *= inverse_euclidean::<M>(i as u64) as i64 * a0_inv as i64 % M as i64;
        }
        q.normalize()
    }

    /// O(n log n)
    pub fn pow(self, k: usize, n: usize) -> Self {
        const MAGIC: usize = 1 << 9;
        let i = self.coeff.iter().position(|&i| i != 0);
        if let Some(i) = i {
            if i > 0 {
                if k >= (n + i - 1) / i {
                    Self::new(vec![])
                } else {
                    let mut s = self.clone();
                    s >>= i;
                    let mut p = s.pow(k, n - i * k);
                    p <<= i * k;
                    p
                }
            } else {
                if self.deg_or_0().min(n) <= MAGIC {
                    self.pow_dn(k, n)
                } else if k <= MAGIC {
                    self.pow_bin(k, n)
                } else {
                    let a0k =
                        mod_pow::<M>(self.coeff[i].rem_euclid(M as i64) as u64, k as u64) as i64;
                    (self.log(n).unwrap().normalize() * (k as u64 % M) as i64)
                        .exp(n)
                        .unwrap()
                        .mod_xn(n)
                        * a0k
                }
            }
        } else {
            if k == 0 {
                self.clone()
            } else {
                Self::new(vec![])
            }
        }
    }

    /// O(n log n)
    pub fn sqrt(&self, n: usize) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::from_elem(0, 0));
        }
        let i = self.trailing_xk();
        if i != 0 && i & 1 == 0 {
            return None;
        } else if i != 0 {
            let ans = self.clone().div_xn(i).sqrt(n - i >> 1);
            return if let Some(mut ans) = ans {
                ans <<= i >> 1;
                Some(ans)
            } else {
                ans
            };
        }
        let half = inverse_euclidean::<M>(2) as i64;
        let st = mod_sqrt::<M>(self.coeff[0].rem_euclid(M as i64) as u64)?;
        let st_inv = inverse_euclidean::<M>(st);
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::from_elem(st as i64, 1),
            Self::from_elem(st_inv as i64, 1),
            Self::from_elem(st as i64, 1),
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
                delta[k + i] = (z[i] - freq(i) - freq(k + i)) % M as i64;
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
                f[i] = (-half * delta[i]) % M as i64;
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
                g[i] = -eps[i] % M as i64;
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
        let i = self.trailing_xk();
        if i != 0 && i & 1 == 0 {
            return None;
        } else if i != 0 {
            let ans = self.clone().div_xn(i).sqrt(n - i >> 1);
            return if let Some(mut ans) = ans {
                ans <<= i >> 1;
                Some((ans, None))
            } else {
                None
            };
        }
        let half = inverse_euclidean::<M>(2) as i64;
        let st = mod_sqrt::<M>(self.coeff[0].rem_euclid(M as i64) as u64)?;
        let st_inv = inverse_euclidean::<M>(st);
        let (mut f, mut g, mut z, mut delta, mut gbuf) = (
            Self::from_elem(st as i64, 1),
            Self::from_elem(st_inv as i64, 1),
            Self::from_elem(st as i64, 1),
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
                delta[k + i] = (z[i] - freq(i) - freq(k + i)) % M as i64;
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
                f[i] = (-half * delta[i]) % M as i64;
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
                g[i] = -eps[i] % M as i64;
            }
            k <<= 1;
        }
        Some((f, Some(g)))
    }

    /// O(n log n)
    pub fn div_mod_ri(&self, q: &Self, qri: &Self) -> (Self, Self) {
        let q_d = q.deg_or_0();
        let d = self.deg_or_0() as i32 - q_d as i32;
        if d.min(q_d as i32) <= 1 << 9 {
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
        let remainder = self - &(&quotient * q);
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
            let coeff = (r.lead() * q_lead_inv).rem_euclid(M as i64);
            d.coeff.push(coeff);
            if coeff != 0 {
                let deg_diff = r.deg_or_0() - q.deg_or_0();
                for i in 0..=q.deg_or_0() {
                    if deg_diff + i < r.coeff.len() {
                        r.coeff[deg_diff + i] =
                            (r.coeff[deg_diff + i] - coeff * q.coeff[i]).rem_euclid(M as i64);
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
    pub fn circular_closure(mut self, m: usize) -> Self {
        let d = self.coeff.iter().rposition(|&i| i != 0);
        if let Some(d) = d {
            for i in (m..=d).rev() {
                self.coeff[i - m] += self.coeff[i];
            }
            let l = self.len();
            self = self.resize(l.min(m));
        }
        self
    }

    #[inline]
    pub fn mul_circular(mut self, rhs: Self, m: usize) -> Self {
        self = self.circular_closure(m);
        self *= rhs;
        self.circular_closure(m).normalize()
    }

    #[inline]
    pub fn square_circular(self, m: usize) -> Self {
        self.circular_closure(m)
            .square()
            .circular_closure(m)
            .normalize()
    }

    /// O(m log m log k)
    #[inline]
    pub fn pow_bin_circular(mut self, mut k: usize, m: usize) -> Self {
        self = self.circular_closure(m);
        let mut ak = Self::from_elem(1, 1);
        while k != 0 {
            if k & 1 != 0 {
                ak = ak.mul_circular(self.clone(), m);
            }
            self = self.square_circular(m);
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
            self.pow_bin_circular(k, d)
        } else {
            self.pow_mod_ri(k, &md, &md.clone().reverse_n(d + 1).inv(d + 1).unwrap())
        }
    }

    /// O(d log d log n)
    #[inline]
    pub fn nth_rec(&mut self, mut q: Self, mut n: usize) -> i64 {
        while n > 0 {
            q = q.n1pkmi(0);
            if n & 1 == 0 {
                *self = self.mul_even(&q, n);
            } else {
                *self = self.mul_odd(&q, n);
            }
            q = q.mul_neg_self_even(n);
            n >>= 1;
        }
        (self.coeff[0] * inverse_euclidean::<M>(q.coeff[0].rem_euclid(M as i64) as u64) as i64)
            % M as i64
    }

    #[inline]
    pub fn mulx_a(mut self, a: i64) -> Self {
        let mut cur = 1;
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= cur;
            cur *= a;
            cur %= M as i64;
        }
        self
    }

    #[inline]
    pub fn mulx_apic2(mut self, a: i64) -> Self {
        let (mut cur, mut total) = (1, 1);
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= total;
            self.coeff[i] %= M as i64;
            total *= cur;
            total %= M as i64;
            cur *= a;
            cur %= M as i64;
        }
        self
    }

    #[inline]
    pub fn mulx_apic2_ti(mut self, a: i64, t: i64) -> Self {
        let (mut cur, mut total, mut ti) = (1, 1, 1);
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= (total * ti) % M as i64;
            self.coeff[i] %= M as i64;
            total *= cur;
            total %= M as i64;
            cur *= a;
            cur %= M as i64;
            ti *= t;
            ti %= M as i64;
        }
        self
    }

    #[inline]
    pub fn mulx_apip1c2(mut self, a: i64) -> Self {
        let (mut cur, mut total) = (1, 1);
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= total;
            cur *= a;
            cur %= M as i64;
            total *= cur;
            total %= M as i64;
        }
        self
    }

    /// O(n log n)
    pub fn chirpz(&self, z: i64, k: usize) -> Self {
        let mut z = z.rem_euclid(M as i64);
        if (z - M as i64).abs() < z {
            z = z - M as i64;
        }
        if self.is_zero() {
            Self::new(vec![0; k])
        } else if z == 0 {
            let mut ans = vec![self.coeff[0]; k];
            if k > 0 {
                ans[0] = self.coeff.iter().sum();
            }
            Self::new(ans)
        } else {
            let mut z_inv = inverse_euclidean::<M>(z.rem_euclid(M as i64) as u64) as i64;
            if (z_inv - M as i64).abs() < z_inv {
                z_inv = z_inv - M as i64;
            }
            Self::from_elem(1, k + self.deg_or_0())
                .mulx_apic2(z)
                .semicorr(self.clone().mulx_apic2(z_inv))
                .mod_xn(k)
                .mulx_apic2(z_inv)
        }
    }

    /// O(n)
    /// ∏_{1 <= j <= i} 1/(1 - z^j)
    #[inline]
    pub fn pref_prod_1o1mzi(z: i64, n: usize) -> Self {
        let mut p = vec![1; n];
        let mut zk = vec![0; n];
        zk[0] = 1;
        for i in 1..n {
            zk[i] = (zk[i - 1] * z) % M as i64;
            p[i] = (p[i - 1] * (1 - zk[i])) % M as i64;
        }
        if let Some(l) = p.last_mut() {
            *l = inverse_euclidean::<M>(l.rem_euclid(M as i64) as u64) as i64;
        }
        for i in (0..n - 1).rev() {
            p[i] = ((1 - zk[i + 1]) * p[i + 1]) % M as i64;
        }
        Self::new(p)
    }

    /// O(n)
    /// ∏_{i < k} (1 + z^i t x) = ∑_{i=0}^k z^(i, 2) \[k,i\]_z t^i mod x^n
    #[inline]
    pub fn prod_1pzitx(z: i64, t: i64, k: usize, n: usize) -> Self {
        Self::from_elem(1, n.min(k)).kqci(k, z).mulx_apic2_ti(z, t)
    }

    /// O(n)
    /// ∏_{i < k} 1/(1 - z^i x) = ∑_{i=0}^k \[k+i-1,i\]_z mod x^n
    #[inline]
    pub fn prod_1o1mzix(z: i64, k: usize, n: usize) -> Self {
        Self::from_elem(1, n).kpiqci(k - 1, z)
    }

    /// O(n)
    /// ∏_i (1 + z^i x) mod x^n = ∑_i z^(i,2)/(z;z)_i x^i
    #[inline]
    pub fn prod_inf_1pzix(z: i64, n: usize) -> Self {
        Self::from_elem(1, n).mulx_apic2(z).q_poch_trans(z)
    }

    /// O(n)
    /// ∏_i 1/(1 - z^i x) = ∑_i x^i/(q; q)_i mod x^n
    #[inline]
    pub fn prod_inf_1o1mzix(z: i64, n: usize) -> Self {
        Self::from_elem(1, n).q_poch_trans(z)
    }

    /// O(n log n)
    #[inline]
    pub fn chirpz_inv(&self, z: i64, k: usize) -> Self {
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
        let prods_neg = Self::pref_prod_1o1mzi(
            inverse_euclidean::<M>(z.rem_euclid(M as i64) as u64) as i64,
            k,
        );
        let zk = inverse_euclidean::<M>(mod_pow::<M>(z.rem_euclid(M as i64) as u64, k as u64 - 1));
        let mut zki = 1;
        for i in 0..k {
            y[i] *= ((zki as i64 * prods_neg[i]) % M as i64 * prods_pos[(k - 1) - i]) % M as i64;
            y[i] %= M as i64;
            zki = (zki * zk) % M;
        }
        let p_over_q = y.chirpz(z, k);
        let q = Self::prod_1pzitx(z, -1, k, k);
        (p_over_q * q).mod_xn(k).reverse_n(k)
    }

    /// O(n log^2 n)
    #[inline]
    pub fn build_eval_tree(tree: &mut [Self], pts: &[i64], v: usize, l: usize, r: usize) -> Self {
        if r - l == 1 {
            let res = Self::new(vec![-pts[l], 1]);
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
    pub fn eval_tree(&self, tree: &[Self], v: usize, l: usize, r: usize) -> Vec<i64> {
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
            let a = (self % &tree[v << 1]).to_newton_tree(tree, v << 1, l, m);
            let b = (self / &tree[v << 1]).to_newton_tree(tree, v << 1 | 1, m, r) << m - l;
            a.resize_max(b.len()) + b
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn to_newton(&self, p: &[i64]) -> Self {
        if self.is_zero() {
            self.clone()
        } else {
            let n = p.len();
            let mut tree = vec![Self::new(vec![]); n << 2];
            Self::build_eval_tree(&mut tree, &p, 1, 0, n);
            self.to_newton_tree(&tree, 1, 0, n)
        }
    }

    /// O(n log^2 n)
    #[inline]
    pub fn evals(&self, x: &[i64]) -> Vec<i64> {
        let n = x.len();
        if self.is_zero() {
            return vec![0; n];
        }
        let mut tree = vec![Self::new(vec![]); n << 2];
        Self::build_eval_tree(&mut tree, &x, 1, 0, x.len());
        self.eval_tree(&tree, 1, 0, x.len())
    }

    /// O(n log^2 n)
    pub fn interp_tree(&self, tree: &[Self], y: &[i64], v: usize, l: usize, r: usize) -> Self {
        if r - l == 1 {
            Self::new(vec![
                (y[l] * inverse_euclidean::<M>(self.coeff[0].rem_euclid(M as i64) as u64) as i64)
                    % M as i64,
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
    pub fn interp(x: &[i64], y: &[i64]) -> Self {
        let n = x.len();
        let mut tree = vec![Self::new(vec![]); n << 2];
        Self::build_eval_tree(&mut tree, &x, 1, 0, x.len())
            .diff()
            .interp_tree(&tree, &y, 1, 0, y.len())
    }

    #[inline]
    pub fn xn(n: usize) -> Self {
        Self::new(vec![0; n]).push(1)
    }

    #[inline]
    pub fn txnpz(t: i64, z: i64, n: usize) -> Self {
        let mut s = Self::new(vec![0; n]).push(t);
        s[0] = z;
        s
    }

    /// O(n)
    #[inline]
    pub fn exp_x(n: usize) -> Self {
        Self::new(vec![1; n]).borel()
    }

    /// O(n)
    #[inline]
    pub fn kn_1_factors(n: usize) -> Self {
        let mut p = Vec::with_capacity(n);
        let mut a = 1;
        for i in (0..n).step_by(2) {
            p.push(a as i64);
            p.push(0);
            a = (a * (i as u64 | 1)) % M;
        }
        if n & 1 != 0 {
            p.pop();
        }
        Self::new(p)
    }

    /// O(n)
    pub fn fact2(mut self) -> Self {
        let n = self.coeff.len();
        let mut a = 1;
        let mut b = 1;
        for i in (1..n - 1).step_by(2) {
            a = (a * i as u64) % M;
            b = (b * (i as u64 + 1)) % M;
            self.coeff[i] *= a as i64;
            self.coeff[i + 1] *= b as i64;
        }
        if n & 1 == 0 {
            a = (a * (n - 1) as u64) % M;
            self.coeff[n - 1] *= a as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn exp_x2o2(n: usize) -> Self {
        Self::kn_1_factors(n).borel()
    }

    /// O(n)
    pub fn telephone(mut self) -> Self {
        let n = self.coeff.len();
        let mut a = 1;
        let mut b = 1;
        for i in 2..n {
            (a, b) = (b, (b + (i as u64 - 1) * a) % M);
            self.coeff[i] *= b as i64;
        }
        self
    }

    #[inline]
    pub fn exp_ax(a: i64, n: usize) -> Self {
        let a = a % M as i64;
        let mut coeff = Vec::with_capacity(n);
        coeff.push(1);
        let mut an = a;
        for _ in 1..n {
            coeff.push(an);
            an *= a;
            an %= M as i64;
        }
        Self::new(coeff).borel()
    }

    #[inline]
    pub fn fall_fact(self, k: usize) -> Self {
        (self.inv_borel() >> k).borel() << k
    }

    #[inline]
    pub fn fall_fact_k(mut self, k: usize) -> Self {
        let mut a = 1;
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= a as i64;
            a *= (k - i) as u64;
            a %= M;
        }
        self
    }

    #[inline]
    pub fn rise_fact(self, k: usize) -> Self {
        ((self << k - 1).inv_borel() >> k).borel() << 1
    }

    #[inline]
    pub fn rise_fact_k(mut self, k: usize) -> Self {
        let mut a = 1;
        for i in 0..=self.deg_or_0() {
            self.coeff[i] *= a as i64;
            a *= (k + i) as u64;
            a %= M;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn fact_i_kmi(self, k: usize) -> Self {
        self.inv_borel().reverse_k(k).inv_borel().reverse_k(k)
    }

    /// O(n)
    #[inline]
    pub fn rfact_i_kmi(self, k: usize) -> Self {
        self.borel().reverse_k(k).borel().reverse_k(k)
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
    pub fn kci(mut self, k: usize, n: usize) -> Self {
        let n = n.min(self.len());
        let invs = inverses_n_div::<M>(n);
        let mut a = 1;
        for i in 1..n {
            a *= (k + 1 - i) as u64 * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn kcipz(self, k: usize, z: isize, n: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kci(k, n + z) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kci(k, n - z) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn kpici(mut self, k: usize, n: usize) -> Self {
        let n = n.min(self.len());
        let invs = inverses_n_div::<M>(n);
        let mut a = 1;
        for i in 1..n {
            a *= (i + k) as u64 * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn kpipzcipz(self, z: isize, k: usize, n: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).kpici(k, n + z) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).kpici(k, n - z) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn ick(mut self, k: usize, n: usize) -> Self {
        let l = self.len();
        let n = n.min(l);
        let invs = inverses_n_div::<M>(n - k);
        self.coeff[0..k.min(l)].fill(0);
        let mut a = 1;
        for i in k + 1..n {
            a *= i as u64 * invs[i - k] % M;
            a %= M;
            self.coeff[i] *= a as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn ipzck(self, z: isize, k: usize, n: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).ick(k, n + z) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).ick(k, n - z) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn i2ci(mut self, n: usize) -> Self {
        let mut a = 1;
        let invs = inverses_n_div::<M>(n);
        for i in 1..n {
            a *= ((((i as u64) << 1) - 1) << 1) * invs[i] % M;
            a %= M;
            self.coeff[i] *= a as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn i2pzcipz(self, z: isize, n: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).i2ci(n + z) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).i2ci(n - z) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn i2qci(mut self, q: i64, n: usize) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let mut qim1s = Vec::with_capacity((n << 1) + 3);
        let mut qi = q;
        for _ in 0..(n << 1) + 3 {
            qim1s.push(qi - 1);
            qi = (qi * q) % M;
        }
        let qim1is = inverses::<M>(&qim1s);
        let mut l = 1;
        for i in 1..n.min(self.coeff.len()) {
            l = (((l * qim1s[(i << 1) - 1]) % M * qim1s[(i << 1) - 2] % M) * qim1is[i - 1]) % M
                * qim1is[i - 1]
                % M;
            self.coeff[i] *= l as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn i2pzqcipz(self, z: isize, q: i64, n: usize) -> Self {
        if z >= 0 {
            let z = z as usize;
            (self << z).i2qci(q, n + z) >> z
        } else {
            let z = (-z) as usize;
            (self >> z).i2qci(q, n - z) << z
        }
    }

    /// O(n)
    #[inline]
    pub fn sum_pwrs(mut self, p: usize, n: usize) -> Self {
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
            self.coeff[i] *= ppw as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(p log p)
    #[inline]
    pub fn faulhaber_kp(k: u64, p: usize) -> u64 {
        let mut a = 0;
        let b = Self::bernoulli_plus(p + 1).inv_borel().kci(p + 1, p + 1);
        let mut kp1mr = k;
        for i in (0..=p).rev() {
            a += b[i] * kp1mr as i64;
            a %= M as i64;
            kp1mr = (kp1mr * k) % M;
        }
        (a * inverse_euclidean::<M>(p as u64 + 1) as i64).rem_euclid(M as i64) as u64
    }

    /// O(p log p)
    #[inline]
    pub fn faulhaber_xp(p: usize) -> Self {
        let b = Self::bernoulli_plus(p + 1)
            .inv_borel()
            .kci(p + 1, p + 1)
            .reverse_k(p + 1);
        let mut s = b * inverse_euclidean::<M>(p as u64 + 1) as i64;
        s[0] = 0;
        s
    }

    /// O(n log n)
    #[inline]
    pub fn pref_x(self) -> Self {
        let d = self.deg_or_0();
        let b = Self::bernoulli_plus(d + 1).reverse_k(d);
        let p0 = self.coeff[0];
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
            .for_each(|(i, j)| *i *= j as i64);
        self
    }

    /// O(n)
    #[inline]
    pub fn pref(mut self, n: usize) -> Self {
        let mut p = 0;
        for i in 0..n {
            p += self.coeff[i];
            p %= M as i64;
            self.coeff[i] = p;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn sum_pwrs_k(k: usize, n: usize) -> Self {
        let mut e = Self::exp_x(n + 1);
        e = ((-e.clone() + 1) >> 1).inv(n).unwrap().normalize()
            * ((e - Self::exp_ax(k as i64 + 1, n + 1)) >> 1).normalize();
        if e.is_zero() {
            e.coeff.push(0);
        } else {
            e[0] += 1;
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
                acc %= M as i64;
            }
            p[i] = acc;
        }
        Self::new(p)
    }

    /// O(n log n)
    /// \[q^z\] \[k!\]_q = permutations on k elements with z inversions
    #[inline]
    pub fn log_q_fact(k: usize, n: usize) -> Self {
        let n = (n.min((k * (k - 1) >> 1) + 1)).next_power_of_two();
        let mut p = vec![0; n];
        for d in 1..=k.min(n - 1) {
            for j in (d..n).step_by(d) {
                p[j] += d as i64;
            }
        }
        p.iter_mut()
            .zip(inverses_n_div::<M>(n))
            .for_each(|(v, j)| *v = ((k as i64 - *v) * j as i64) % M as i64);
        Self::new(p)
    }

    /// O(n log n)
    /// \[q^z\] \[k, i\]_q = binary strings of length k with i ones and z inversions
    /// \[q^z\] \[k+i, i\]_q = partitions of z with i or fewer parts, each less than or equal to k = partitions of z with k or fewer parts, each less than or equal to i
    /// \[q^z\] q^(i,2) \[k, i\]_q = partitions of z into k distinct parts where each is in [0,k)
    #[inline]
    pub fn log_q_bin(k: usize, i: usize, n: usize) -> Self {
        let n = (n.min(i * (k - i) + 1)).next_power_of_two();
        let mut p = vec![0; n];
        let (alpha, beta) = if i < k - i { (i, k - 1) } else { (k - i, i) };
        for d in 1..=alpha {
            for j in (d..n).step_by(d) {
                p[j] += d as i64;
            }
        }
        for d in beta + 1..=k {
            for j in (d..n).step_by(d) {
                p[j] -= d as i64;
            }
        }
        p.iter_mut()
            .zip(inverses_n_div::<M>(n))
            .for_each(|(v, j)| *v *= j as i64);
        Self::new(p)
    }

    /// O(n log n)
    #[inline]
    pub fn partition(n: usize) -> Self {
        if n <= 0x7700 {
            Self::partition_pent(n)
        } else {
            Self::pent(n).inv(n).unwrap()
        }
    }

    /// O(n log n + |k|)
    /// ∏_{i ∈ k} (1 + x^i t)
    #[inline]
    pub fn log_prod_1pxit(k: impl Iterator<Item = usize>, t: i64, n: usize) -> Self {
        let n = n.next_power_of_two();
        let mut p = vec![0; n];
        for i in k.filter(|&j| j < n) {
            let mut x = t;
            for j in (i..n).step_by(i) {
                p[j] += x * i as i64;
                x = (-t * x) % M as i64;
            }
        }
        p.iter_mut().zip(inverses_n_div::<M>(n)).for_each(|(v, j)| {
            *v *= j as i64;
            *v %= M as i64;
        });
        Self::new(p)
    }

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
            let v = ((k << 1) * i) as i64;
            let mut sign = 1;
            for j in (i..n).step_by(i) {
                sign = -sign;
                p[j] -= v * sign;
            }
        }
        for i in (2..n).step_by(2) {
            let v = (k * i) as i64;
            for j in (i..n).step_by(i) {
                p[j] -= v;
            }
        }
        p.iter_mut().zip(inverses_n_div::<M>(n)).for_each(|(i, j)| {
            *i *= j as i64;
            *i %= M as i64
        });
        Self::new(p)
    }

    /// O(n)
    #[inline]
    pub fn kqci(mut self, k: usize, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let mut qim1s = Vec::with_capacity(k);
        let mut qi = q;
        for _ in 0..k {
            qim1s.push(qi - 1);
            qi = (qi * q) % M;
        }
        let qim1is = inverses::<M>(&qim1s);
        let mut l = 1;
        for i in 1..self.coeff.len().min(k + 1) {
            l = ((l * qim1s[k - i]) % M * qim1is[i - 1]) % M;
            self.coeff[i] *= l as i64;
            self.coeff[i] %= M as i64;
        }
        self.mod_xn(k + 1)
    }

    /// O(n)
    #[inline]
    pub fn kpiqci(mut self, k: usize, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let n = self.coeff.len();
        let mut qim1s = Vec::with_capacity(n + k);
        let mut qi = q;
        for _ in 0..n + k {
            qim1s.push(qi - 1);
            qi = (qi * q) % M;
        }
        let qim1is = inverses::<M>(&qim1s);
        let mut l = 1;
        for i in 1..n {
            l = ((l * qim1s[k + i - 1] % M) * qim1is[i - 1]) % M;
            self.coeff[i] *= l as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n + max(z,0))
    #[inline]
    pub fn kqcipz(self, k: usize, z: isize, q: i64) -> Self {
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
    pub fn kpipzqcipz(self, k: usize, z: isize, q: i64) -> Self {
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
    pub fn iqck(mut self, k: usize, q: i64) -> Self {
        let l = self.len();
        let q = q.rem_euclid(M as i64) as u64;
        let n = self.coeff.len().min(l);
        let mut qim1s = Vec::with_capacity(n);
        let mut qi = q;
        for _ in 0..n {
            qim1s.push(qi - 1);
            qi = (qi * q) % M;
        }
        let qim1is = inverses::<M>(&qim1s);
        self.coeff[0..k.min(l)].fill(0);
        let mut l = 1;
        for i in k + 1..n {
            l = ((l * qim1s[i - 1] % M) * qim1is[i - k - 1]) % M;
            self.coeff[i] *= l as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n + max(z,0))
    #[inline]
    pub fn ipzqck(self, k: usize, z: isize, q: i64) -> Self {
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
    pub fn q_diff_x(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        self.coeff[0] = 0;
        let mut qi = (q * q) % M;
        let qmii = inverse_euclidean::<M>(q - 1);
        for i in 2..self.len() {
            self.coeff[i] *= (((qi - 1) * qmii) % M) as i64;
            self.coeff[i] %= M as i64;
            qi = (qi * q) % M;
        }
        self
    }

    #[inline]
    pub fn q_diff(self, q: i64) -> Self {
        self.q_diff_x(q) >> 1
    }

    /// O(n)
    #[inline]
    pub fn q_diff_k(self, k: usize, q: i64) -> Self {
        (self.q_inv_borel(q) >> k).q_borel(q)
    }

    /// O(n)
    #[inline]
    pub fn q_integr_divx(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let n = self.coeff.len();
        self.coeff[0] = 0;
        let mut qi = (q * q) % M;
        let qmii = inverse_euclidean::<M>(q - 1);
        let mut a = Vec::with_capacity(n);
        for _ in 2..n {
            a.push(((qi - 1) * qmii) % M);
            qi = (qi * q) % M;
        }
        a = inverses::<M>(&a);
        let mut i = 0;
        for j in 2..n {
            self.coeff[j] *= a[i] as i64;
            self.coeff[j] %= M as i64;
            i += 1;
        }
        self
    }

    /// O(n)
    #[inline]
    pub fn q_integr(self, q: i64) -> Self {
        (self << 1).q_integr_divx(q)
    }

    /// O(n)
    #[inline]
    pub fn q_integr_k(self, k: usize, q: i64) -> Self {
        (self.q_inv_borel(q) << k).q_borel(q)
    }

    /// O(n)
    #[inline]
    pub fn q_inv_borel(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let mut q_fact = 1;
        let mut qi = (q * q) % M;
        let qmii = inverse_euclidean::<M>(q - 1);
        let d = self.deg_or_0();
        self.coeff.iter_mut().take(d + 1).skip(2).for_each(|v| {
            q_fact *= ((qi - 1) * qmii) % M;
            q_fact %= M;
            *v *= q_fact as i64;
            *v %= M as i64;
            qi = (qi * q) % M;
        });
        self
    }

    /// O(n)
    #[inline]
    pub fn q_borel(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let d = self.deg_or_0();
        let mut qi = (q * q) % M;
        let qmii = inverse_euclidean::<M>(q - 1);
        let mut q_fact = 1;
        for _ in 2..=d {
            q_fact *= (qi - 1) * qmii % M;
            q_fact %= M;
            qi = (qi * q) % M;
        }
        q_fact = inverse_euclidean::<M>(q_fact);
        let q_inv = inverse_euclidean::<M>(q);
        self.coeff
            .iter_mut()
            .take(d + 1)
            .skip(1)
            .rev()
            .for_each(|v| {
                qi = (qi * q_inv) % M;
                *v *= q_fact as i64;
                *v %= M as i64;
                q_fact *= (qi - 1) * qmii % M;
                q_fact %= M;
            });
        self
    }

    /// O(n)
    #[inline]
    pub fn inv_q_poch_trans(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let d = self.deg_or_0();
        let mut q_poch = 1;
        let mut qi = q;
        self.coeff.iter_mut().take(d + 1).skip(1).for_each(|v| {
            q_poch *= (1 - qi as i64) % M as i64;
            q_poch %= M as i64;
            *v *= q_poch as i64;
            *v %= M as i64;
            qi = (qi * q) % M;
        });
        self
    }

    /// O(n)
    #[inline]
    pub fn q_poch_trans(mut self, q: i64) -> Self {
        let q = q.rem_euclid(M as i64) as u64;
        let d = self.deg_or_0();
        let mut q_poch = 1;
        let mut qi = q;
        for _ in 1..=d {
            q_poch *= (1 - qi as i64) % M as i64;
            q_poch %= M as i64;
            qi = (qi * q) % M;
        }
        q_poch = inverse_euclidean::<M>(q_poch.rem_euclid(M as i64) as u64) as i64;
        let q_inv = inverse_euclidean::<M>(q);
        let d = self.deg_or_0();
        self.coeff
            .iter_mut()
            .take(d + 1)
            .skip(1)
            .rev()
            .for_each(|v| {
                qi = (qi * q_inv) % M;
                *v *= q_poch;
                *v %= M as i64;
                q_poch *= (1 - qi as i64) % M as i64;
                q_poch %= M as i64;
            });
        self
    }

    /// O(n)
    #[inline]
    pub fn log_1o1mx(n: usize) -> Self {
        Self::new(
            inverses_n_div::<M>(n)
                .into_iter()
                .map(|i| i as i64)
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
            self.coeff[i] *= f1 as i64;
            self.coeff[i] %= M as i64;
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
            (f0, f1) = (f1, f0 + f1 % M as i64);
            self.coeff[i] *= f1;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn euler(n: usize) -> Self {
        (Self::exp_x(n) + Self::exp_ax(-1, n)).inv(n).unwrap() * 2
    }

    /// O(n)
    #[inline]
    pub fn catalan(mut self, n: usize) -> Self {
        let mut a = 1;
        let invs = inverses_n_div::<M>(n + 1);
        for i in 1..n {
            a *= ((((i as u64) << 1) - 1) << 1) * invs[i] % M;
            a %= M;
            self.coeff[i] *= (a * invs[i + 1]) as i64;
            self.coeff[i] %= M as i64;
        }
        self
    }

    /// O(n log n)
    #[inline]
    pub fn catalan_p(self, n: usize) -> Option<Self> {
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
            a *= i as i64;
            a += if i & 1 == 0 { 1 } else { -1 };
            self.coeff[i] *= a;
            self.coeff[i] %= M as i64;
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
            let p_shift = a.clone().shift(-(m as i64)).normalize();
            a = (a * p_shift).normalize();
            if k & 1 == 1 {
                a *= Self::new(vec![-((k - 1) as i64), 1]);
            }
            a = a.normalize();
            i -= 1;
        }
        a
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_unsigned(n: usize) -> Self {
        Self::stirling1(n).n1pkmi(0)
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_k(k: usize, n: usize) -> Self {
        Self::log_1px(n).pow(k, n) * mod_rfact::<M>(k as u64) as i64
    }

    /// O(n log n)
    #[inline]
    pub fn stirling1_unsigned_k(k: usize, n: usize) -> Self {
        Self::log_1o1mx(n).pow(k, n) * mod_rfact::<M>(k as u64) as i64
    }

    /// O(n log n)
    #[inline]
    pub fn stirling2(n: usize) -> Self {
        let mut pws = sieve_complete(
            n + 1,
            1,
            |a, b| a * b % M as i64,
            |p, _| mod_pow_signed::<M>(p as i64, n as u64),
        )
        .0;
        pws[0] = 0;
        let f = Self::new(pws).borel();
        let g = Self::from_elem(1, n + 1).n1pkmi(0).borel();
        (f * g).mod_xn(n + 1)
    }

    /// O(n log n)
    #[inline]
    pub fn stirling2_k(k: usize, n: usize) -> Self {
        (Self::exp_x(n) - 1).pow(k, n) * mod_rfact::<M>(k as u64) as i64
    }

    /// O(n log n)
    #[inline]
    pub fn corr(self, rhs: Self) -> Self {
        rhs.reverse().normalize() * self
    }

    /// O(n log n)
    #[inline]
    pub fn semicorr(self, rhs: Self) -> Self {
        let d = rhs.deg_or_0();
        self.corr(rhs) >> d
    }

    /// O(n)
    #[inline]
    pub fn inv_borel(mut self) -> Self {
        let mut fact = 1;
        let d = self.deg_or_0();
        self.coeff
            .iter_mut()
            .take(d + 1)
            .enumerate()
            .skip(2)
            .for_each(|(i, v)| {
                fact *= i as i64;
                fact %= M as i64;
                *v *= fact;
                *v %= M as i64;
            });
        self
    }

    /// O(n)
    #[inline]
    pub fn borel(mut self) -> Self {
        let mut a = mod_rfact::<M>(self.deg_or_0() as u64);
        let d = self.deg_or_0();
        self.coeff
            .iter_mut()
            .take(d + 1)
            .enumerate()
            .skip(2)
            .rev()
            .for_each(|(i, v)| {
                *v *= a as i64;
                *v %= M as i64;
                a *= i as u64;
                a %= M;
            });
        self
    }

    /// O(n log n)
    #[inline]
    pub fn shift(self, a: i64) -> Self {
        let d = self.deg_or_0();
        self.inv_borel()
            .semicorr(Self::exp_ax(a, d + 1 as usize))
            .borel()
    }

    /// O(n^2)
    pub fn comp_naive(&self, b: &Self, n: usize) -> Self {
        let q = n.isqrt();
        let mut b_k = Vec::with_capacity(q);
        let b_q = b.clone().pow(q, n);
        b_k.push(Self::new(vec![1]));
        for i in 1..q {
            b_k.push((b * &b_k[i - 1]).mod_xn(n).normalize())
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

    // https://judge.yosupo.jp/problem/composition_of_formal_power_series
    // https://codeforces.com/blog/entry/127674
    // https://codeforces.com/blog/entry/128204
    // https://codeforces.com/blog/entry/126124
    pub fn comp() {
        unimplemented!()
    }

    // https://judge.yosupo.jp/problem/compositional_inverse_of_formal_power_series
    // https://codeforces.com/blog/entry/128814
    pub fn comp_inv() -> Self {
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

    /// O(n log n)
    pub fn subset(mut self) -> Self {
        lattice::subset(&mut self.coeff);
        self
    }

    /// O(n log n)
    pub fn subset_inv(mut self) -> Self {
        lattice::subset_inv(&mut self.coeff);
        self
    }

    /// O(n log n)
    pub fn and_conv(self, rhs: Self) -> Self {
        self.subset()
            .normalize()
            .dot(&rhs.subset().normalize())
            .normalize()
            .subset_inv()
    }

    /// O(n log^2 n)
    pub fn subset_conv(mut self, rhs: &Self) -> Self {
        let n = self.len().ilog2() as usize;
        let mut fhat = vec![vec![0; 1 << n]; n + 1];
        let mut ghat = vec![vec![0; 1 << n]; n + 1];
        for m in 0_usize..1 << n {
            fhat[m.count_ones() as usize][m] = self.coeff[m];
            ghat[m.count_ones() as usize][m] = rhs.coeff[m];
        }
        for i in 0..=n {
            lattice::superset(&mut fhat[i]);
            lattice::superset(&mut ghat[i]);
            fhat[i].iter_mut().for_each(|i| *i %= M as i64);
            ghat[i].iter_mut().for_each(|i| *i %= M as i64);
        }
        let mut h = vec![vec![0; 1 << n]; n + 1];
        for i in 0..=n {
            for j in 0..=i {
                h[i].iter_mut()
                    .zip(&fhat[j])
                    .zip(&ghat[i - j])
                    .for_each(|((a, b), c)| *a += b * c % M as i64);
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

    /// O(n log n)
    pub fn superset(mut self) -> Self {
        lattice::superset(&mut self.coeff);
        self
    }

    /// O(n log n)
    pub fn superset_inv(mut self) -> Self {
        lattice::superset_inv(&mut self.coeff);
        self
    }

    /// O(n log n)
    pub fn or_conv(self, rhs: Self) -> Self {
        self.superset()
            .normalize()
            .dot(&rhs.superset().normalize())
            .normalize()
            .superset_inv()
    }

    /// O(n log n)
    pub fn xor(mut self) -> Self {
        lattice::xor(&mut self.coeff);
        self
    }

    /// O(n log n)
    pub fn xor_inv(self) -> Self {
        let n = self.len();
        self.xor() * inverse_euclidean::<M>(n as u64) as i64
    }

    /// O(n log n)
    pub fn xor_conv(self, rhs: Self) -> Self {
        self.xor()
            .normalize()
            .dot(&rhs.xor().normalize())
            .normalize()
            .xor_inv()
    }

    // TODO: min plus convolution
    // https://judge.yosupo.jp/submission/296643
    // https://judge.yosupo.jp/submission/152464
    // https://judge.yosupo.jp/submission/261406
    // https://codeforces.com/blog/entry/98663
    pub fn min_plus() -> Self {
        unimplemented!()
    }

    // TODO: SPS pow proj
    // https://judge.yosupo.jp/submission/244938
    pub fn sps_pow_proj() -> Self {
        unimplemented!()
    }

    // TODO: SPS exp
    // https://judge.yosupo.jp/problem/exp_of_set_power_series
    pub fn sps_exp() {}

    // TODO: SPS comp
    // https://judge.yosupo.jp/submission/140530
    pub fn sps_comp() {}
}

impl<const M: u64> Debug for Poly<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.coeff)?;
        Ok(())
    }
}

impl<const M: u64> PartialEq for Poly<M> {
    fn eq(&self, other: &Self) -> bool {
        self.coeff[..=self.deg_or_0()] == other.coeff[..=other.deg_or_0()]
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

impl<const M: u64> Add<Self> for &Poly<M> {
    type Output = Poly<M>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut s = self.clone();
        s += rhs;
        s
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
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .for_each(|(a, b)| *a += b);
    }
}

impl<const M: u64> Sub<Self> for &Poly<M> {
    type Output = Poly<M>;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut s = self.clone();
        s -= rhs;
        s
    }
}

impl<const M: u64> Sub<Self> for Poly<M> {
    type Output = Poly<M>;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const M: u64> Sub<Poly<M>> for &Poly<M> {
    type Output = Poly<M>;

    fn sub(self, mut rhs: Poly<M>) -> Self::Output {
        rhs.coeff.iter_mut().for_each(|i| *i = -*i);
        rhs += self;
        rhs
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
        self.coeff
            .iter_mut()
            .zip(&rhs.coeff)
            .for_each(|(a, &b)| *a -= b);
    }
}

impl<const M: u64> Mul<Self> for &Poly<M> {
    type Output = Poly<M>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut s = self.clone();
        s *= rhs;
        s
    }
}

impl<const M: u64> Mul<Poly<M>> for &Poly<M> {
    type Output = Poly<M>;

    fn mul(self, mut rhs: Poly<M>) -> Self::Output {
        rhs *= self;
        rhs
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
            let mut res = vec![0i64; n + m - 1];
            for j in 0..m {
                let a = rhs.coeff[j];
                res.iter_mut()
                    .skip(j)
                    .zip(&self.coeff)
                    .for_each(|(i, &j)| *i += a * j % M as i64);
            }
            self.coeff = res;
        } else {
            ntt_conv::<M>(&mut self.coeff, &mut rhs.coeff);
            self.coeff.iter_mut().for_each(|i| {
                *i = i.rem_euclid(M as i64);
            });
        }
    }
}

impl<const M: u64> AddAssign<i64> for Poly<M> {
    fn add_assign(&mut self, rhs: i64) {
        self.coeff[0] += rhs;
    }
}

impl<const M: u64> Add<i64> for Poly<M> {
    type Output = Self;

    fn add(mut self, rhs: i64) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const M: u64> SubAssign<i64> for Poly<M> {
    fn sub_assign(&mut self, rhs: i64) {
        self.coeff[0] -= rhs;
    }
}

impl<const M: u64> Sub<i64> for Poly<M> {
    type Output = Self;

    fn sub(mut self, rhs: i64) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const M: u64> MulAssign<i64> for Poly<M> {
    fn mul_assign(&mut self, rhs: i64) {
        self.coeff.iter_mut().for_each(|i| *i *= rhs);
    }
}

impl<const M: u64> Mul<i64> for Poly<M> {
    type Output = Self;

    fn mul(mut self, rhs: i64) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<const M: u64> Mul<i64> for &Poly<M> {
    type Output = Poly<M>;

    fn mul(self, rhs: i64) -> Self::Output {
        let mut s = self.clone();
        s *= rhs;
        s
    }
}

impl<const M: u64, T, S> Index<T> for Poly<M>
where
    Vec<i64>: Index<T, Output = S>,
{
    type Output = S;

    fn index(&self, index: T) -> &Self::Output {
        &self.coeff[index]
    }
}

impl<const M: u64, T, S> IndexMut<T> for Poly<M>
where
    Vec<i64>: IndexMut<T, Output = S>,
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

// TODO: CDQ convolution
// https://codeforces.com/blog/entry/111399

// TODO: set power series
// https://codeforces.com/blog/entry/92183

#[derive(Clone)]
pub struct Affine<const M: u64> {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

impl<const M: u64> PartialEq for Affine<M> {
    fn eq(&self, other: &Self) -> bool {
        (self.a % M, self.b % M, self.c % M) == (other.a % M, other.b % M, other.c % M)
    }
}

impl<const M: u64> Eq for Affine<M> {}

impl<const M: u64> PartialOrd for Affine<M> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (self.a % M, self.b % M, self.c % M).partial_cmp(&(other.a % M, other.b % M, other.c % M))
    }
}

impl<const M: u64> Ord for Affine<M> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.a % M, self.b % M, self.c % M).cmp(&(other.a % M, other.b % M, other.c % M))
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
