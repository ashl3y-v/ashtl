/// O(log m)
pub fn floor_sum_linear(l: i64, r: i64, mut a: i64, mut b: i64, mut m: i64) -> i128 {
    let mut res: i128 = 0;
    b += l * a;
    let mut n = r - l;
    if b < 0 {
        let k = (-b + m - 1) / m;
        b += k * m;
        res -= (n as i128) * (k as i128);
    }
    while n > 0 {
        let q = a / m;
        a %= m;
        res += (n as i128) * ((n - 1) as i128) / 2 * (q as i128);
        if b >= m {
            let q_b = b / m;
            b %= m;
            res += (n as i128) * (q_b as i128);
        }
        let y_max = (a as i128) * (n as i128) + (b as i128);
        n = (y_max / (m as i128)) as i64;
        b = (y_max % (m as i128)) as i64;
        std::mem::swap(&mut a, &mut m);
    }
    res
}

use crate::alg::ops::{inverses_n_div, mod_pow_signed};

pub struct FloorPowerSum<const M: u64> {
    limit: usize,
    ncr: Vec<Vec<i64>>,
    faul: Vec<Vec<i64>>,
    pub table: Vec<i64>,
}

impl<const M: u64> FloorPowerSum<M> {
    /// O(k^2)
    pub fn new(k: usize) -> Self {
        let limit = k + 2;
        let m_i64 = M as i64;
        let mut ncr = vec![vec![0; limit + 1]; limit + 1];
        for i in 0..=limit {
            ncr[i][0] = 1;
            for j in 1..=i {
                ncr[i][j] = ncr[i - 1][j - 1] + ncr[i - 1][j];
                if ncr[i][j] >= m_i64 {
                    ncr[i][j] -= m_i64;
                }
            }
        }
        let inv = inverses_n_div::<M>(limit + 1)
            .into_iter()
            .map(|a| a as i64)
            .collect::<Vec<_>>();
        let mut bernoulli = vec![0; limit];
        bernoulli[0] = 1;
        for i in 1..limit {
            let mut sum = 0;
            for k in 0..i {
                let term = (ncr[i + 1][k] * bernoulli[k]) % m_i64;
                sum = (sum + term) % m_i64;
            }
            bernoulli[i] = (sum * (m_i64 - inv[i + 1])) % m_i64;
        }
        let mut faul = vec![vec![0; limit + 1]; limit];
        for k in 0..limit {
            let inv_k1 = inv[k + 1];
            for j in 0..=k {
                let p = k + 1 - j;
                let comb = ncr[k + 1][j];
                let b_val = bernoulli[j];
                let coeff = (comb * b_val) % m_i64;
                let coeff = (coeff * inv_k1) % m_i64;
                faul[k][p] = coeff;
            }
        }
        Self {
            limit,
            ncr,
            faul,
            table: vec![],
        }
    }

    #[inline]
    fn sum_pow(&self, n: i64, k: usize) -> i64 {
        let m_i64 = M as i64;
        if k == 0 {
            return (n + 1) % m_i64;
        }
        let x = (n + 1) % m_i64;
        let mut ans = 0;
        let mut x_pow = x;
        for p in 1..=k + 1 {
            let c = self.faul[k][p];
            if c != 0 {
                ans = (ans + c * x_pow) % m_i64;
            }
            x_pow = (x_pow * x) % m_i64;
        }
        ans
    }

    pub fn calc(&mut self, n: i64, a: i64, b: i64, c: i64) {
        self.table = self.rec(n, a, b, c);
    }

    pub fn query(&self, k1: usize, k2: usize) -> i64 {
        self.table[k1 * self.limit + k2]
    }

    /// O(k^4 log c)
    fn rec(&self, n: i64, a: i64, b: i64, c: i64) -> Vec<i64> {
        let size = self.limit;
        let m_i64 = M as i64;
        let mut res = vec![0; size * size];
        if a == 0 {
            let floor_val = (b / c) % m_i64;
            let mut f_pow = 1;
            for k_b in 0..size {
                for k_a in 0..(size - k_b) {
                    let s_pow = self.sum_pow(n, k_a);
                    res[k_a * size + k_b] = (s_pow * f_pow) % m_i64;
                }
                f_pow = (f_pow * floor_val) % m_i64;
            }
            return res;
        }
        if a >= c || b >= c {
            let new_a = a % c;
            let new_b = b % c;
            let factor_a = (a / c) % m_i64;
            let factor_b = (b / c) % m_i64;
            let prev = self.rec(n, new_a, new_b, c);
            for k_a in 0..size {
                res[k_a * size + 0] = self.sum_pow(n, k_a);
                for k_b in 1..(size - k_a) {
                    let mut term_sum = 0;
                    for y in 0..=k_b {
                        let rem = k_b - y;
                        let ncr_y = self.ncr[k_b][y];
                        let mut term_val = 0;
                        for z in 0..=rem {
                            let coeff_z = self.ncr[rem][z];
                            let f_a_pow = mod_pow_signed::<M>(factor_a, z as u64);
                            let f_b_pow = mod_pow_signed::<M>(factor_b, (rem - z) as u64);
                            let combined_coeff = (coeff_z * ((f_a_pow * f_b_pow) % m_i64)) % m_i64;
                            let rec = prev[(k_a + z) * size + y];
                            term_val = (term_val + combined_coeff * rec) % m_i64;
                        }
                        let total_term = (ncr_y * term_val) % m_i64;
                        term_sum = (term_sum + total_term) % m_i64;
                    }
                    res[k_a * size + k_b] = term_sum;
                }
            }
            return res;
        }
        let m = (a * n + b) / c;
        if m == 0 {
            for k_a in 0..size {
                res[k_a * size + 0] = self.sum_pow(n, k_a);
            }
            return res;
        }
        let prev = self.rec(m - 1, c, c - b - 1, a);
        let mut psum_m = vec![0; size];
        for i in 0..size {
            psum_m[i] = self.sum_pow(m - 1, i);
        }
        for k_a in 0..size {
            res[k_a * size + 0] = self.sum_pow(n, k_a);
            let mut integrated = vec![0; size];
            let max_j = (k_a + 1).min(size - 1);
            for j in 1..=max_j {
                let coef = self.faul[k_a][j];
                if coef == 0 {
                    continue;
                }
                for i in 0..size {
                    let term = (coef * prev[i * size + j]) % m_i64;
                    integrated[i] = (integrated[i] + term) % m_i64;
                }
            }
            for i in 0..size {
                integrated[i] = (integrated[i] + prev[i * size + k_a]) % m_i64;
            }
            for k_b in 1..(size - k_a) {
                let mut term2_acc = 0;
                for i in 0..k_b {
                    let coef = self.ncr[k_b][i];
                    let t1 = (coef * psum_m[i]) % m_i64;
                    let t1 = (t1 * res[k_a * size + 0]) % m_i64;
                    let t2 = (coef * integrated[i]) % m_i64;
                    let diff = (t1 - t2 + m_i64) % m_i64;
                    term2_acc = (term2_acc + diff) % m_i64;
                }
                res[k_a * size + k_b] = term2_acc;
            }
        }
        res
    }
}
