use crate::ds::bit_vec::{BitVec, PrefBitVec};

pub struct Wavelet {
    ls: Vec<PrefBitVec>,
    b: usize,
}

impl Wavelet {
    /// O(n log σ)
    pub fn new(mut a: Vec<u64>, b: usize) -> Self {
        let mut ls = vec![PrefBitVec::new(BitVec::new(0, false)); b];
        for b in (0..b).rev() {
            let mut a0 = Vec::with_capacity(a.len());
            let mut a1 = Vec::with_capacity(a.len());
            let mut bv = BitVec::with_capacity(a.len());
            for &x in &a {
                if (x & (1 << b)) != 0 {
                    bv.push(false);
                    a1.push(x);
                } else {
                    bv.push(true);
                    a0.push(x);
                }
            }
            ls[b] = PrefBitVec::new(bv);
            a.clear();
            a.extend(a0);
            a.extend(a1);
        }
        Wavelet { ls, b }
    }

    /// O(log σ)
    pub fn kth(&self, mut l: usize, mut r: usize, mut k: usize) -> u64 {
        let mut ans = 0;
        for b in (0..self.b).rev() {
            let pl = self.ls[b].rank(l);
            let pr = self.ls[b].rank(r);
            let n_l = pr - pl;
            if k < n_l {
                l = pl;
                r = pr;
            } else {
                let t = self.ls[b].count();
                k -= n_l;
                l = l - pl + t;
                r = r - pr + t;
                ans |= 1 << b;
            }
        }
        ans
    }

    /// O(log σ)
    pub fn rank(&self, mut k: usize, x: u64) -> usize {
        if (x >> self.b) > 0 {
            return 0;
        }
        let mut l = 0;
        for b in (0..self.b).rev() {
            let pl = self.ls[b].rank(l);
            let pr = self.ls[b].rank(k);
            if (x >> b) & 1 == 0 {
                l = pl;
                k = pr;
            } else {
                let t = self.ls[b].count();
                l = l - pl + t;
                k = k - pr + t;
            }
        }
        k - l
    }

    /// O(log σ)
    pub fn range_freq(&self, mut l: usize, mut r: usize, ub: u64) -> usize {
        if (ub >> self.b) > 0 {
            return r - l;
        }
        let mut ans = 0;
        for b in (0..self.b).rev() {
            let pl = self.ls[b].rank(l);
            let pr = self.ls[b].rank(r);
            if (ub >> b) & 1 == 0 {
                l = pl;
                r = pr;
            } else {
                let t = self.ls[b].count();
                ans += pr - pl;
                l = l - pl + t;
                r = r - pr + t;
            }
        }
        ans
    }

    /// O(log σ)
    pub fn range_freq_range(&self, l: usize, r: usize, lb: u64, ub: u64) -> usize {
        if lb >= ub {
            return 0;
        }
        self.range_freq(l, r, ub) - self.range_freq(l, r, lb)
    }

    /// O(log n log σ)
    pub fn select(&self, k: usize, x: u64) -> usize {
        let mut lo = 0;
        let mut hi = self.ls[0].bv.len();
        if self.rank(hi, x) <= k {
            return hi;
        }
        while lo < hi {
            let m = lo.midpoint(hi);
            if self.rank(m + 1, x) <= k {
                lo = m + 1;
            } else {
                hi = m;
            }
        }
        lo
    }
}

// TODO: dynamic wavelet matrix
// https://blog.niuez.net/cp-cpp-library/data_structures/wavelet_matrix/dynamic_wavelet_matrix.html
