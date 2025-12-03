use std::ops::Index;

pub struct RollingPoly<const M: u64> {
    pub pows: Vec<u64>,
}

impl<const M: u64> RollingPoly<M> {
    pub fn new() -> Self {
        Self { pows: Vec::new() }
    }

    pub fn extend(&mut self, n: usize) {
        let p = 263;
        let mut l = self.pows.len();
        if l == 0 {
            self.pows.push(1);
            l += 1;
        }
        if l < n {
            self.pows.resize(n, 0);
            for i in l - 1..n - 1 {
                self.pows[i + 1] = self.pows[i] * p % M;
            }
        }
    }

    pub fn eval(s: &str) -> u64 {
        let p = 263;
        s.bytes().fold(0, |hash, c| (hash * p + c as u64 + 1) % M)
    }

    pub fn prefixes(s: &str) -> Vec<u64> {
        let p = 263;
        let mut hashes = Vec::with_capacity(s.len() + 1);
        hashes.push(0);
        let mut h = 0;
        for c in s.bytes() {
            h = (h * p + (c + 1) as u64) % M;
            hashes.push(h);
        }
        hashes
    }

    pub fn query(&mut self, p: &[u64], l: usize, r: usize) -> u64 {
        self.extend(r - l + 1);
        M - (p[l] * self.pows[r - l] + M - p[r]) % M
    }

    pub fn combine(&mut self, h1: u64, h2: u64, h2_len: usize) -> u64 {
        self.extend(h2_len + 1);
        (h1 * self.pows[h2_len] + h2) % M
    }

    /// O(log n)
    pub fn lcp(
        &mut self,
        l0: usize,
        r0: usize,
        l1: usize,
        r1: usize,
        p0: &[u64],
        p1: &[u64],
    ) -> usize {
        let len = (r0 - l0).min(r1 - l1);
        let (mut l, mut r) = (0, len + 1);
        while r - l > 1 {
            let m = l + (r - l >> 1);
            if self.query(p0, l0, l0 + m) == self.query(p1, l1, l1 + m) {
                l = m;
            } else {
                r = m;
            }
        }
        l
    }
}

impl<const M: u64> Index<usize> for RollingPoly<M> {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        &self.pows[index]
    }
}

pub fn hash_occurrences<const M: u64>(s: &str, t: &str) -> impl Iterator<Item = usize> {
    let mut h = RollingPoly::<M>::new();
    let (n, m) = (s.len(), t.len());
    h.extend(n + 1);
    let h_s = RollingPoly::<M>::eval(&s);
    let h_t = RollingPoly::<M>::prefixes(&t);
    (0..m + 1 - n).filter(move |&i| h.query(&h_t, i, i + n) == h_s)
}
