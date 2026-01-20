use std::{
    fmt::Debug,
    ops::{Add, AddAssign, BitAnd, BitAndAssign, Div, Index, IndexMut, Range, Rem},
};

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

impl Debug for XorBasis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..B::BITS as usize {
            writeln!(f, "{:128b}", self.basis[i])?;
        }
        Ok(())
    }
}

impl Index<usize> for XorBasis {
    type Output = B;

    fn index(&self, index: usize) -> &Self::Output {
        &self.basis[index]
    }
}

impl IndexMut<usize> for XorBasis {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.basis[index]
    }
}

impl Index<Range<usize>> for XorBasis {
    type Output = [B];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self.basis[index]
    }
}

impl IndexMut<Range<usize>> for XorBasis {
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        &mut self.basis[index]
    }
}

impl AddAssign<B> for XorBasis {
    fn add_assign(&mut self, mut m: B) {
        for i in (0..B::BITS as usize).rev() {
            if m & 1 << i == 0 {
                continue;
            }
            if self.mask & 1 << i == 0 {
                self.basis[i] = m;
                self.mask |= 1 << i;
            }
            m ^= self.basis[i];
        }
    }
}

impl AddAssign<Self> for XorBasis {
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..B::BITS as usize {
            if rhs.mask & (1 << i) != 0 {
                *self += rhs.basis[i];
            }
        }
    }
}

impl AddAssign<&Self> for XorBasis {
    fn add_assign(&mut self, rhs: &Self) {
        for i in 0..B::BITS as usize {
            if rhs.mask & (1 << i) != 0 {
                *self += rhs.basis[i];
            }
        }
    }
}

impl Add<Self> for XorBasis {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl Add<&Self> for XorBasis {
    type Output = Self;

    fn add(mut self, rhs: &Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl BitAnd<B> for &XorBasis {
    type Output = bool;

    fn bitand(self, rhs: B) -> Self::Output {
        let mut m = rhs;
        for i in (0..B::BITS as usize).rev() {
            if m & 1 << i == 0 {
                continue;
            }
            if self.mask & 1 << i == 0 {
                return false;
            }
            m ^= self.basis[i];
        }
        true
    }
}

impl BitAnd<&XorBasis> for B {
    type Output = bool;

    fn bitand(self, rhs: &XorBasis) -> Self::Output {
        rhs & self
    }
}

impl BitAnd<Self> for &XorBasis {
    type Output = XorBasis;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut extended = XorBasis::new();
        let hlf = (B::BITS >> 1) as usize;
        for i in 0..hlf {
            if self.mask & (1 << i) != 0 {
                extended += self.basis[i] | (self.basis[i] << hlf);
            }
        }
        for i in 0..hlf {
            if rhs.mask & (1 << i) != 0 {
                extended += rhs.basis[i] << hlf;
            }
        }
        extended.eliminate();
        let mut result = XorBasis::new();
        for i in 0..B::BITS as usize {
            if extended.mask & (1 << i) != 0 {
                let val = extended.basis[i];
                if val < (1 << hlf) {
                    result += val;
                }
            }
        }
        result
    }
}

impl BitAnd<&Self> for XorBasis {
    type Output = Self;

    fn bitand(self, rhs: &Self) -> Self::Output {
        &self & rhs
    }
}

impl BitAnd<Self> for XorBasis {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        &self & &rhs
    }
}

impl BitAndAssign<&Self> for XorBasis {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = &*self & rhs;
    }
}

impl BitAndAssign<Self> for XorBasis {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = &*self & &rhs;
    }
}

impl Div<&XorBasis> for B {
    type Output = B;

    fn div(self, rhs: &XorBasis) -> Self::Output {
        let mut m = self;
        let mut r = 0;
        for i in (0..B::BITS as usize).rev() {
            if m & 1 << i == 0 {
                continue;
            }
            if rhs.mask & 1 << i == 0 {
                return 0;
            }
            m ^= rhs.basis[i];
            r ^= 1 << i;
        }
        r
    }
}

impl Rem<&XorBasis> for B {
    type Output = B;

    fn rem(self, rhs: &XorBasis) -> Self::Output {
        let mut m = self;
        for i in (0..B::BITS as usize).rev() {
            if m & 1 << i != 0 && rhs.mask & 1 << i != 0 {
                m ^= rhs.basis[i];
            }
        }
        m
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_new_and_basic_properties() {
        let b = XorBasis::new();
        assert_eq!(b.size(), 0);
        assert_eq!(b.span_size(), 1);
        // ker_size(at) = 2^(at - size)
        assert_eq!(b.ker_size(5), 1 << 5);
    }

    #[test]
    fn test_insert_and_size() {
        let mut b = XorBasis::new();
        // inserting zero should do nothing
        b += 0;
        assert_eq!(b.size(), 0);

        // insert two independent vectors
        b += 1; // 0b1
        assert_eq!(b.size(), 1);
        b += 2; // 0b10
        assert_eq!(b.size(), 2);

        // insert a combination (3 = 1^2) should not increase size
        b += 3;
        assert_eq!(b.size(), 2);
    }

    #[test]
    fn test_membership_and_remainder() {
        let mut b = XorBasis::new();
        b += 1;
        b += 2;
        // span = {0,1,2,3}
        assert!((&b & 3u128), "3 should be in span");
        assert!(3u128 & &b, "symmetric BitAnd should work");
        assert!(!(&b & 4u128), "4 is not in span");

        // remainder of anything in the span must be 0
        for &v in &[0u128, 1, 2, 3] {
            let r = v % &b;
            assert_eq!(r, 0, "remainder of {} in span must be 0", v);
        }
        // remainder of something outside may be nonzero
        let r5 = 5u128 % &b; // 5 = 101₂, removes bits 2/1/0 if present
        assert!(r5 != 0, "5 is not in the span, remainder = {}", r5);
    }

    #[test]
    fn test_division_representation() {
        let mut b = XorBasis::new();
        // build basis of {1,2,4}
        b += 1;
        b += 2;
        b += 4;
        // for each element in the span, compute its representation r = v / b
        // and then reconstruct sum_{i bit of r} basis[i] == v
        for v in 0u128..8 {
            assert!((&b & v), "{} should be in the span", v);
            let r = v / &b;
            // reconstruct
            let mut sum = 0;
            for i in 0..128 {
                if (r >> i) & 1 == 1 {
                    sum ^= b.basis[i];
                }
            }
            assert_eq!(sum, v, "div representation failed for v={}", v);
        }
    }

    #[test]
    fn test_eliminate_and_pivots() {
        let mut b = XorBasis::new();
        // insert some random vectors with overlapping bits
        for &v in &[0b1101, 0b1011, 0b0111] {
            b += v;
        }
        // now eliminate into reduced echelon form
        b.eliminate();
        // ensure that for each pivot i, no higher-index pivot has a 1-bit at i
        let pivots: Vec<usize> = (0..128).filter(|&i| (b.mask >> i) & 1 == 1).collect();
        for &i in &pivots {
            for &j in pivots.iter().filter(|&&j| j > i) {
                assert_eq!(
                    (b.basis[j] >> i) & 1,
                    0,
                    "pivot at {} not eliminated from basis[{}]={:b}",
                    i,
                    j,
                    b.basis[j]
                );
            }
        }
    }

    #[test]
    fn test_max_span_bruteforce() {
        let mut b = XorBasis::new();
        for &v in &[3u128, 5, 9] {
            b += v;
        }
        // brute-force all 2^size combinations
        let mut all = Vec::new();
        let pivots: Vec<u128> = (0..128)
            .filter_map(|i| {
                if (b.mask >> i) & 1 == 1 {
                    Some(b.basis[i])
                } else {
                    None
                }
            })
            .collect();
        let sz = pivots.len();
        for mask in 0..(1 << sz) {
            let mut x = 0;
            for j in 0..sz {
                if (mask >> j) & 1 == 1 {
                    x ^= pivots[j];
                }
            }
            all.push(x);
        }
        let expected = *all.iter().max().unwrap();
        assert_eq!(b.max_span(), expected);
    }

    #[test]
    fn test_kth_span_covers_all() {
        let mut b = XorBasis::new();
        for &v in &[7u128, 11, 13] {
            b += v;
        }
        let total = b.span_size();
        let mut seen = HashSet::new();
        for k in 0..total {
            seen.insert(b.kth_span(k));
        }
        // brute set
        let mut brute = HashSet::new();
        let pivots: Vec<u128> = (0..128)
            .filter_map(|i| {
                if (b.mask >> i) & 1 == 1 {
                    Some(b.basis[i])
                } else {
                    None
                }
            })
            .collect();
        let sz = pivots.len();
        for mask in 0..(1 << sz) {
            let mut x = 0;
            for j in 0..sz {
                if (mask >> j) & 1 == 1 {
                    x ^= pivots[j];
                }
            }
            brute.insert(x);
        }
        println!("{:?}", b.span());
        assert_eq!(seen, brute, "kth_span should enumerate entire span");
    }

    #[test]
    fn test_index_and_range() {
        let mut b = XorBasis::new();
        // manually poke basis array
        for i in 0..10 {
            b.basis[i] = i as u128;
        }
        // single-index
        assert_eq!(b[3], 3);
        // mutable index
        {
            let slot = &mut b[4];
            *slot = 99;
        }
        assert_eq!(b[4], 99);

        // range indexing
        let slice: &[u128] = &b[2..6];
        assert_eq!(slice, &[2, 3, 99, 5]);
        // mutable range
        {
            let slice_mut: &mut [u128] = &mut b[6..9];
            slice_mut[0] = 42;
            slice_mut[1] = 43;
            slice_mut[2] = 44;
        }
        assert_eq!(&b.basis[6..9], &[42, 43, 44]);
    }
}
