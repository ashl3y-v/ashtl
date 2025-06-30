type B = u64;
const S: usize = B::BITS as usize;
const L: u32 = S.trailing_zeros();

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FirstOne {
    l0: Vec<B>,
    l1: Vec<B>,
    n: usize,
}

impl FirstOne {
    pub fn new(n: usize, init: bool) -> Self {
        let blocks = (n + S - 1) >> L;
        let mut l0 = vec![0; blocks];
        if init {
            for w in &mut l0 {
                *w = B::MAX;
            }
            let tail_bits = n & (S - 1);
            if tail_bits != 0 {
                let mask = (1 << tail_bits) - 1;
                l0[blocks - 1] = mask;
            }
        }
        let summary_blocks = (blocks + S - 1) >> L;
        let mut l1 = vec![0; summary_blocks];
        if init {
            for (i, slot) in l1.iter_mut().enumerate() {
                let mut w = B::MAX;
                let max_chunk = ((i + 1) << L).min(blocks);
                let valid = max_chunk - (i << L);
                if valid < S {
                    w = (1 << valid) - 1;
                }
                *slot = w;
            }
        }
        Self { l0, l1, n }
    }

    pub fn set(&mut self, i: usize, v: bool) {
        let (b, o) = (i >> L, i & (S - 1));
        let was_nz = self.l0[b] != 0;
        if v {
            self.l0[b] |= 1 << o;
        } else {
            self.l0[b] &= !(1 << o);
        }
        let now_nz = self.l0[b] != 0;
        if was_nz != now_nz {
            let (sbi, sbo) = (b >> L, b & (S - 1));
            if now_nz {
                self.l1[sbi] |= 1 << sbo;
            } else {
                self.l1[sbi] &= !(1 << sbo);
            }
        }
    }

    pub fn first_one(&self) -> Option<usize> {
        for (sbi, &word1) in self.l1.iter().enumerate() {
            if word1 != 0 {
                let sbo = word1.trailing_zeros() as usize;
                let chunk_idx = (sbi << L) + sbo;
                let word0 = self.l0[chunk_idx];
                let bo = word0.trailing_zeros() as usize;
                let pos = (chunk_idx << L) + bo;
                return if pos < self.n { Some(pos) } else { None };
            }
        }
        None
    }

    pub fn resize(&mut self, n: usize, init: bool) {
        if n <= self.n {
            return;
        }
        let old_n = self.n;
        let old_blocks = (old_n + (S - 1)) >> L;
        let new_blocks = (n + (S - 1)) >> L;
        if new_blocks == old_blocks && old_blocks > 0 {
            let b = old_blocks - 1;
            let old_off = old_n & (S - 1);
            let new_off = n & (S - 1);
            let mask = if new_off == 0 {
                B::MAX.wrapping_shl(old_off as u32)
            } else {
                ((1 << new_off) - 1) ^ ((1 << old_off) - 1)
            };
            if init {
                self.l0[b] |= mask;
            } else {
                self.l0[b] &= !mask;
            }
        } else {
            if old_blocks > 0 {
                let b = old_blocks - 1;
                let old_off = old_n & (S - 1);
                if init {
                    self.l0[b] |= B::MAX.wrapping_shl(old_off as u32);
                } else {
                    self.l0[b] &= (1 << old_off) - 1;
                }
            }
            for _ in old_blocks..(new_blocks.saturating_sub(1)) {
                self.l0.push(if init { B::MAX } else { 0 });
            }
            let tail_bits = n & (S - 1);
            let last_word = if tail_bits == 0 {
                if init { B::MAX } else { 0 }
            } else {
                let mask = (1 << tail_bits) - 1;
                if init { mask } else { 0 }
            };
            self.l0.push(last_word);
        }
        self.n = n;
        let summary_blocks = (new_blocks + (S - 1)) >> L;
        let mut new_l1 = vec![0; summary_blocks];
        for block_idx in 0..new_blocks {
            if self.l0[block_idx] != 0 {
                let sbi = block_idx >> L;
                let sbo = block_idx & (S - 1);
                new_l1[sbi] |= 1 << sbo;
            }
        }
        self.l1 = new_l1;
    }

    pub fn len(&self) -> usize {
        self.n
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::FirstOne;

    /// Helper: collect all positions of 1-bits by scanning a Vec<bool>
    fn brute_first_one(bits: &[bool]) -> Option<usize> {
        bits.iter().position(|&b| b)
    }

    #[test]
    fn test_new_all_false() {
        let n = 100;
        let fo = FirstOne::new(n, false);
        assert_eq!(fo.first_one(), None, "all-false init should yield no 1");
    }

    #[test]
    fn test_new_all_true() {
        let n = 100;
        let fo = FirstOne::new(n, true);
        // first_one should be 0
        assert_eq!(fo.first_one(), Some(0));
    }

    #[test]
    fn test_single_bit() {
        let n = 128;
        let mut fo = FirstOne::new(n, false);
        // set each bit one at a time and check
        for i in 0..n {
            fo.set(i, true);
            assert_eq!(
                fo.first_one(),
                Some(i),
                "after setting bit {}, first_one should be 0",
                i
            );
            // clear it again
            fo.set(i, false);
            assert_eq!(
                fo.first_one(),
                None,
                "after clearing bit {}, should be none",
                i
            );
        }
    }

    #[test]
    fn test_edge_bits() {
        let n = 130;
        let mut fo = FirstOne::new(n, false);
        // first and last
        fo.set(0, true);
        assert_eq!(fo.first_one(), Some(0));
        fo.set(0, false);
        fo.set(n - 1, true);
        assert_eq!(fo.first_one(), Some(n - 1));
        fo.set(n - 1, false);
        assert_eq!(fo.first_one(), None);
    }

    #[test]
    fn test_multiple_bits() {
        let n = 200;
        let mut fo = FirstOne::new(n, false);
        // set a few bits out of order
        for &i in &[37, 5, 150, 99] {
            fo.set(i, true);
        }
        assert_eq!(fo.first_one(), Some(5));
        // clear the smallest
        fo.set(5, false);
        assert_eq!(fo.first_one(), Some(37));
        // clear all
        for &i in &[37, 150, 99] {
            fo.set(i, false);
        }
        assert_eq!(fo.first_one(), None);
    }

    #[test]
    fn test_overwrite_and_toggle() {
        let n = 67;
        let mut fo = FirstOne::new(n, true);
        // clear bit 10, then set it repeatedly
        fo.set(10, false);
        assert_eq!(fo.first_one(), Some(0));
        fo.set(0, false);
        assert_eq!(fo.first_one(), Some(1));
        fo.set(1, false);
        assert_eq!(fo.first_one(), Some(2));
        // now toggle bit 10 back on
        fo.set(10, true);
        assert_eq!(fo.first_one(), Some(2));
    }

    #[test]
    fn test_non_multiple_of_64() {
        let n = 70; // crosses a partial l0 block
        let mut fo = FirstOne::new(n, false);
        assert_eq!(fo.first_one(), None);
        fo.set(69, true);
        assert_eq!(fo.first_one(), Some(69));
        fo.set(0, true);
        assert_eq!(fo.first_one(), Some(0));
    }

    #[test]
    fn test_random_small() {
        let n = 300;
        let mut rng = rand::rng();
        let mut bits = vec![false; n];
        let mut fo = FirstOne::new(n, false);
        for _ in 0..1000 {
            let i = rng.random_range(0..n);
            let v = rng.random();
            bits[i] = v;
            fo.set(i, v);
            assert_eq!(fo.first_one(), brute_first_one(&bits));
        }
    }

    #[test]
    fn test_random_large() {
        let n = 10_000;
        use rand::Rng;
        let mut rng = rand::rng();
        let mut bits = vec![false; n];
        let mut fo = FirstOne::new(n, false);
        for _ in 0..5_000 {
            let i = rng.random_range(0..n);
            let v = rng.random();
            bits[i] = v;
            fo.set(i, v);
        }
        // do one full scan check
        let expect = brute_first_one(&bits);
        assert_eq!(fo.first_one(), expect);
    }

    #[test]
    fn test_resize_noop() {
        let mut fo = FirstOne::new(50, false);
        let before = fo.first_one();
        fo.resize(30, true); // smaller than current, should do nothing
        assert_eq!(fo.first_one(), before);
    }

    #[test]
    fn test_resize_same_block() {
        // initial length 10, all false; resize to 20 (still in block 0)
        let mut fo = FirstOne::new(10, false);
        fo.set(3, true);
        assert_eq!(fo.first_one(), Some(3));
        fo.resize(20, true);
        // existing bit still at 3
        assert_eq!(fo.first_one(), Some(3));
        // bits 10..20 should all be 1
        for i in 10..20 {
            fo.set(i, false);
            assert_eq!(
                fo.first_one(),
                Some(3),
                "clearing position {} should not affect first_one",
                i
            );
        }
    }

    #[test]
    fn test_resize_multi_block() {
        // initial length 70 (blocks 0 and 1 partial), all false
        let mut fo = FirstOne::new(70, false);
        assert_eq!(fo.first_one(), None);
        // resize to 200, init=true
        fo.resize(200, true);
        // bits 0..70 still false
        for _ in 0..70 {
            assert_eq!(
                fo.first_one(),
                Some(70),
                "first_one should now be 70 after resizing"
            );
        }
        // bits 70..200 should all be true
        for _ in 70..200 {
            assert_eq!(fo.first_one(), Some(70));
        }
    }

    #[test]
    fn test_resize_preserves_and_init_false() {
        // initial length 100, init=true
        let mut fo = FirstOne::new(100, true);
        // clear bit 5 and bit 50
        fo.set(5, false);
        fo.set(50, false);
        assert_eq!(fo.first_one(), Some(0));
        // resize to 150 with init=false
        fo.resize(150, false);
        // bits 0..100 retain their values
        assert_eq!(fo.first_one(), Some(0));
        fo.set(0, false);
        assert_eq!(fo.first_one(), Some(1));
        // bits 100..150 are all false, so once you clear down into that range, you get None
        for i in 1..100 {
            fo.set(i, false);
        }
        assert_eq!(fo.first_one(), None);
    }

    #[test]
    fn test_resize_random() {
        let mut rng = rand::rng();
        let mut bits = Vec::new();
        let initial_n = 500;
        // random initial bits
        for _ in 0..initial_n {
            bits.push(rng.random());
        }
        let mut fo = FirstOne::new(initial_n, false);
        for (i, &b) in bits.iter().enumerate() {
            fo.set(i, b);
        }

        // resize to a larger size with random init value
        let new_n = 800;
        let init = rng.random();
        fo.resize(new_n, init);
        bits.resize(new_n, init);

        // compare brute vs structure first_one
        let brute = bits.iter().position(|&b| b);
        assert_eq!(fo.first_one(), brute);
    }
}
