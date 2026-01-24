use std::ops::Index;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitVec {
    pub nbits: usize,
    pub storage: Vec<u64>,
}

impl BitVec {
    const B: usize = 64;

    pub fn new(n: usize, value: bool) -> Self {
        let num_words = (n + Self::B - 1) / Self::B;
        let fill_pattern = if value { !0 } else { 0 };
        let mut storage = vec![fill_pattern; num_words];
        if value {
            let rem = n % Self::B;
            if rem != 0 {
                if let Some(last) = storage.last_mut() {
                    *last &= (1 << rem) - 1;
                }
            }
        }
        Self { nbits: n, storage }
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            nbits: 0,
            storage: Vec::with_capacity((n + Self::B - 1) / Self::B),
        }
    }

    pub fn from_fn<F>(n: usize, mut f: F) -> Self
    where
        F: FnMut(usize) -> bool,
    {
        let mut bv = Self::new(n, false);
        for i in 0..n {
            if f(i) {
                bv.set(i, true);
            }
        }
        bv
    }

    pub fn len(&self) -> usize {
        self.nbits
    }

    pub fn is_empty(&self) -> bool {
        self.nbits == 0
    }

    /// O(1)
    pub fn get(&self, i: usize) -> bool {
        let word = i / Self::B;
        let bit = i % Self::B;
        (self.storage[word] & (1 << bit)) != 0
    }

    /// O(1)
    pub fn set(&mut self, i: usize, value: bool) {
        let word = i / Self::B;
        let bit = i % Self::B;
        if value {
            self.storage[word] |= 1 << bit;
        } else {
            self.storage[word] &= !(1 << bit);
        }
    }

    /// O(1)
    pub fn push(&mut self, value: bool) {
        let bit = self.nbits % Self::B;
        if bit == 0 {
            self.storage.push(0);
        }
        if value {
            let last_idx = self.storage.len() - 1;
            self.storage[last_idx] |= 1 << bit;
        }
        self.nbits += 1;
    }

    /// O(1)
    pub fn pop(&mut self) -> Option<bool> {
        if self.nbits == 0 {
            return None;
        }
        self.nbits -= 1;
        let result = self.get(self.nbits);
        if self.nbits % Self::B == 0 {
            self.storage.pop();
        } else {
            let word = self.nbits / Self::B;
            let bit = self.nbits % Self::B;
            self.storage[word] &= !(1 << bit);
        }
        Some(result)
    }

    pub fn iter(&self) -> BitVecIter<'_> {
        BitVecIter { bv: self, pos: 0 }
    }

    pub fn clear(&mut self) {
        self.storage.fill(0);
    }

    pub fn negate(&mut self) {
        for word in &mut self.storage {
            *word = !*word;
        }
        self.clean_excess_bits();
    }

    fn clean_excess_bits(&mut self) {
        let rem = self.nbits % Self::B;
        if rem != 0 {
            if let Some(last) = self.storage.last_mut() {
                *last &= (1 << rem) - 1;
            }
        }
    }
}

impl Index<usize> for BitVec {
    type Output = bool;

    fn index(&self, i: usize) -> &Self::Output {
        if self.get(i) { &true } else { &false }
    }
}

pub struct BitVecIter<'a> {
    bv: &'a BitVec,
    pos: usize,
}

impl<'a> Iterator for BitVecIter<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.bv.nbits {
            let bit = self.bv.get(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct PrefBitVec {
    pub bv: BitVec,
    pub block_rank: Vec<usize>,
}

impl PrefBitVec {
    pub fn new(bv: BitVec) -> Self {
        let mut block_rank = Vec::with_capacity(bv.storage.len() + 1);
        let mut count = 0;
        block_rank.push(0);
        for &w in &bv.storage {
            count += w.count_ones() as usize;
            block_rank.push(count);
        }
        Self { bv, block_rank }
    }

    /// O(1)
    pub fn rank(&self, i: usize) -> usize {
        if i == 0 {
            return 0;
        }
        let word_idx = i / BitVec::B;
        let bit_idx = i % BitVec::B;
        let mut r = self.block_rank[word_idx];
        if bit_idx > 0 {
            let mask = (1u64 << bit_idx) - 1;
            r += (self.bv.storage[word_idx] & mask).count_ones() as usize;
        }
        r
    }

    /// O(1)
    pub fn count(&self) -> usize {
        *self.block_rank.last().unwrap_or(&0)
    }
}
