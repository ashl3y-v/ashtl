use std::ops::Index;

#[derive(Debug, Clone, PartialEq)]
pub struct BitVec {
    pub storage: Vec<u32>,
    pub len: usize,
}

impl BitVec {
    pub fn new(n: usize, initial_value: bool) -> Self {
        let blocks = (n + 31) / 32;

        let fill_value = if initial_value { u32::MAX } else { 0 };

        BitVec {
            storage: vec![fill_value; blocks],
            len: n,
        }
    }

    pub fn from_fn<F>(n: usize, mut f: F) -> Self
    where
        F: FnMut(usize) -> bool,
    {
        let mut bv = BitVec::new(n, false);
        for i in 0..n {
            if f(i) {
                bv.set(i, true);
            }
        }
        bv
    }

    pub fn get(&self, index: usize) -> bool {
        if index >= self.len {
            panic!(
                "BitVec index out of bounds: index {}, len {}",
                index, self.len
            );
        }

        let block_idx = index / 32;
        let bit_idx = index % 32;

        let block = self.storage[block_idx];
        let is_set = (block & (1 << bit_idx)) != 0;

        is_set
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if index >= self.len {
            panic!(
                "BitVec index out of bounds: index {}, len {}",
                index, self.len
            );
        }

        let block_idx = index / 32;
        let bit_idx = index % 32;
        let mask = 1 << bit_idx;

        if value {
            self.storage[block_idx] |= mask;
        } else {
            self.storage[block_idx] &= !mask;
        }
    }

    pub fn push(&mut self, value: bool) {
        let block_idx = self.len / 32;
        let bit_idx = self.len % 32;

        if block_idx == self.storage.len() {
            self.storage.push(0);
        }

        let mask = 1 << bit_idx;
        if value {
            self.storage[block_idx] |= mask;
        } else {
            self.storage[block_idx] &= !mask;
        }

        self.len += 1;
    }

    pub fn negate(&mut self) {
        let n = self.storage.len();
        self.storage[..n - 1]
            .iter_mut()
            .for_each(|a| *a ^= u32::MAX);
        self.storage[n - 1] ^= (1 << self.len() % 32) - 1;
    }

    pub fn fill(&mut self, value: bool) {
        let fill_value = if value { u32::MAX } else { 0 };
        self.storage.fill(fill_value);
    }

    pub fn clear(&mut self) {
        self.fill(false);
    }

    pub fn iter(&'_ self) -> BitVecIter<'_> {
        BitVecIter { bv: self, pos: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
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
        if self.pos < self.bv.len {
            let bit = self.bv.get(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialization_false() {
        let bv = BitVec::new(64, false);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.get(0), false);
        assert_eq!(bv.get(63), false);
    }

    #[test]
    fn test_initialization_true() {
        let bv = BitVec::new(10, true);
        assert_eq!(bv.len(), 10);
        assert_eq!(bv.get(0), true);
        assert_eq!(bv.get(9), true);
    }

    #[test]
    fn test_set_and_get() {
        let mut bv = BitVec::new(100, false);

        assert_eq!(bv.get(50), false);

        bv.set(50, true);
        assert_eq!(bv.get(50), true);

        bv.set(50, false);
        assert_eq!(bv.get(50), false);
    }

    #[test]
    #[should_panic]
    fn test_strict_bounds_set() {
        // Allocated capacity is 32 bits (1 u32), but len is 10
        let mut bv = BitVec::new(10, false);

        // This is valid memory-wise (inside the u32), but invalid for our logic
        bv.set(11, true);
    }
}
