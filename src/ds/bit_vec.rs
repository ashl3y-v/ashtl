use std::ops::Index;

const B: usize = 64;

#[derive(Debug, Clone)]
pub struct BitVec {
    n: usize,
    seg: Vec<Vec<u64>>,
}

impl BitVec {
    pub fn new(n: usize, initial_value: bool) -> Self {
        if n == 0 {
            return Self {
                n: 0,
                seg: vec![vec![0]],
            };
        }
        let mut seg = Vec::new();
        let mut m = n;
        loop {
            seg.push(vec![0; (m + B - 1) / B]);
            m = (m + B - 1) / B;
            if m <= 1 {
                break;
            }
        }
        let mut result = Self { n, seg };
        if initial_value {
            result.seg[0].fill(u64::MAX);
            let rem = n % B;
            if rem != 0 {
                let last = result.seg[0].len() - 1;
                result.seg[0][last] = (1u64 << rem) - 1;
            }
            result.rebuild_upper();
        }
        result
    }

    pub fn from_fn<F: FnMut(usize) -> bool>(n: usize, mut f: F) -> Self {
        let mut bv = Self::new(n, false);
        for i in 0..n {
            bv.seg[0][i / B] |= (f(i) as u64) << (i % B);
        }
        bv.rebuild_upper();
        bv
    }

    fn rebuild_upper(&mut self) {
        for h in 0..self.seg.len() - 1 {
            self.seg[h + 1].fill(0);
            for i in 0..self.seg[h].len() {
                self.seg[h + 1][i / B] |= ((self.seg[h][i] != 0) as u64) << (i % B);
            }
        }
    }

    pub fn len(&self) -> usize {
        self.n
    }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    pub fn push(&mut self, value: bool) {
        let i = self.n;
        self.n += 1;
        // Extend levels as needed
        for h in 0..self.seg.len() {
            let idx = i / B.pow(h as u32 + 1);
            if idx >= self.seg[h].len() {
                self.seg[h].push(0);
            }
        }
        // Check if we need a new level
        let top_len = self.seg.last().unwrap().len();
        if top_len > 1 {
            self.seg.push(vec![0; (top_len + B - 1) / B]);
            for j in 0..self.seg[self.seg.len() - 2].len() {
                if self.seg[self.seg.len() - 2][j] != 0 {
                    self.seg.last_mut().unwrap()[j / B] |= 1 << (j % B);
                }
            }
        }
        if value {
            self.insert(i);
        }
    }

    pub fn get(&self, i: usize) -> bool {
        debug_assert!(i < self.n);
        (self.seg[0][i / B] >> (i % B)) & 1 != 0
    }

    pub fn contains(&self, i: usize) -> bool {
        self.get(i)
    }

    pub fn set(&mut self, i: usize, value: bool) {
        debug_assert!(i < self.n);
        if value {
            self.insert(i);
        } else {
            self.remove(i);
        }
    }

    pub fn insert(&mut self, i: usize) {
        debug_assert!(i < self.n);
        let mut i = i;
        for h in 0..self.seg.len() {
            self.seg[h][i / B] |= 1 << (i % B);
            i /= B;
        }
    }

    pub fn remove(&mut self, i: usize) {
        debug_assert!(i < self.n);
        let mut i = i;
        for h in 0..self.seg.len() {
            self.seg[h][i / B] &= !(1 << (i % B));
            let x = (self.seg[h][i / B] != 0) as u64;
            i /= B;
            if h + 1 < self.seg.len() {
                self.seg[h + 1][i / B] &= !(1 << (i % B));
                self.seg[h + 1][i / B] |= x << (i % B);
            }
        }
    }

    pub fn next(&self, i: usize) -> Option<usize> {
        if i >= self.n {
            return None;
        }
        let mut i = i;
        for h in 0..self.seg.len() {
            if i / B >= self.seg[h].len() {
                return None;
            }
            let d = self.seg[h][i / B] >> (i % B);
            if d == 0 {
                i = i / B + 1;
                continue;
            }
            i += d.trailing_zeros() as usize;
            for g in (0..h).rev() {
                i *= B;
                i += self.seg[g][i / B].trailing_zeros() as usize;
            }
            return if i < self.n { Some(i) } else { None };
        }
        None
    }

    pub fn prev(&self, i: usize) -> Option<usize> {
        let mut i = i.min(self.n.saturating_sub(1)) as isize;
        for h in 0..self.seg.len() {
            if i < 0 {
                return None;
            }
            let d = self.seg[h][i as usize / B] << (63 - i as usize % B);
            if d == 0 {
                i = i / B as isize - 1;
                continue;
            }
            i -= d.leading_zeros() as isize;
            for g in (0..h).rev() {
                i *= B as isize;
                i += (63 - self.seg[g][i as usize / B].leading_zeros()) as isize;
            }
            return Some(i as usize);
        }
        None
    }

    pub fn any(&self, l: usize, r: usize) -> bool {
        self.next(l).map_or(false, |x| x < r)
    }

    pub fn enumerate<F: FnMut(usize)>(&self, l: usize, r: usize, mut f: F) {
        let mut x = match self.next(l) {
            Some(x) => x,
            None => return,
        };
        while x < r {
            f(x);
            x = match self.next(x + 1) {
                Some(x) => x,
                None => return,
            };
        }
    }

    pub fn negate(&mut self) {
        if self.n == 0 {
            return;
        }
        for block in &mut self.seg[0] {
            *block ^= u64::MAX;
        }
        let rem = self.n % B;
        if rem != 0 {
            let last = self.seg[0].len() - 1;
            self.seg[0][last] &= (1u64 << rem) - 1;
        }
        self.rebuild_upper();
    }

    pub fn fill(&mut self, value: bool) {
        if self.n == 0 {
            return;
        }
        let fill_val = if value { u64::MAX } else { 0 };
        self.seg[0].fill(fill_val);
        if value {
            let rem = self.n % B;
            if rem != 0 {
                let last = self.seg[0].len() - 1;
                self.seg[0][last] = (1u64 << rem) - 1;
            }
        }
        self.rebuild_upper();
    }

    pub fn clear(&mut self) {
        for level in &mut self.seg {
            level.fill(0);
        }
    }

    pub fn iter(&self) -> BitVecIter<'_> {
        BitVecIter { bv: self, pos: 0 }
    }

    pub fn ones(&self) -> BitVecOnes<'_> {
        BitVecOnes { bv: self, pos: 0 }
    }

    pub fn count_ones(&self) -> usize {
        self.seg[0].iter().map(|&x| x.count_ones() as usize).sum()
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
        if self.pos < self.bv.n {
            let bit = self.bv.get(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }
}

pub struct BitVecOnes<'a> {
    bv: &'a BitVec,
    pos: usize,
}

impl<'a> Iterator for BitVecOnes<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.bv.next(self.pos)?;
        self.pos = result + 1;
        Some(result)
    }
}
