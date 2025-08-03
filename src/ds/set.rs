type E = u128;
const B: usize = E::BITS as usize;

#[derive(Clone, Debug)]
pub struct UbIntSet {
    n: usize,
    l: usize,
    t: Vec<Vec<E>>,
}

impl UbIntSet {
    pub fn new(n: usize) -> Self {
        let mut s = Self {
            n,
            l: 0,
            t: Vec::new(),
        };
        s.build();
        s
    }

    fn build(&mut self) {
        let mut m = self.n;
        while m > 1 {
            m = (m + B - 1) / B;
            self.t.push(vec![0; m]);
        }
        self.l = self.t.len();
    }

    pub fn insert(&mut self, mut i: usize) -> &mut Self {
        for h in 0..self.l {
            let r = 1 << i % B;
            i /= B;
            self.t[h][i] |= r;
        }
        self
    }

    pub fn remove(&mut self, mut i: usize) -> &mut Self {
        for h in 0..self.l {
            let r = !(1 << i % B);
            i /= B;
            self.t[h][i] &= r;
            if self.t[h][i] != 0 {
                break;
            }
        }
        self
    }

    pub fn contains(&self, i: usize) -> bool {
        self.t[0][i / B] & (1 << i % B) != 0
    }

    pub fn is_empty(&self) -> bool {
        self.t[self.l - 1][0] != 0
    }

    pub fn pred(&self, mut i: usize) -> usize {
        if i >= self.n {
            i = self.n - 1;
        }
        for h in 0..self.l {
            let d = self.t[h][i / B] << B - 1 - i % B;
            if d == 0 {
                if i < B {
                    break;
                }
                i = i / B - 1;
                continue;
            }
            i -= d.leading_zeros() as usize;
            for g in (0..h).rev() {
                i *= B;
                i += self.t[g][i / B].ilog2() as usize;
            }
            return i;
        }
        usize::MAX
    }

    pub fn succ(&self, mut i: usize) -> usize {
        if i >= self.n {
            return usize::MAX;
        }
        for h in 0..self.l {
            let d = self.t[h][i / B] >> i % B;
            if d == 0 {
                i = i / B + 1;
                continue;
            }
            i += d.trailing_zeros() as usize;
            for g in (0..h).rev() {
                i *= B;
                i += self.t[g][i / B].trailing_zeros() as usize;
            }
            return i;
        }
        usize::MAX
    }

    pub fn expred(&self, mut i: usize) -> usize {
        if i >= self.n {
            i = self.n - 1;
        }
        for h in 0..self.l {
            let d = self.t[h][i / B] << B - 1 - i % B;
            if d == E::MAX {
                if i < B {
                    break;
                }
                i = i / B - 1;
                continue;
            }
            i -= d.leading_ones() as usize;
            for g in (0..h).rev() {
                i *= B;
                i += B - self.t[g][i / B].leading_ones() as usize;
            }
            return i;
        }
        usize::MAX
    }

    pub fn exsucc(&self, mut i: usize) -> usize {
        if i >= self.n {
            return usize::MAX;
        }
        for h in 0..self.l {
            let d = self.t[h][i / B] >> i % B;
            if d == E::MAX {
                i = i / B + 1;
                continue;
            }
            i += d.trailing_ones() as usize;
            for g in (0..h).rev() {
                i *= B;
                i += self.t[g][i / B].trailing_ones() as usize;
            }
            return i;
        }
        usize::MAX
    }

    pub fn len(&self) -> usize {
        self.n
    }
}
