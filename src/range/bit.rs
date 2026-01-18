pub struct BIT<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn new(mut bit: Vec<T>, mut f: F) -> Self {
        let n = bit.len();
        for i in 0..n {
            if i | i + 1 < n {
                bit[i | i + 1] = f(&bit[i | i + 1], &bit[i]);
            }
        }
        Self { bit, f }
    }

    pub fn update(&mut self, mut i: usize, d: T) -> &mut Self {
        while i < self.bit.len() {
            self.bit[i] = (self.f)(&self.bit[i], &d);
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, mut i: usize, id: T) -> T {
        let mut res = id;

        while i > 0 {
            res = (self.f)(&res, &self.bit[i - 1]);
            i &= i - 1;
        }
        res
    }
}

impl<T: PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn lower_bound(&self, max: T) -> usize {
        let mut pos = 0;

        let n = self.bit.len();
        let mut pw = usize::MAX.unbounded_shr(n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= n && self.bit[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}

pub struct BIT2D<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    n: usize,
    m: usize,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn new(mut bit: Vec<T>, n: usize, m: usize, mut f: F) -> Self {
        for i in 0..n {
            for j in 0..m {
                if j | j + 1 < m {
                    bit[i * m + (j | j + 1)] = f(&bit[i * m + (j | j + 1)], &bit[i * m + j]);
                }
            }
        }
        for i in 0..n {
            if i | i + 1 < n {
                for j in 0..m {
                    bit[(i | i + 1) * m + j] = f(&bit[(i | i + 1) * m + j], &bit[i * m + j]);
                }
            }
        }
        Self { bit, n, m, f }
    }

    pub fn update(&mut self, (mut i, j): (usize, usize), d: T) -> &mut Self {
        while i < self.n {
            let mut j = j;
            while j < self.m {
                self.bit[i * self.m + j] = (self.f)(&self.bit[i * self.m + j], &d);
                j |= j + 1;
            }
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, (mut i, j): (usize, usize), identity: T) -> T {
        let mut res = identity;

        while i > 0 {
            let mut j = j;
            while j > 0 {
                res = (self.f)(&res, &self.bit[(i - 1) * self.m + j - 1]);
                j &= j - 1;
            }
            i &= i - 1;
        }
        res
    }
}

impl<T: std::cmp::PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn lower_bound_row(&self, i: usize, max: T) -> usize {
        let mut pos = 0;

        let row = &self.bit[i * self.m..(i + 1) * self.m];
        let mut pw = usize::MAX.unbounded_shr(self.m.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.m && row[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }

    pub fn lower_bound_col(&self, j: usize, max: T) -> usize {
        let mut pos = 0;

        let mut pw = usize::MAX.unbounded_shr(self.n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.n && self.bit[(pos | pw - 1) * self.m + j] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}
