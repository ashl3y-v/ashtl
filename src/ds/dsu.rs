pub struct DSU {
    pub dsu: Vec<isize>,
}

impl DSU {
    pub fn new(n: usize) -> Self {
        Self { dsu: vec![-1; n] }
    }

    pub fn find(&mut self, mut x: usize) -> usize {
        while self.dsu[x] >= 0 {
            let p = self.dsu[x] as usize;
            if self.dsu[p] >= 0 {
                self.dsu[x] = self.dsu[p];
            }
            x = p;
        }
        x
    }

    pub fn union(&mut self, a: usize, b: usize) -> (bool, usize) {
        let mut i = self.find(a);
        let mut j = self.find(b);
        if i == j {
            return (false, i);
        }
        if self.dsu[i] > self.dsu[j] {
            (i, j) = (j, i);
        }
        self.dsu[i] += self.dsu[j];
        self.dsu[j] = i as isize;
        (true, i)
    }

    pub fn union_root(&mut self, a: usize, mut r: usize) -> (bool, usize) {
        let mut i = self.find(a);
        if i == r {
            return (false, r);
        }
        if self.dsu[i] > self.dsu[r] {
            (i, r) = (r, i);
        }
        self.dsu[i] += self.dsu[r];
        self.dsu[r] = i as isize;
        (true, i)
    }

    pub fn size(&mut self, x: usize) -> usize {
        let r = self.find(x);
        (-self.dsu[r]) as usize
    }
}

// TODO: DSU with potential
// https://judge.yosupo.jp/submission/214503
// https://judge.yosupo.jp/submission/236404

// TODO: persistent union find
// https://judge.yosupo.jp/problem/persistent_unionfind
