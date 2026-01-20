use std::{
    fmt::Debug,
    ops::{Index, IndexMut},
};

pub struct DSU {
    pub p: Vec<isize>,
}

impl DSU {
    pub fn new(n: usize) -> Self {
        Self { p: vec![-1; n] }
    }

    pub fn find(&mut self, mut x: usize) -> usize {
        while self.p[x] >= 0 {
            let p = self.p[x] as usize;
            if self.p[p] >= 0 {
                self.p[x] = self.p[p];
            }
            x = p;
        }
        x
    }

    pub fn same(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn union(&mut self, x: usize, y: usize) -> (usize, bool) {
        let mut i = self.find(x);
        let mut j = self.find(y);
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (i, false);
        }
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        (i, true)
    }

    pub fn union_root(&mut self, x: usize, mut r: usize) -> (usize, bool) {
        let mut i = self.find(x);
        if i == r {
            return (r, false);
        }
        if self.p[i] > self.p[r] {
            (i, r) = (r, i);
        }
        self.p[i] += self.p[r];
        self.p[r] = i as isize;
        (i, true)
    }

    pub fn size(&mut self, x: usize) -> usize {
        let r = self.find(x);
        (-self.p[r]) as usize
    }

    pub fn resize(&mut self, n: usize) {
        self.p.resize(n, -1);
    }
}

impl Debug for DSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self.p))
    }
}

impl<Idx, T> Index<Idx> for DSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for DSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}

// TODO: DSU with potential
// https://judge.yosupo.jp/submission/214503
// https://judge.yosupo.jp/submission/236404
// https://maspypy.github.io/library/ds/unionfind/potentialized_unionfind.hpp
// https://maspypy.github.io/library/ds/unionfind/rollback_potentialized_unionfind.hpp

pub struct RollbackDSU {
    pub p: Vec<isize>,
    pub joins: Vec<(usize, isize)>,
}

impl RollbackDSU {
    pub fn new(n: usize) -> Self {
        Self {
            p: vec![-1; n],
            joins: Vec::new(),
        }
    }

    pub fn find(&self, mut i: usize) -> usize {
        while self.p[i] >= 0 {
            i = self.p[i] as usize;
        }
        i
    }

    pub fn same(&self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn size(&self, x: usize) -> usize {
        (-self.p[self.find(x)]) as usize
    }

    pub fn union(&mut self, x: usize, y: usize) -> (usize, bool) {
        let (mut i, mut j) = (self.find(x), self.find(y));
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (i, false);
        }
        self.joins.push((j, self.p[j]));
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        return (i, true);
    }

    pub fn rollback(&mut self, t: usize) {
        while self.joins.len() > t
            && let Some((i, s)) = self.joins.pop()
        {
            let pi = self.p[i] as usize;
            self.p[pi] -= s;
            self.p[i] = s;
        }
    }
}

impl Debug for RollbackDSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}, {:?}", self.p, self.joins))
    }
}

impl<Idx, T> Index<Idx> for RollbackDSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for RollbackDSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}
