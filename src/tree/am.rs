use std::collections::HashMap;
use std::ops::{Add, AddAssign, Sub, SubAssign};

use rand::Rng;
use rand::rngs::ThreadRng;

pub struct AMTree {
    p: Vec<usize>,
    s: Vec<i64>,
    t: Vec<(i64, i64)>,
}

impl AMTree {
    pub fn new(n: usize) -> Self {
        AMTree {
            p: vec![usize::MAX; n],
            s: vec![1; n],
            t: vec![(i64::MAX, -1); n],
        }
    }

    pub fn rot(&mut self, x: usize, y: usize) {
        if self.t[x] >= self.t[y] {
            self.s[y] -= self.s[x];
            self.p[x] = self.p[y];
        } else {
            self.s[y] -= self.s[x];
            self.s[x] += self.s[y];
            (self.t[x], self.t[y]) = (self.t[y], self.t[x]);
            self.p[x] = self.p[y];
            self.p[y] = x;
        }
    }

    pub fn upward_calibrate(&mut self, mut x: usize) {
        while self.p[x] != usize::MAX {
            let y = self.p[x];
            if self.s[x] * 3 <= self.s[y] * 2 {
                x = y;
            } else {
                self.rot(x, y);
            }
        }
    }

    pub fn link(&mut self, ts: (i64, i64), u: usize, v: usize) -> (i64, i64) {
        if u == v {
            return ts;
        }
        self.upward_calibrate(u);
        self.upward_calibrate(v);
        let mut x = u;
        let mut y = v;
        let mut max_t = (i64::MIN, -1);
        let mut max_x = usize::MAX;
        loop {
            if x == y {
                break;
            }
            if self.s[x] > self.s[y] {
                std::mem::swap(&mut x, &mut y);
            }
            if self.t[x].0 == i64::MAX {
                break;
            }
            if self.t[x].0 > max_t.0 {
                max_t = self.t[x];
                max_x = x;
            }
            x = self.p[x];
        }
        let mut res = (0, i64::MIN);
        if x == y {
            if ts >= max_t {
                return ts;
            }
            res = max_t;
            x = max_x;
            let mut curr_y = self.p[x];
            while curr_y != usize::MAX {
                self.s[curr_y] -= self.s[x];
                curr_y = self.p[curr_y];
            }
            self.p[x] = usize::MAX;
            self.t[x] = (i64::MAX, -1);
        }
        x = u;
        y = v;
        let mut w = ts;
        let mut dx = 0;
        let mut dy = 0;
        while x != usize::MAX && y != usize::MAX {
            if w >= self.t[x] {
                self.s[self.p[x]] += dx;
                x = self.p[x];
            } else if w >= self.t[y] {
                self.s[self.p[y]] += dy;
                y = self.p[y];
            } else {
                if self.s[x] > self.s[y] {
                    std::mem::swap(&mut x, &mut y);
                    std::mem::swap(&mut dx, &mut dy);
                }
                dx -= self.s[x];
                dy += self.s[x];
                self.s[y] += self.s[x];
                let px_old = self.p[x];
                self.p[x] = y;
                (self.t[x], w) = (w, self.t[x]);
                if px_old != usize::MAX {
                    self.s[px_old] += dx;
                }
                x = px_old;
            }
        }
        if y != usize::MAX {
            y = self.p[y];
            while y != usize::MAX {
                self.s[y] += dy;
                y = self.p[y];
            }
        }
        res
    }
}

pub struct FoldableAMTree<T> {
    p: Vec<usize>,
    s: Vec<i64>,
    c: Vec<(i64, i64)>,
    v: Vec<T>,
}

impl<T> FoldableAMTree<T>
where
    T: Clone + Copy + Default + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign,
{
    pub fn new(n: usize, init: Vec<T>) -> Self {
        FoldableAMTree {
            p: vec![usize::MAX; n],
            s: vec![1; n],
            c: vec![(i64::MAX, -1); n],
            v: init,
        }
    }

    pub fn root(&self, mut x: usize) -> usize {
        while self.p[x] != usize::MAX {
            x = self.p[x];
        }
        x
    }

    pub fn component_sum(&self, u: usize) -> T {
        let root = self.root(u);
        self.v[root]
    }

    pub fn vertex_add(&mut self, u: usize, val: T) {
        let mut curr = u;
        while curr != usize::MAX {
            self.v[curr] += val;
            curr = self.p[curr];
        }
    }

    pub fn rot(&mut self, x: usize, y: usize) {
        if self.c[x] >= self.c[y] {
            self.s[y] -= self.s[x];
            let z = self.v[x];
            self.v[y] -= z;
            self.p[x] = self.p[y];
        } else {
            self.s[y] -= self.s[x];
            let z = self.v[x];
            self.v[y] -= z;
            self.s[x] += self.s[y];
            let z = self.v[y];
            self.v[x] += z;
            let z = self.c[x];
            self.c[x] = self.c[y];
            self.c[y] = z;
            self.p[x] = self.p[y];
            self.p[y] = x;
        }
    }

    pub fn upward_calibrate(&mut self, mut x: usize) {
        while self.p[x] != usize::MAX {
            let y = self.p[x];
            if self.s[x] * 3 <= self.s[y] * 2 {
                x = y;
            } else {
                self.rot(x, y);
            }
        }
    }

    pub fn link(&mut self, ts: (i64, i64), u: usize, v: usize) -> (i64, i64) {
        if u == v {
            return ts;
        }
        self.upward_calibrate(u);
        self.upward_calibrate(v);
        let mut x = u;
        let mut y = v;
        let mut max_t = (i64::MIN, -1);
        let mut max_x = usize::MAX;
        loop {
            if x == y {
                break;
            }
            if self.s[x] > self.s[y] {
                std::mem::swap(&mut x, &mut y);
            }
            if self.c[x].0 == i64::MAX {
                break;
            }
            if self.c[x] > max_t {
                max_t = self.c[x];
                max_x = x;
            }
            x = self.p[x];
        }
        let mut res = (0, i64::MIN);
        if x == y {
            if ts >= max_t {
                return ts;
            }
            res = max_t;
            x = max_x;
            let val_x = self.v[x];
            let mut curr_y = self.p[x];
            while curr_y != usize::MAX {
                self.s[curr_y] -= self.s[x];
                self.v[curr_y] -= val_x;
                curr_y = self.p[curr_y];
            }
            self.p[x] = usize::MAX;
            self.c[x] = (i64::MAX, -1);
        }
        x = u;
        y = v;
        let mut w = ts;
        let mut dx = 0;
        let mut dy = 0;
        let mut dv_x = T::default();
        let mut dv_y = T::default();
        while x != usize::MAX && y != usize::MAX {
            if w >= self.c[x] {
                self.s[self.p[x]] += dx;
                self.v[self.p[x]] += dv_x;
                x = self.p[x];
            } else if w >= self.c[y] {
                self.s[self.p[y]] += dy;
                self.v[self.p[y]] += dv_y;
                y = self.p[y];
            } else {
                if self.s[x] > self.s[y] {
                    std::mem::swap(&mut x, &mut y);
                    std::mem::swap(&mut dx, &mut dy);
                    std::mem::swap(&mut dv_x, &mut dv_y);
                }
                dx -= self.s[x];
                dv_x -= self.v[x];
                dy += self.s[x];
                dv_y += self.v[x];
                self.s[y] += self.s[x];
                let z = self.v[x];
                self.v[y] += z;
                let px_old = self.p[x];
                self.p[x] = y;
                (self.c[x], w) = (w, self.c[x]);
                if px_old != usize::MAX {
                    self.s[px_old] += dx;
                    self.v[px_old] += dv_x;
                }
                x = px_old;
            }
        }
        if y != usize::MAX {
            y = self.p[y];
            while y != usize::MAX {
                self.s[y] += dy;
                self.v[y] += dv_y;
                y = self.p[y];
            }
        }
        res
    }

    pub fn cut(&mut self, ts: (i64, i64), u: usize, v: usize) -> bool {
        if u == v {
            return false;
        }
        self.upward_calibrate(u);
        self.upward_calibrate(v);
        let mut x = u;
        let mut y = v;
        let mut max_t = (i64::MIN, -1);
        let mut max_x = usize::MAX;
        loop {
            if x == y {
                break;
            }
            if self.s[x] > self.s[y] {
                std::mem::swap(&mut x, &mut y);
            }
            if self.c[x].0 == i64::MAX {
                break;
            }
            if self.c[x] == ts {
                max_t = self.c[x];
                max_x = x;
            }
            x = self.p[x];
        }
        if x == y && max_t == ts {
            let cut_node = max_x;
            let val_cut = self.v[cut_node];
            let mut curr = self.p[cut_node];
            while curr != usize::MAX {
                self.s[curr] -= self.s[cut_node];
                self.v[curr] -= val_cut;
                curr = self.p[curr];
            }
            self.p[cut_node] = usize::MAX;
            self.c[cut_node] = (i64::MAX, -1);
            return true;
        }
        false
    }
}

pub struct VertexAddComponentSum<T> {
    t: FoldableAMTree<T>,
    es: HashMap<(usize, usize), (i64, i64)>,
    rng: ThreadRng,
}

impl<T> VertexAddComponentSum<T>
where
    T: Clone + Copy + Default + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign,
{
    pub fn new(values: Vec<T>) -> Self {
        let n = values.len();
        VertexAddComponentSum {
            t: FoldableAMTree::new(n, values),
            es: HashMap::new(),
            rng: rand::rng(),
        }
    }

    pub fn add_edge(&mut self, mut u: usize, mut v: usize) {
        if u == v {
            return;
        }
        if u > v {
            std::mem::swap(&mut u, &mut v);
        }
        if self.es.contains_key(&(u, v)) {
            return;
        }
        let w = (self.rng.random::<i64>(), self.rng.random::<i64>());
        self.es.insert((u, v), w);
        self.t.link(w, u, v);
    }

    pub fn remove_edge(&mut self, mut u: usize, mut v: usize) {
        if u > v {
            std::mem::swap(&mut u, &mut v);
        }
        if let Some(w) = self.es.remove(&(u, v)) {
            self.t.cut(w, u, v);
        }
    }

    pub fn add_val(&mut self, u: usize, val: T) {
        self.t.vertex_add(u, val);
    }

    pub fn query_component(&self, u: usize) -> T {
        self.t.component_sum(u)
    }
}
