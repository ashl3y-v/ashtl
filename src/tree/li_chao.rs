pub trait LiChaoFunc: Clone + Copy {
    fn eval(&self, x: i64) -> i64;

    fn max() -> Self;
}

pub trait LiChaoLazy<F>: Clone + Copy + PartialEq + Default {
    fn apply_to_func(&self, f: &mut F);

    fn merge(&mut self, parent: &Self);
}

#[derive(Clone, Copy, Debug)]
pub struct LiChaoNode<F: LiChaoFunc, Z: LiChaoLazy<F>> {
    pub x: F,
    pub lazy: Z,
    pub l: usize,
    pub r: usize,
}

impl<F: LiChaoFunc, Z: LiChaoLazy<F>> LiChaoNode<F, Z> {
    pub fn new(f: F) -> Self {
        Self {
            x: f,
            lazy: Z::default(),
            l: usize::MAX,
            r: usize::MAX,
        }
    }
}

pub struct LiChao<const L: i64, const R: i64, F: LiChaoFunc, Z: LiChaoLazy<F>> {
    pub ns: Vec<LiChaoNode<F, Z>>,
}

impl<const L: i64, const R: i64, F: LiChaoFunc, Z: LiChaoLazy<F>> LiChao<L, R, F, Z> {
    pub fn new() -> Self {
        let mut tree = Self { ns: Vec::new() };
        tree.new_node(F::max());
        tree
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut tree = Self {
            ns: Vec::with_capacity(capacity),
        };
        tree.new_node(F::max());
        tree
    }

    fn new_node(&mut self, x: F) -> usize {
        let i = self.ns.len();
        self.ns.push(LiChaoNode::new(x));
        i
    }

    fn push(&mut self, i: usize) {
        if self.ns[i].lazy == Z::default() {
            return;
        }
        if self.ns[i].l == usize::MAX {
            self.ns[i].l = self.new_node(F::max());
        }
        if self.ns[i].r == usize::MAX {
            self.ns[i].r = self.new_node(F::max());
        }
        let lc = self.ns[i].l;
        let rc = self.ns[i].r;
        let lazy = self.ns[i].lazy;
        self.ns[lc].lazy.merge(&lazy);
        lazy.apply_to_func(&mut self.ns[lc].x);
        self.ns[rc].lazy.merge(&lazy);
        lazy.apply_to_func(&mut self.ns[rc].x);
        self.ns[i].lazy = Z::default();
    }

    /// O(log C)
    pub fn add(&mut self, x: F) {
        let x_l = x.eval(L);
        let x_r = x.eval(R - 1);
        self.update_seg(x, 0, L, R, x_l, x_r);
    }

    /// O(log^2 C)
    pub fn add_seg(&mut self, x: F, ql: i64, qr: i64) {
        self.update_range_rec(x, 0, L, R, ql, qr);
    }

    /// O(log^2 C)
    pub fn range_lazy_update(&mut self, val: Z, ql: i64, qr: i64) {
        self.update_lazy_rec(0, L, R, ql, qr, val);
    }

    fn update_lazy_rec(&mut self, i: usize, l: i64, r: i64, ql: i64, qr: i64, val: Z) {
        if l >= qr || r <= ql {
            return;
        } else if l >= ql && r <= qr {
            self.ns[i].lazy.merge(&val);
            val.apply_to_func(&mut self.ns[i].x);
            return;
        }
        self.push(i);
        let m = l.midpoint(r);
        if self.ns[i].l == usize::MAX {
            self.ns[i].l = self.new_node(F::max());
        }
        if self.ns[i].r == usize::MAX {
            self.ns[i].r = self.new_node(F::max());
        }
        let cur = self.ns[i].x;
        self.ns[i].x = F::max();
        let fl_l = cur.eval(l);
        let fl_r = cur.eval(m - 1);
        self.update_seg(cur, self.ns[i].l, l, m, fl_l, fl_r);
        let fr_l = cur.eval(m);
        let fr_r = cur.eval(r - 1);
        self.update_seg(cur, self.ns[i].r, m, r, fr_l, fr_r);
        self.update_lazy_rec(self.ns[i].l, l, m, ql, qr, val);
        self.update_lazy_rec(self.ns[i].r, m, r, ql, qr, val);
    }

    fn update_range_rec(&mut self, x: F, i: usize, l: i64, r: i64, ql: i64, qr: i64) {
        if l >= qr || r <= ql {
            return;
        }
        self.push(i);
        if l >= ql && r <= qr {
            let x_l = x.eval(l);
            let x_r = x.eval(r - 1);
            self.update_seg(x, i, l, r, x_l, x_r);
            return;
        }
        let m = l.midpoint(r);
        if self.ns[i].l == usize::MAX {
            self.ns[i].l = self.new_node(F::max());
        }
        if self.ns[i].r == usize::MAX {
            self.ns[i].r = self.new_node(F::max());
        }
        let lc = self.ns[i].l;
        let rc = self.ns[i].r;
        self.update_range_rec(x, lc, l, m, ql, qr);
        self.update_range_rec(x, rc, m, r, ql, qr);
    }

    fn update_seg(
        &mut self,
        mut x: F,
        mut i: usize,
        mut l: i64,
        mut r: i64,
        mut x_l: i64,
        mut x_r: i64,
    ) {
        loop {
            self.push(i);
            let z_l = self.ns[i].x.eval(l);
            let z_r = self.ns[i].x.eval(r - 1);
            if x_l <= z_l && x_r <= z_r {
                self.ns[i].x = x;
                return;
            } else if x_l >= z_l && x_r >= z_r {
                return;
            }
            let m = l.midpoint(r);
            let z_mid = self.ns[i].x.eval(m - 1);
            let x_mid = x.eval(m - 1);
            if x_l > z_l {
                if x_mid < z_mid {
                    std::mem::swap(&mut x, &mut self.ns[i].x);
                    r = m;
                    x_l = z_l;
                    x_r = z_mid;
                } else {
                    l = m;
                    x_l = x.eval(m);
                }
            } else {
                let z_midp1 = self.ns[i].x.eval(m);
                if x.eval(m) < z_midp1 {
                    std::mem::swap(&mut x, &mut self.ns[i].x);
                    l = m;
                    x_l = z_midp1;
                    x_r = z_r;
                } else {
                    r = m;
                    x_r = x_mid;
                }
            }
            if r == m {
                if self.ns[i].l == usize::MAX {
                    self.ns[i].l = self.new_node(x);
                }
                i = self.ns[i].l;
            } else if l == m {
                if self.ns[i].r == usize::MAX {
                    self.ns[i].r = self.new_node(x);
                }
                i = self.ns[i].r;
            } else {
                break;
            }
        }
    }

    /// O(log C)
    pub fn query(&mut self, i: i64) -> i64 {
        self.query_rec(0, L, R, i)
    }

    fn query_rec(&mut self, i: usize, l: i64, r: i64, x: i64) -> i64 {
        self.push(i);
        let val = self.ns[i].x.eval(x);
        if l + 1 == r {
            return val;
        }
        let m = l.midpoint(r);
        let child_res = if x < m {
            if self.ns[i].l != usize::MAX {
                self.query_rec(self.ns[i].l, l, m, x)
            } else {
                i64::MAX
            }
        } else {
            if self.ns[i].r != usize::MAX {
                self.query_rec(self.ns[i].r, m, r, x)
            } else {
                i64::MAX
            }
        };
        val.min(child_res)
    }
}
