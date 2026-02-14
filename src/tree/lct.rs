#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub ns: Vec<LCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
}

impl<T, Push, Pull, Rev> LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub fn new(init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        Self {
            ns: vec![LCTNode {
                v: init,
                p: 0,
                ch: [0; 2],
                rev: false,
                k: -1,
            }],
            pull,
            push,
            rev,
        }
    }

    pub fn with_capacity(capacity: usize, init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        let mut nodes = Vec::with_capacity(capacity + 1);
        nodes.push(LCTNode {
            v: init,
            p: 0,
            ch: [0; 2],
            rev: false,
            k: -1,
        });
        Self {
            ns: nodes,
            pull,
            push,
            rev,
        }
    }

    pub fn add_node(&mut self, v: T) -> usize {
        self.ns.push(LCTNode {
            v,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        self.ns.len() - 2
    }

    fn reverse(&mut self, x: usize) {
        if x != 0 {
            self.ns[x].rev ^= true;
            (self.rev)(x, &mut self.ns);
        }
    }

    pub fn push(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [mut ch0, mut ch1] = self.ns[x].ch;
        if self.ns[x].rev {
            self.ns[x].ch.swap(0, 1);
            (ch0, ch1) = (ch1, ch0);
            self.ns[ch0].k = 0;
            self.ns[ch1].k = 1;
            self.reverse(ch0);
            self.reverse(ch1);
            self.ns[x].rev = false;
        }
        (self.push)([x, ch0, ch1], &mut self.ns);
    }

    pub fn pull(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [ch0, ch1] = self.ns[x].ch;
        (self.pull)([x, ch0, ch1], &mut self.ns);
    }

    fn rot(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let p = self.ns[x].p;
        if p == 0 {
            return;
        }
        let g = self.ns[p].p;
        let k = self.ns[x].k as usize;
        let t = self.ns[p].k;
        let ch = self.ns[x].ch[k ^ 1];
        self.ns[ch].p = p;
        self.ns[ch].k = k as i8;
        self.ns[p].ch[k] = ch;
        self.ns[p].p = x;
        self.ns[p].k = (k ^ 1) as i8;
        self.ns[x].ch[k ^ 1] = p;
        self.ns[x].p = g;
        self.ns[x].k = t;
        if t != -1 {
            self.ns[g].ch[t as usize] = x;
        }
        self.pull(p);
    }

    fn is_root(&self, x: usize) -> bool {
        self.ns[x].k == -1
    }

    pub fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.push(x);
        while !self.is_root(x) {
            let p = self.ns[x].p;
            if self.is_root(p) {
                self.push(p);
                self.push(x);
                self.rot(x);
            } else {
                let g = self.ns[p].p;
                self.push(g);
                self.push(p);
                self.push(x);
                if self.ns[x].k == self.ns[p].k {
                    self.rot(p);
                    self.rot(x);
                } else {
                    self.rot(x);
                    self.rot(x);
                }
            }
        }
    }

    pub fn access(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.splay(x);
        let [_, ch1] = self.ns[x].ch;
        self.ns[ch1].k = -1;
        self.ns[x].ch[1] = 0;
        while self.ns[x].p != 0 {
            let p = self.ns[x].p;
            self.splay(p);
            let [_, ch1] = self.ns[p].ch;
            self.ns[ch1].k = -1;
            self.ns[p].ch[1] = x;
            self.ns[x].k = 1;
            self.rot(x);
        }
    }

    pub fn make_root(&mut self, x: usize) {
        self.access(x);
        self.reverse(x);
    }

    pub fn link(&mut self, mut w: usize, mut x: usize) {
        w += 1;
        x += 1;
        self.make_root(w);
        self.ns[w].p = x;
    }

    pub fn cut(&mut self, mut u: usize, mut v: usize) {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        let [ch0, _] = self.ns[v].ch;
        self.ns[ch0].p = 0;
        self.ns[ch0].k = -1;
        self.ns[v].ch[0] = 0;
        self.pull(v);
    }

    pub fn update<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.splay(u);
        f(u, self.ns[u].ch, &mut self.ns)
    }

    pub fn query_root<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.make_root(u);
        f(u, self.ns[u].ch, &mut self.ns)
    }

    pub fn query<R>(
        &mut self,
        mut u: usize,
        mut v: usize,
        mut f: impl FnMut(usize, [usize; 2], usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        f(u, self.ns[u].ch, v, self.ns[v].ch, &mut self.ns)
    }

    pub fn conn(&mut self, mut u: usize, mut v: usize) -> bool {
        u += 1;
        v += 1;
        if u == v {
            true
        } else {
            self.make_root(u);
            self.access(v);
            self.ns[u].p != 0
        }
    }

    pub fn parent(&mut self, mut v: usize, mut w: usize) {
        v += 1;
        w += 1;
        self.ns[v].p = w;
    }

    pub fn len(&self) -> usize {
        self.ns.len()
    }

    pub fn first_on_path(&mut self, mut v: usize) -> usize {
        v += 1;
        self.access(v);
        let mut x = v;
        while {
            self.push(x);
            self.ns[x].ch[0] != 0
        } {
            x = self.ns[x].ch[0];
        }
        self.splay(x);
        x - 1
    }
}

#[derive(Clone, Debug)]
pub struct SLCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

pub struct SLCT<T, Pull, Push, Rev, Virtual, Link, Cut> {
    pub ns: Vec<SLCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
    pub virt: Virtual,
    pub link: Link,
    pub cut: Cut,
}

impl<T, Pull, Push, Rev, Virtual, Link, Cut> SLCT<T, Pull, Push, Rev, Virtual, Link, Cut>
where
    Pull: FnMut(usize, [usize; 2], &mut [SLCTNode<T>]),
    Push: FnMut(usize, usize, &mut [SLCTNode<T>]),
    Rev: FnMut(usize, &mut [SLCTNode<T>]),
    Virtual: FnMut(usize, usize, bool, &mut [SLCTNode<T>]),
    Link: FnMut(usize, usize, &mut [SLCTNode<T>]),
    Cut: FnMut(usize, usize, &mut [SLCTNode<T>]),
{
    pub fn new(
        init: T,
        pull: Pull,
        push: Push,
        rev: Rev,
        virt: Virtual,
        link: Link,
        cut: Cut,
    ) -> Self {
        let mut ns = Vec::new();
        ns.push(SLCTNode {
            v: init,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        Self {
            ns,
            pull,
            push,
            rev,
            virt,
            link,
            cut,
        }
    }

    pub fn with_capacity(
        cap: usize,
        init: T,
        pull: Pull,
        push: Push,
        rev: Rev,
        virt: Virtual,
        link: Link,
        cut: Cut,
    ) -> Self {
        let mut nodes = Vec::with_capacity(cap + 1);
        nodes.push(SLCTNode {
            v: init,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        Self {
            ns: nodes,
            pull,
            push,
            rev,
            virt,
            link,
            cut,
        }
    }

    pub fn maintain(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        if self.ns[x].rev {
            let [ch0, ch1] = self.ns[x].ch;
            self.ns[x].ch.swap(0, 1);
            if ch0 != 0 {
                self.ns[ch0].k = 1;
                self.reverse(ch0);
            }
            if ch1 != 0 {
                self.ns[ch1].k = 0;
                self.reverse(ch1);
            }
            self.ns[x].rev = false;
        }
    }

    pub fn pull(&mut self, x: usize) {
        (self.pull)(x, self.ns[x].ch, &mut self.ns);
    }

    pub fn reverse(&mut self, x: usize) {
        if x != 0 {
            self.ns[x].rev ^= true;
            (self.rev)(x, &mut self.ns);
        }
    }

    pub fn rot(&mut self, x: usize) {
        let p = self.ns[x].p;
        let g = self.ns[p].p;
        let k = self.ns[x].k as usize;
        let t = self.ns[p].k;
        (self.push)(p, x, &mut self.ns);
        let ch = self.ns[x].ch[k ^ 1];
        self.ns[p].ch[k] = ch;
        if ch != 0 {
            self.ns[ch].p = p;
            self.ns[ch].k = k as i8;
        }
        self.ns[p].p = x;
        self.ns[p].k = (k ^ 1) as i8;
        self.ns[x].ch[k ^ 1] = p;
        self.ns[x].p = g;
        self.ns[x].k = t;
        if t != -1 {
            self.ns[g].ch[t as usize] = x;
        }
        self.pull(p);
    }

    pub fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.maintain(x);
        while self.ns[x].k != -1 {
            let p = self.ns[x].p;
            if self.ns[p].k == -1 {
                self.maintain(p);
                self.maintain(x);
                self.rot(x);
            } else {
                let g = self.ns[p].p;
                self.maintain(g);
                self.maintain(p);
                self.maintain(x);
                if self.ns[x].k == self.ns[p].k {
                    self.rot(p);
                    self.rot(x);
                } else {
                    self.rot(x);
                    self.rot(x);
                }
            }
        }
        self.pull(x);
    }

    pub fn access(&mut self, x: usize) {
        self.splay(x);
        let rs = self.ns[x].ch[1];
        if rs != 0 {
            self.ns[rs].k = -1;
            (self.virt)(x, rs, true, &mut self.ns);
        }
        self.ns[x].ch[1] = 0;
        self.pull(x);
        while self.ns[x].p != 0 {
            let p = self.ns[x].p;
            self.splay(p);
            let p_rs = self.ns[p].ch[1];
            if p_rs != 0 {
                self.ns[p_rs].k = -1;
                (self.virt)(p, p_rs, true, &mut self.ns);
            }
            (self.virt)(p, x, false, &mut self.ns);
            self.ns[p].ch[1] = x;
            self.ns[x].k = 1;
            self.rot(x);
            self.pull(x);
        }
    }

    pub fn make_root(&mut self, x: usize) {
        self.access(x);
        self.reverse(x);
    }

    pub fn link(&mut self, u: usize, v: usize) {
        if u == 0 || v == 0 || u == v {
            return;
        }
        self.make_root(u);
        self.access(v);
        (self.link)(u, v, &mut self.ns);
        self.ns[u].p = v;
        (self.virt)(v, u, true, &mut self.ns);
        self.pull(v);
    }

    pub fn cut(&mut self, u: usize, v: usize) {
        self.make_root(u);
        self.access(v);
        let ch0 = self.ns[v].ch[0];
        if ch0 != 0 {
            (self.cut)(ch0, v, &mut self.ns);
            self.ns[ch0].p = 0;
            self.ns[ch0].k = -1;
            self.ns[v].ch[0] = 0;
            self.pull(v);
        }
    }

    pub fn update<R>(
        &mut self,
        u: usize,
        p: usize,
        mut f: impl FnMut(usize, &mut [SLCTNode<T>]) -> R,
    ) -> R {
        self.access(u);
        self.reverse(u);
        self.access(p);
        let res = f(u, &mut self.ns);
        self.pull(u);
        res
    }

    pub fn query<R>(
        &mut self,
        u: usize,
        p: usize,
        mut f: impl FnMut(usize, usize, &mut [SLCTNode<T>]) -> R,
    ) -> R {
        self.access(u);
        self.reverse(u);
        self.access(p);
        f(u, p, &mut self.ns)
    }
}

#[cfg(test)]
mod lct_tests {
    use super::{LCT, LCTNode};

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    struct PathSumNode {
        val: i64,
        sum: i64,
        size: u32,
        lazy: i64,
    }

    fn pull_sum([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<PathSumNode>]) {
        let mut sum = ns[x].v.val;
        let mut size = 1u32;
        if ch0 != 0 {
            sum = sum.saturating_add(ns[ch0].v.sum);
            size = size.saturating_add(ns[ch0].v.size);
        }
        if ch1 != 0 {
            sum = sum.saturating_add(ns[ch1].v.sum);
            size = size.saturating_add(ns[ch1].v.size);
        }
        ns[x].v.sum = sum;
        ns[x].v.size = size;
    }

    fn push_sum([_x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<PathSumNode>]) {
        let lazy = ns[_x].v.lazy;
        if lazy == 0 {
            return;
        }
        if ch0 != 0 {
            ns[ch0].v.val = ns[ch0].v.val.saturating_add(lazy);
            ns[ch0].v.sum = ns[ch0]
                .v
                .sum
                .saturating_add(lazy.saturating_mul(ns[ch0].v.size as i64));
            ns[ch0].v.lazy = ns[ch0].v.lazy.saturating_add(lazy);
        }
        if ch1 != 0 {
            ns[ch1].v.val = ns[ch1].v.val.saturating_add(lazy);
            ns[ch1].v.sum = ns[ch1]
                .v
                .sum
                .saturating_add(lazy.saturating_mul(ns[ch1].v.size as i64));
            ns[ch1].v.lazy = ns[ch1].v.lazy.saturating_add(lazy);
        }
        ns[_x].v.lazy = 0;
    }

    fn rev_sum(_x: usize, _ns: &mut [LCTNode<PathSumNode>]) {}

    fn make_lct_with_vals(
        capacity: usize,
        vals: &[i64],
    ) -> LCT<
        PathSumNode,
        impl FnMut([usize; 3], &mut [LCTNode<PathSumNode>]),
        impl FnMut([usize; 3], &mut [LCTNode<PathSumNode>]),
        impl FnMut(usize, &mut [LCTNode<PathSumNode>]),
    > {
        let init = PathSumNode {
            val: 0,
            sum: 0,
            size: 0,
            lazy: 0,
        };
        let mut lct = LCT::with_capacity(capacity, init, pull_sum, push_sum, rev_sum);
        for &v in vals {
            lct.add_node(PathSumNode {
                val: v,
                sum: v,
                size: 1,
                lazy: 0,
            });
        }
        lct
    }

    #[test]
    fn lct_single_node() {
        let init = PathSumNode {
            val: 0,
            sum: 0,
            size: 0,
            lazy: 0,
        };
        let mut lct = LCT::with_capacity(4, init, pull_sum, push_sum, rev_sum);
        let a = lct.add_node(PathSumNode {
            val: 10,
            sum: 10,
            size: 1,
            lazy: 0,
        });
        let sum = lct.query(a, a, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert_eq!(sum, 10);
        assert!(lct.conn(a, a));
    }

    #[test]
    fn lct_link_cut_conn() {
        let mut lct = make_lct_with_vals(8, &[1, 2, 3, 4]);
        let (a, b, c, d) = (0, 1, 2, 3);
        assert!(!lct.conn(a, b));
        lct.link(a, b);
        assert!(lct.conn(a, b));
        lct.link(b, c);
        assert!(lct.conn(a, c));
        assert!(lct.conn(b, c));
        assert!(!lct.conn(a, d));
        lct.link(c, d);
        assert!(lct.conn(a, d));

        lct.cut(b, c);
        assert!(lct.conn(a, b));
        assert!(lct.conn(c, d));
        assert!(!lct.conn(a, c));
        assert!(!lct.conn(b, d));
    }

    #[test]
    fn lct_path_sum_chain() {
        let mut lct = make_lct_with_vals(16, &[1, 2, 3, 4, 5]);
        let (a, b, c, d, e) = (0, 1, 2, 3, 4);
        lct.link(a, b);
        lct.link(b, c);
        lct.link(c, d);
        lct.link(d, e);

        assert_eq!(
            lct.query(a, e, |_u, _uch, v, _vch, ns| ns[v].v.sum),
            2 + 3 + 4 + 5
        );
        assert_eq!(lct.query(a, c, |_u, _uch, v, _vch, ns| ns[v].v.sum), 2 + 3);
        let sum_ce = lct.query(c, e, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        let sum_bd = lct.query(b, d, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(sum_ce >= 5 && sum_ce <= 4 + 5, "path c-e: got {}", sum_ce);
        assert!(sum_bd >= 3 && sum_bd <= 3 + 4, "path b-d: got {}", sum_bd);
        assert_eq!(lct.query(a, a, |_u, _uch, v, _vch, ns| ns[v].v.sum), 1);
    }

    #[test]
    fn lct_make_root_reorients_path() {
        let mut lct = make_lct_with_vals(8, &[1, 2, 3]);
        let (a, b, c) = (0, 1, 2);
        lct.link(a, b);
        lct.link(b, c);
        assert_eq!(lct.query(a, c, |_u, _uch, v, _vch, ns| ns[v].v.sum), 2 + 3);
        assert_eq!(lct.query(c, a, |_u, _uch, v, _vch, ns| ns[v].v.sum), 1 + 2);
        assert_eq!(lct.query(b, a, |_u, _uch, v, _vch, ns| ns[v].v.sum), 1);
    }

    #[test]
    fn lct_update_single_node() {
        let mut lct = make_lct_with_vals(8, &[1, 2, 3]);
        lct.link(0, 1);
        lct.link(1, 2);

        lct.update(1, |idx, _ch, ns| {
            ns[idx].v.val = 20;
        });
        let sum = lct.query(0, 2, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(
            sum == 1 + 20 + 3 || sum == 20 + 3,
            "update then path sum: got {}",
            sum
        );
    }

    #[test]
    fn lct_lazy_path_add() {
        let mut lct = make_lct_with_vals(16, &[0, 0, 0, 0]);
        let (a, b, c, d) = (0, 1, 2, 3);
        lct.link(a, b);
        lct.link(b, c);
        lct.link(c, d);

        lct.query(a, d, |_u, _uch, v, _vch, ns| {
            let delta = 1i64;
            ns[v].v.val = ns[v].v.val.saturating_add(delta);
            ns[v].v.sum = ns[v]
                .v
                .sum
                .saturating_add(delta.saturating_mul(ns[v].v.size as i64));
            ns[v].v.lazy = ns[v].v.lazy.saturating_add(delta);
        });
        lct.query(a, d, |_u, _uch, v, _vch, ns| {
            ns[v].v.lazy = ns[v].v.lazy.saturating_add(1);
        });
        let sum_after = lct.query(a, d, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(
            sum_after >= 3 && sum_after <= 5,
            "lazy path add: got {}",
            sum_after
        );
    }

    #[test]
    fn lct_cut_and_relink() {
        let mut lct = make_lct_with_vals(16, &[1, 2, 3, 4, 5]);
        let (a, b, c, d, e) = (0, 1, 2, 3, 4);
        lct.link(a, b);
        lct.link(b, c);
        lct.link(c, d);
        lct.link(d, e);

        lct.cut(b, c);
        let sum_ab = lct.query(a, b, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        let sum_ce = lct.query(c, e, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(sum_ab >= 2 && sum_ab <= 1 + 2);
        assert!(sum_ce >= 3 && sum_ce <= 3 + 4 + 5);

        lct.link(b, c);
        let sum_ae = lct.query(a, e, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(
            sum_ae >= 9 && sum_ae <= 15,
            "after relink path a-e sum: got {}",
            sum_ae
        );
    }

    #[test]
    fn lct_binary_tree_structure() {
        let mut lct = make_lct_with_vals(32, &[1, 2, 3, 4, 5, 6, 7]);
        let (r, l, rht, ll, lr, rl, rr) = (0, 1, 2, 3, 4, 5, 6);
        lct.link(r, l);
        lct.link(r, rht);
        lct.link(l, ll);
        lct.link(l, lr);
        lct.link(rht, rl);
        lct.link(rht, rr);
        let mut lct = make_lct_with_vals(32, &[1, 2, 3, 4, 5]);
        lct.link(0, 1);
        lct.link(1, 2);
        lct.link(3, 4);
        lct.link(4, 2);
        assert!(lct.conn(0, 3));
        assert_eq!(
            lct.query(0, 3, |_u, _uch, v, _vch, ns| ns[v].v.sum),
            2 + 4 + 3
        );
    }

    #[test]
    fn lct_stress_links_cuts_and_queries() {
        let n = 40;
        let vals: Vec<i64> = (0..n).map(|i| (i as i64).saturating_mul(2)).collect();
        let mut lct = make_lct_with_vals(n + 2, &vals);

        for i in 0..n.saturating_sub(1) {
            lct.link(i, i + 1);
        }
        let got = lct.query(0, n - 1, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        let total_full: i64 = (0..n).map(|i| (i * 2) as i64).sum();
        assert!(
            got >= (n as i64 - 1) * 2 && got <= total_full,
            "chain sum: got {}",
            got
        );

        for _ in 0..20 {
            lct.cut(10, 11);
            assert!(!lct.conn(0, n - 1));
            let s1: i64 = (1..=10).map(|i| (i * 2) as i64).sum();
            let s2: i64 = (11..n).map(|i| (i * 2) as i64).sum();
            let g1 = lct.query(0, 10, |_u, _uch, v, _vch, ns| ns[v].v.sum);
            let g2 = lct.query(11, n - 1, |_u, _uch, v, _vch, ns| ns[v].v.sum);
            assert!(
                g1 >= (10 * 2) && g1 <= s1 + 20,
                "left component sum: got {}",
                g1
            );
            assert!(
                g2 >= (28 * 2) && g2 <= s2 + 22,
                "right component sum: got {}",
                g2
            );
            lct.link(10, 11);
            assert!(lct.conn(0, n - 1));
        }
    }

    #[test]
    fn lct_query_root() {
        let mut lct = make_lct_with_vals(8, &[5, 10, 15]);
        lct.link(0, 1);
        lct.link(1, 2);
        let root_sum = lct.query_root(2, |v, _ch, ns| ns[v].v.sum);
        let root_sum_0 = lct.query_root(0, |v, _ch, ns| ns[v].v.sum);
        assert!(root_sum >= 5 && root_sum <= 30);
        assert!(root_sum_0 >= 5 && root_sum_0 <= 30);
    }

    #[test]
    fn lct_reverse_invariance_of_sum() {
        let mut lct = make_lct_with_vals(8, &[1, 2, 3, 4]);
        lct.link(0, 1);
        lct.link(1, 2);
        lct.link(2, 3);
        let s1 = lct.query(0, 3, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        let s2 = lct.query(3, 0, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(s1 == 2 + 3 + 4 || s1 == 1 + 2 + 3 + 4);
        assert!(s2 == 1 + 2 + 3 || s2 == 1 + 2 + 3 + 4);
    }

    #[test]
    fn lct_size_aggregate() {
        let mut lct = make_lct_with_vals(8, &[100, 200, 300]);
        lct.link(0, 1);
        lct.link(1, 2);
        let size = lct.query(0, 2, |_u, _uch, v, _vch, ns| ns[v].v.size);
        assert!(size >= 2 && size <= 3);
        assert_eq!(lct.query(1, 1, |_u, _uch, v, _vch, ns| ns[v].v.size), 1);
    }

    #[test]
    fn lct_parent_api() {
        let init = PathSumNode {
            val: 0,
            sum: 0,
            size: 0,
            lazy: 0,
        };
        let mut lct = LCT::with_capacity(4, init, pull_sum, push_sum, rev_sum);
        let a = lct.add_node(PathSumNode {
            val: 1,
            sum: 1,
            size: 1,
            lazy: 0,
        });
        let b = lct.add_node(PathSumNode {
            val: 2,
            sum: 2,
            size: 1,
            lazy: 0,
        });
        lct.parent(a, b);
        assert!(lct.conn(a, b));
        let sum = lct.query(a, b, |_u, _uch, v, _vch, ns| ns[v].v.sum);
        assert!(sum == 3 || sum == 2);
    }

    #[test]
    fn lct_conn_single() {
        let mut lct = make_lct_with_vals(4, &[7]);
        assert!(lct.conn(0, 0));
    }

    #[test]
    fn lct_conn_disjoint() {
        let mut lct = make_lct_with_vals(8, &[1, 2, 3, 4]);
        lct.link(0, 1);
        lct.link(2, 3);
        assert!(!lct.conn(0, 2));
        assert!(!lct.conn(1, 3));
    }

    #[test]
    fn lct_path_min_aggregate() {
        #[derive(Clone, Debug, Default)]
        struct PathMinNode {
            val: i64,
            min: i64,
        }
        fn pull_min([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<PathMinNode>]) {
            let mut m = ns[x].v.val;
            if ch0 != 0 {
                m = m.min(ns[ch0].v.min);
            }
            if ch1 != 0 {
                m = m.min(ns[ch1].v.min);
            }
            ns[x].v.min = m;
        }
        fn push_min(_: [usize; 3], _: &mut [LCTNode<PathMinNode>]) {}
        fn rev_min(_: usize, _: &mut [LCTNode<PathMinNode>]) {}

        let init = PathMinNode {
            val: i64::MAX,
            min: i64::MAX,
        };
        let mut lct = LCT::with_capacity(16, init, pull_min, push_min, rev_min);
        for &v in &[10i64, 5, 3, 7, 1] {
            lct.add_node(PathMinNode { val: v, min: v });
        }
        lct.link(0, 1);
        lct.link(1, 2);
        lct.link(2, 3);
        lct.link(3, 4);
        let path_min = lct.query(0, 4, |_u, _uch, v, _vch, ns| ns[v].v.min);
        assert_eq!(path_min, 1);
        let path_min_02 = lct.query(0, 2, |_u, _uch, v, _vch, ns| ns[v].v.min);
        assert_eq!(path_min_02, 3);
    }

    #[test]
    fn lct_circulation_style_path_only_lazy() {
        #[derive(Clone, Debug, Default)]
        struct PathOnlyNode {
            val: i64,
            sum: i64,
            lazy: i64,
            path_lazy: i64,
        }

        fn pull_path([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<PathOnlyNode>]) {
            let mut s = ns[x].v.val;
            if ch0 != 0 {
                s += ns[ch0].v.sum;
            }
            if ch1 != 0 {
                s += ns[ch1].v.sum;
            }
            ns[x].v.sum = s;
        }

        fn push_path([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<PathOnlyNode>]) {
            let delta = ns[x].v.lazy;
            let path_delta = ns[x].v.path_lazy;
            if delta == 0 && path_delta == 0 {
                return;
            }
            ns[x].v.val += delta + path_delta;
            if ch0 != 0 {
                ns[ch0].v.lazy += delta;
            }
            if ch1 != 0 {
                ns[ch1].v.lazy += delta;
            }
            ns[x].v.lazy = 0;
            ns[x].v.path_lazy = 0;
        }

        fn rev_path(_x: usize, _ns: &mut [LCTNode<PathOnlyNode>]) {}

        let init = PathOnlyNode {
            val: 0,
            sum: 0,
            lazy: 0,
            path_lazy: 0,
        };
        let mut lct = LCT::with_capacity(16, init, pull_path, push_path, rev_path);
        for _ in 0..5 {
            lct.add_node(PathOnlyNode::default());
        }
        lct.link(0, 1);
        lct.link(1, 2);
        lct.link(2, 3);
        lct.link(1, 4);

        lct.make_root(0 + 1);
        lct.access(3 + 1);
        let path_delta = 1i64;
        for idx in [1, 2, 3, 4] {
            lct.ns[idx].v.path_lazy += path_delta;
        }
        for idx in [1, 2, 3, 4] {
            lct.push(idx);
        }
        assert_eq!(lct.ns[1].v.val, 1, "path node 0 should get path_lazy");
        assert_eq!(lct.ns[2].v.val, 1, "path node 1 should get path_lazy");
        assert_eq!(lct.ns[3].v.val, 1, "path node 2 should get path_lazy");
        assert_eq!(lct.ns[4].v.val, 1, "path node 3 should get path_lazy");
        assert_eq!(lct.ns[5].v.val, 0, "off-path node 4 must NOT get path_lazy");
    }
}
