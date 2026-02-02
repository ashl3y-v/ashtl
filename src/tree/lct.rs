#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PLCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PLCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [PLCTNode<T>]),
    Push: FnMut([usize; 3], &mut [PLCTNode<T>]),
    Rev: FnMut(usize, &mut [PLCTNode<T>]),
{
    pub ns: Vec<PLCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
}

impl<T, Push, Pull, Rev> PLCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [PLCTNode<T>]),
    Push: FnMut([usize; 3], &mut [PLCTNode<T>]),
    Rev: FnMut(usize, &mut [PLCTNode<T>]),
{
    pub fn new(init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        Self {
            ns: vec![PLCTNode {
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
        nodes.push(PLCTNode {
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
        self.ns.push(PLCTNode {
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

    fn push(&mut self, x: usize) {
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

    fn pull(&mut self, x: usize) {
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

    fn splay(&mut self, x: usize) {
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
        mut f: impl FnMut(usize, [usize; 2], &mut [PLCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.splay(u);
        f(u, self.ns[u].ch, &mut self.ns)
    }

    pub fn query_root<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [PLCTNode<T>]) -> R,
    ) -> R {
        u += 1;
        self.make_root(u);
        f(u, self.ns[u].ch, &mut self.ns)
    }

    pub fn query<R>(
        &mut self,
        mut u: usize,
        mut v: usize,
        mut f: impl FnMut(usize, [usize; 2], usize, [usize; 2], &mut [PLCTNode<T>]) -> R,
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
