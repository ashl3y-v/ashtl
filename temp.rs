pub trait TopTreeMonoid {
    type Path: Clone + Default;
    type Point: Clone + Default;
    type Info: Clone + Default;

    fn vertex(info: &Self::Info) -> Self::Path;
    fn compress(p: &Self::Path, c: &Self::Path) -> Self::Path;
    fn rake(l: &Self::Point, r: &Self::Point) -> Self::Point;
    fn add_edge(p: &Self::Path) -> Self::Point;
    fn add_vertex(p: &Self::Point, i: &Self::Info) -> Self::Path;
}

#[derive(Clone, Default)]
struct TopTreeNode<S: TopTreeMonoid> {
    l: usize,
    r: usize,
    p: usize,
    info: S::Info,
    key: S::Path,
    sum: S::Path,
    mus: S::Path,
    light: usize,
    belong: usize,
    rev: bool,
}

#[derive(Clone, Default)]
struct TopTreeDashedNode<S: TopTreeMonoid> {
    l: usize,
    r: usize,
    p: usize,
    key: S::Point,
    sum: S::Point,
}

pub struct TopTree<S: TopTreeMonoid> {
    nodes: Vec<TopTreeNode<S>>,
    dashed: Vec<TopTreeDashedNode<S>>,
    dashed_free: Vec<usize>,
}

impl<S: Default + TopTreeMonoid> TopTree<S> {
    pub fn new(n: usize, infos: Vec<S::Info>) -> Self {
        let mut nodes = Vec::with_capacity(n + 1);
        nodes.push(TopTreeNode::default());
        for info in infos {
            let key = S::vertex(&info);
            nodes.push(TopTreeNode {
                l: 0,
                r: 0,
                p: 0,
                info,
                key: key.clone(),
                sum: key.clone(),
                mus: key,
                light: 0,
                belong: 0,
                rev: false,
            });
        }
        let mut dashed = Vec::new();
        dashed.push(TopTreeDashedNode::default());
        Self {
            nodes,
            dashed,
            dashed_free: Vec::new(),
        }
    }

    fn alloc_dashed(&mut self, key: S::Point) -> usize {
        if let Some(idx) = self.dashed_free.pop() {
            self.dashed[idx] = TopTreeDashedNode {
                l: 0,
                r: 0,
                p: 0,
                key: key.clone(),
                sum: key,
            };
            idx
        } else {
            let idx = self.dashed.len();
            self.dashed.push(TopTreeDashedNode {
                l: 0,
                r: 0,
                p: 0,
                key: key.clone(),
                sum: key,
            });
            idx
        }
    }

    fn free_dashed(&mut self, idx: usize) {
        if idx != 0 {
            self.dashed_free.push(idx);
        }
    }

    fn dashed_update(&mut self, t: usize) {
        if t == 0 {
            return;
        }
        let mut sum = self.dashed[t].key.clone();
        let l = self.dashed[t].l;
        let r = self.dashed[t].r;
        if l != 0 {
            sum = S::rake(&sum, &self.dashed[l].sum);
        }
        if r != 0 {
            sum = S::rake(&sum, &self.dashed[r].sum);
        }
        self.dashed[t].sum = sum;
    }

    fn dashed_rotate(&mut self, t: usize, right: bool) {
        let p = self.dashed[t].p;
        let g = self.dashed[p].p;
        if right {
            // Rotate Right
            let r = self.dashed[t].r;
            self.dashed[p].l = r;
            if r != 0 {
                self.dashed[r].p = p;
            }
            self.dashed[t].r = p;
            self.dashed[p].p = t;
        } else {
            // Rotate Left
            let l = self.dashed[t].l;
            self.dashed[p].r = l;
            if l != 0 {
                self.dashed[l].p = p;
            }
            self.dashed[t].l = p;
            self.dashed[p].p = t;
        }
        self.dashed_update(p);
        self.dashed_update(t);
        self.dashed[t].p = g;
        if g != 0 {
            if self.dashed[g].l == p {
                self.dashed[g].l = t;
            } else {
                self.dashed[g].r = t;
            }
        }
    }

    fn dashed_splay(&mut self, t: usize) {
        while self.dashed[t].p != 0 {
            let p = self.dashed[t].p;
            let g = self.dashed[p].p;
            if g == 0 {
                // Zig
                if self.dashed[p].l == t {
                    self.dashed_rotate(t, true);
                } else {
                    self.dashed_rotate(t, false);
                }
            } else {
                let p_left = self.dashed[g].l == p;
                let t_left = self.dashed[p].l == t;
                if p_left == t_left {
                    // Zig-Zig
                    if p_left {
                        self.dashed_rotate(p, true);
                        self.dashed_rotate(t, true);
                    } else {
                        self.dashed_rotate(p, false);
                        self.dashed_rotate(t, false);
                    }
                } else {
                    // Zig-Zag
                    if t_left {
                        self.dashed_rotate(t, true);
                        self.dashed_rotate(t, false);
                    } else {
                        self.dashed_rotate(t, false);
                        self.dashed_rotate(t, true);
                    }
                }
            }
        }
    }

    fn dashed_insert(&mut self, root: usize, val: S::Point) -> usize {
        let node = self.alloc_dashed(val);
        if root == 0 {
            return node;
        }
        // Insert as rightmost child to maintain order if needed,
        // though rake order technically doesn't matter for commutative ops.
        // Usually rake trees are just binary search trees or unsorted.
        // We'll append to the right.
        let mut cur = root;
        while self.dashed[cur].r != 0 {
            cur = self.dashed[cur].r;
        }
        self.dashed_splay(cur); // Splay the rightmost to root
        // Now cur is root and has no right child
        self.dashed[cur].r = node;
        self.dashed[node].p = cur;
        self.dashed_update(cur);
        self.dashed_splay(node);
        node
    }

    fn dashed_erase(&mut self, t: usize) -> usize {
        self.dashed_splay(t);
        let l = self.dashed[t].l;
        let r = self.dashed[t].r;
        self.free_dashed(t);
        if l == 0 {
            if r != 0 {
                self.dashed[r].p = 0;
            }
            return r;
        }
        if r == 0 {
            self.dashed[l].p = 0;
            return l;
        }
        self.dashed[l].p = 0;
        self.dashed[r].p = 0;
        // Join l and r: find rightmost of l, splay it, attach r
        let mut cur = l;
        while self.dashed[cur].r != 0 {
            cur = self.dashed[cur].r;
        }
        self.dashed_splay(cur);
        self.dashed[cur].r = r;
        self.dashed[r].p = cur;
        self.dashed_update(cur);
        cur
    }

    fn is_root(&self, t: usize) -> bool {
        let p = self.nodes[t].p;
        p == 0 || (self.nodes[p].l != t && self.nodes[p].r != t)
    }

    fn reverse(&mut self, t: usize) {
        if t == 0 {
            return;
        }
        let l = self.nodes[t].l;
        let r = self.nodes[t].r;
        self.nodes[t].l = r;
        self.nodes[t].r = l;
        let sum = self.nodes[t].sum.clone();
        let mus = self.nodes[t].mus.clone();
        self.nodes[t].sum = mus;
        self.nodes[t].mus = sum;
        self.nodes[t].rev ^= true;
    }

    fn push(&mut self, t: usize) {
        if t == 0 {
            return;
        }
        if self.nodes[t].rev {
            let l = self.nodes[t].l;
            let r = self.nodes[t].r;
            self.reverse(l);
            self.reverse(r);
            self.nodes[t].rev = false;
        }
    }

    fn update(&mut self, t: usize) {
        if t == 0 {
            return;
        }
        // Rake dashed edges into key
        let light = self.nodes[t].light;
        let key = if light != 0 {
            S::add_vertex(&self.dashed[light].sum, &self.nodes[t].info)
        } else {
            S::vertex(&self.nodes[t].info)
        };
        let mut sum = key.clone();
        let mut mus = key.clone();
        let l = self.nodes[t].l;
        let r = self.nodes[t].r;
        if l != 0 {
            sum = S::compress(&self.nodes[l].sum, &sum);
            mus = S::compress(&mus, &self.nodes[l].mus);
        }
        if r != 0 {
            sum = S::compress(&sum, &self.nodes[r].sum);
            mus = S::compress(&self.nodes[r].mus, &mus);
        }
        self.nodes[t].key = key;
        self.nodes[t].sum = sum;
        self.nodes[t].mus = mus;
    }

    fn rotate(&mut self, t: usize, right: bool) {
        let p = self.nodes[t].p;
        let g = self.nodes[p].p;
        // Push rev flags before structural change
        // In top-down splay/expose we usually push beforehand,
        // but here we do it inside rotate to be safe.
        self.push(p);
        self.push(t);
        if right {
            let r = self.nodes[t].r;
            self.nodes[p].l = r;
            if r != 0 {
                self.nodes[r].p = p;
            }
            self.nodes[t].r = p;
            self.nodes[p].p = t;
        } else {
            let l = self.nodes[t].l;
            self.nodes[p].r = l;
            if l != 0 {
                self.nodes[l].p = p;
            }
            self.nodes[t].l = p;
            self.nodes[p].p = t;
        }
        self.update(p);
        self.update(t);
        self.nodes[t].p = g;
        if g != 0 {
            if self.nodes[g].l == p {
                self.nodes[g].l = t;
            } else if self.nodes[g].r == p {
                self.nodes[g].r = t;
            }
            // If p was connected via light/belong pointers (path parent but not tree parent),
            // g's l/r won't point to p, so we don't update g's children.
        }
        // Maintain 'belong' pointer (path-parent pointer logic)
        self.nodes[t].belong = self.nodes[p].belong;
        self.nodes[p].belong = 0;
    }

    fn splay(&mut self, t: usize) {
        self.push(t);
        while !self.is_root(t) {
            let p = self.nodes[t].p;
            if self.is_root(p) {
                self.push(p);
                self.push(t);
                if self.nodes[p].l == t {
                    self.rotate(t, true);
                } else {
                    self.rotate(t, false);
                }
            } else {
                let g = self.nodes[p].p;
                self.push(g);
                self.push(p);
                self.push(t);
                let p_left = self.nodes[g].l == p;
                let t_left = self.nodes[p].l == t;
                if p_left == t_left {
                    if p_left {
                        self.rotate(p, true);
                        self.rotate(t, true);
                    } else {
                        self.rotate(p, false);
                        self.rotate(t, false);
                    }
                } else {
                    if t_left {
                        self.rotate(t, true);
                        self.rotate(t, false);
                    } else {
                        self.rotate(t, false);
                        self.rotate(t, true);
                    }
                }
            }
        }
    }

    fn expose(&mut self, t: usize) -> usize {
        let mut rp = 0;
        let mut cur = t;
        while cur != 0 {
            self.splay(cur);
            // Move current right child (heavy) to light (dashed)
            let r = self.nodes[cur].r;
            if r != 0 {
                let val = S::add_edge(&self.nodes[r].sum);
                let dashed_node = self.dashed_insert(self.nodes[cur].light, val);
                self.nodes[cur].light = dashed_node;
                self.nodes[r].belong = dashed_node;
            }
            // Move rp (which was light) to heavy (right child)
            self.nodes[cur].r = rp;
            // Remove rp from light (dashed)
            if rp != 0 {
                let belong = self.nodes[rp].belong;
                self.dashed_splay(belong);
                // Note: The structure of dashed tree changed, update light pointer of cur
                // But wait, 'belong' points to the dashed node representing 'rp'.
                // If we erase it, the root of the dashed tree might change.
                self.nodes[cur].light = self.dashed_erase(belong);
                self.nodes[rp].belong = 0;
            }
            self.update(cur);
            rp = cur;
            cur = self.nodes[cur].p;
        }
        self.splay(t);
        rp
    }

    pub fn link(&mut self, child: usize, parent: usize) {
        if child == 0 || parent == 0 {
            return;
        }
        self.expose(child);
        self.reverse(child);
        self.push(child); // Evert
        self.expose(parent);
        self.nodes[child].p = parent;
        self.nodes[parent].r = child;
        self.update(parent);
    }

    pub fn cut(&mut self, u: usize, v: usize) {
        if u == 0 || v == 0 {
            return;
        }
        self.expose(u);
        self.reverse(u);
        self.push(u); // Evert u
        self.expose(v);
        // v should be the root of the splay, u should be left child if connected
        if self.nodes[v].l == u {
            self.nodes[v].l = 0;
            self.nodes[u].p = 0;
            self.update(v);
        }
    }

    pub fn set_info(&mut self, u: usize, info: S::Info) {
        if u == 0 {
            return;
        }
        self.expose(u);
        self.nodes[u].info = info;
        self.update(u);
    }

    pub fn query(&mut self, u: usize) -> S::Path {
        if u == 0 {
            return S::Path::default();
        }
        self.expose(u);
        self.reverse(u);
        self.push(u);
        self.nodes[u].sum.clone()
    }
}
