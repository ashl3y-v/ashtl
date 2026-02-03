#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StaticTopTreeNodeType {
    Vertex,
    AddVertex,
    Compress,
    Rake,
    AddEdge,
}

pub struct StaticTopTree {
    pub n: usize,
    pub p: Vec<usize>,
    pub l: Vec<usize>,
    pub r: Vec<usize>,
    pub typ: Vec<StaticTopTreeNodeType>,
    pub root: usize,
}

impl StaticTopTree {
    /// O(n log n)
    pub fn new(parent: &[usize]) -> Self {
        let n = parent.len();
        let mut tt = Self {
            n,
            p: vec![usize::MAX; n],
            l: vec![usize::MAX; n],
            r: vec![usize::MAX; n],
            typ: vec![StaticTopTreeNodeType::Vertex; n],
            root: 0,
        };
        if n == 0 {
            return tt;
        }
        let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
        for v in 1..n {
            adj[parent[v]].push(v);
        }
        tt.dfs_size(&mut adj, 0);
        tt.root = tt.compress(&adj, 0).0;
        tt
    }

    fn dfs_size(&self, adj: &mut [Vec<usize>], u: usize) -> usize {
        let mut s = 1;
        let mut best = 0;
        for i in 0..adj[u].len() {
            let t = self.dfs_size(adj, adj[u][i]);
            s += t;
            if best < t {
                best = t;
                adj[u].swap(0, i);
            }
        }
        s
    }

    fn add(&mut self, k: usize, l: usize, r: usize, t: StaticTopTreeNodeType) -> usize {
        let v = if k == usize::MAX { self.p.len() } else { k };
        if v >= self.p.len() {
            self.p.resize(v + 1, usize::MAX);
            self.l.resize(v + 1, usize::MAX);
            self.r.resize(v + 1, usize::MAX);
            self.typ.resize(v + 1, StaticTopTreeNodeType::Vertex);
        }
        self.p[v] = usize::MAX;
        self.l[v] = l;
        self.r[v] = r;
        self.typ[v] = t;
        if l != usize::MAX {
            self.p[l] = v;
        }
        if r != usize::MAX {
            self.p[r] = v;
        }
        v
    }

    fn merge(&mut self, items: &[(usize, usize)], t: StaticTopTreeNodeType) -> (usize, usize) {
        if items.len() == 1 {
            return items[0];
        }
        let mut u: i64 = items.iter().map(|&(_, s)| s as i64).sum();
        let (mut left, mut right) = (vec![], vec![]);
        for &(i, s) in items {
            if u > s as i64 {
                left.push((i, s));
            } else {
                right.push((i, s));
            }
            u -= 2 * s as i64;
        }
        let ((i, si), (j, sj)) = (self.merge(&left, t), self.merge(&right, t));
        (self.add(usize::MAX, i, j, t), si + sj)
    }

    fn compress(&mut self, adj: &[Vec<usize>], mut i: usize) -> (usize, usize) {
        let mut chs = vec![self.add_vertex(adj, i)];
        while !adj[i].is_empty() {
            i = adj[i][0];
            chs.push(self.add_vertex(adj, i));
        }
        self.merge(&chs, StaticTopTreeNodeType::Compress)
    }

    fn rake(&mut self, adj: &[Vec<usize>], i: usize) -> (usize, usize) {
        let chs: Vec<_> = adj[i]
            .iter()
            .skip(1)
            .map(|&j| self.add_edge(adj, j))
            .collect();
        if chs.is_empty() {
            (usize::MAX, 0)
        } else {
            self.merge(&chs, StaticTopTreeNodeType::Rake)
        }
    }

    fn add_edge(&mut self, adj: &[Vec<usize>], i: usize) -> (usize, usize) {
        let (j, sj) = self.compress(adj, i);
        (
            self.add(usize::MAX, j, usize::MAX, StaticTopTreeNodeType::AddEdge),
            sj,
        )
    }

    fn add_vertex(&mut self, adj: &[Vec<usize>], i: usize) -> (usize, usize) {
        let (j, sj) = self.rake(adj, i);
        let t = if j == usize::MAX {
            StaticTopTreeNodeType::Vertex
        } else {
            StaticTopTreeNodeType::AddVertex
        };
        (self.add(i, j, usize::MAX, t), sj + 1)
    }

    pub fn calc<Path: Clone, Point: Clone>(
        &self,
        mut v: impl FnMut(usize) -> Path,
        mut cmpr: impl FnMut(Path, Path) -> Path,
        mut rake: impl FnMut(Point, Point) -> Point,
        mut add_e: impl FnMut(Path) -> Point,
        mut add_v: impl FnMut(Point, usize) -> Path,
        id: Point,
    ) -> Path {
        self.path(
            self.root, &mut v, &mut cmpr, &mut rake, &mut add_e, &mut add_v, &id,
        )
    }

    fn path<Path: Clone, Point: Clone>(
        &self,
        k: usize,
        v: &mut impl FnMut(usize) -> Path,
        cmpr: &mut impl FnMut(Path, Path) -> Path,
        rake: &mut impl FnMut(Point, Point) -> Point,
        add_e: &mut impl FnMut(Path) -> Point,
        add_v: &mut impl FnMut(Point, usize) -> Path,
        id: &Point,
    ) -> Path {
        match self.typ[k] {
            StaticTopTreeNodeType::Vertex => v(k),
            StaticTopTreeNodeType::AddVertex => {
                let raked = if self.l[k] == usize::MAX {
                    id.clone()
                } else {
                    self.point(self.l[k], v, cmpr, rake, add_e, add_v, id)
                };
                add_v(raked, k)
            }
            StaticTopTreeNodeType::Compress => {
                let lp = self.path(self.l[k], v, cmpr, rake, add_e, add_v, id);
                let rp = self.path(self.r[k], v, cmpr, rake, add_e, add_v, id);
                cmpr(lp, rp)
            }
            _ => unreachable!(),
        }
    }

    fn point<Path: Clone, Point: Clone>(
        &self,
        k: usize,
        v: &mut impl FnMut(usize) -> Path,
        cmpr: &mut impl FnMut(Path, Path) -> Path,
        rake: &mut impl FnMut(Point, Point) -> Point,
        add_e: &mut impl FnMut(Path) -> Point,
        add_v: &mut impl FnMut(Point, usize) -> Path,
        id: &Point,
    ) -> Point {
        match self.typ[k] {
            StaticTopTreeNodeType::Rake => {
                let lpt = self.point(self.l[k], v, cmpr, rake, add_e, add_v, id);
                let rpt = self.point(self.r[k], v, cmpr, rake, add_e, add_v, id);
                rake(lpt, rpt)
            }
            StaticTopTreeNodeType::AddEdge => {
                let p = self.path(self.l[k], v, cmpr, rake, add_e, add_v, id);
                add_e(p)
            }
            _ => unreachable!(),
        }
    }

    pub fn update<Path: Clone, Point: Clone>(
        &self,
        s: usize,
        path: &mut [Path],
        pt: &mut [Point],
        v: impl Fn(usize) -> Path,
        cmpr: impl Fn(&Path, &Path) -> Path,
        rake: impl Fn(&Point, &Point) -> Point,
        add_e: impl Fn(&Path) -> Point,
        add_v: impl Fn(&Point, usize) -> Path,
        id: &Point,
    ) {
        let mut k = s;
        while k != usize::MAX {
            match self.typ[k] {
                StaticTopTreeNodeType::Vertex => {
                    path[k] = v(k);
                }
                StaticTopTreeNodeType::AddVertex => {
                    let raked = if self.l[k] == usize::MAX {
                        id.clone()
                    } else {
                        pt[self.l[k]].clone()
                    };
                    path[k] = add_v(&raked, k);
                }
                StaticTopTreeNodeType::Compress => {
                    path[k] = cmpr(&path[self.l[k]], &path[self.r[k]]);
                }
                StaticTopTreeNodeType::Rake => {
                    pt[k] = rake(&pt[self.l[k]], &pt[self.r[k]]);
                }
                StaticTopTreeNodeType::AddEdge => {
                    pt[k] = add_e(&path[self.l[k]]);
                }
            }
            k = self.p[k];
        }
    }

    pub fn len(&self) -> usize {
        self.p.len()
    }
}

pub trait StaticTopTreeMonoid {
    type Path: Clone;
    type Point: Clone;

    fn vertex(i: usize) -> Self::Path;
    fn add_vertex(pt: &Self::Point, i: usize) -> Self::Path;
    fn add_edge(ph: &Self::Path) -> Self::Point;
    fn compress(l: &Self::Path, r: &Self::Path) -> Self::Path;
    fn rake(l: &Self::Point, r: &Self::Point) -> Self::Point;
}

pub struct DynamicTreeDp<'a, M: StaticTopTreeMonoid> {
    stt: &'a StaticTopTree,
    pub path: Vec<Option<M::Path>>,
    pub point: Vec<Option<M::Point>>,
}

impl<'a, M: StaticTopTreeMonoid> DynamicTreeDp<'a, M> {
    pub fn new(stt: &'a StaticTopTree) -> Self {
        let mut dp = Self {
            stt,
            path: vec![None; stt.p.len()],
            point: vec![None; stt.p.len()],
        };
        dp.update_dfs(stt.root);
        dp
    }

    fn update_dfs(&mut self, u: usize) {
        if u == usize::MAX {
            return;
        }
        if self.stt.l[u] != usize::MAX {
            self.update_dfs(self.stt.l[u]);
        }
        if self.stt.r[u] != usize::MAX {
            self.update_dfs(self.stt.r[u]);
        }
        self.update(u);
    }

    pub fn update(&mut self, u: usize) {
        let l = self.stt.l[u];
        let r = self.stt.r[u];
        match self.stt.typ[u] {
            StaticTopTreeNodeType::Vertex => {
                self.path[u] = Some(M::vertex(u));
            }
            StaticTopTreeNodeType::AddVertex => {
                if let Some(p_val) = &self.point[l] {
                    self.path[u] = Some(M::add_vertex(p_val, u));
                }
            }
            StaticTopTreeNodeType::AddEdge => {
                if let Some(path_val) = &self.path[l] {
                    self.point[u] = Some(M::add_edge(path_val));
                }
            }
            StaticTopTreeNodeType::Compress => {
                if let (Some(lp), Some(rp)) = (&self.path[l], &self.path[r]) {
                    self.path[u] = Some(M::compress(lp, rp));
                }
            }
            StaticTopTreeNodeType::Rake => {
                if let (Some(lp), Some(rp)) = (&self.point[l], &self.point[r]) {
                    self.point[u] = Some(M::rake(lp, rp));
                }
            }
        }
    }

    pub fn prod(&self) -> &M::Path {
        self.path[self.stt.root].as_ref().unwrap()
    }
}

// TODO: dyanmic rerooting tree DP structure
// https://maspypy.github.io/library/graph/ds/dynamic_tree_dp.hpp
// https://maspypy.github.io/library/graph/ds/dynamic_rerooting_tree_dp.hpp

pub trait RerootTreeDpTrait {
    type X: Clone;
    fn vertex(i: usize) -> Self::X;
    fn vertex2(i: usize) -> Self::X;
    fn add_vertex(x: &Self::X, i: usize) -> Self::X;
    fn add_edge(x: &Self::X) -> Self::X;
    fn rake(l: &Self::X, r: &Self::X) -> Self::X;
    fn compress(l: &Self::X, r: &Self::X) -> Self::X;
    fn add_vertex2(x: &Self::X, i: usize) -> Self::X;
    fn add_edge2(x: &Self::X) -> Self::X;
    fn rake2(l: &Self::X, r: &Self::X) -> Self::X;
    fn compress2(l: &Self::X, r: &Self::X) -> Self::X;
    fn compress3(l: &Self::X, r: &Self::X) -> Self::X;
}

pub struct DynamicRerootingTreeDp<'a, M: RerootTreeDpTrait> {
    stt: &'a StaticTopTree,
    dp: Vec<(M::X, M::X)>,
}

impl<'a, M: RerootTreeDpTrait> DynamicRerootingTreeDp<'a, M> {
    pub fn new(stt: &'a StaticTopTree) -> Self {
        let dummy = (M::vertex(0), M::vertex2(0));
        let mut dp = Self {
            stt,
            dp: vec![dummy; stt.p.len()],
        };
        dp.dfs_update(stt.root);
        dp
    }

    fn dfs_update(&mut self, u: usize) {
        if u == usize::MAX {
            return;
        }
        if self.stt.l[u] != usize::MAX {
            self.dfs_update(self.stt.l[u]);
        }
        if self.stt.r[u] != usize::MAX {
            self.dfs_update(self.stt.r[u]);
        }
        self.update(u);
    }

    fn update(&mut self, i: usize) {
        let l = self.stt.l[i];
        let r = self.stt.r[i];
        match self.stt.typ[i] {
            StaticTopTreeNodeType::Vertex => {
                self.dp[i] = (M::vertex(i), M::vertex2(i));
            }
            StaticTopTreeNodeType::AddVertex => {
                let (l0, l1) = &self.dp[l];
                self.dp[i] = (M::add_vertex(l0, i), M::add_vertex2(l1, i));
            }
            StaticTopTreeNodeType::AddEdge => {
                let (l0, l1) = &self.dp[l];
                self.dp[i] = (M::add_edge(l0), M::add_edge2(l1));
            }
            StaticTopTreeNodeType::Compress => {
                let (l1, l2) = &self.dp[l];
                let (r1, r2) = &self.dp[r];
                self.dp[i] = (M::compress(l1, r1), M::compress2(r2, l2));
            }
            StaticTopTreeNodeType::Rake => {
                let (l1, l2) = &self.dp[l];
                let (r1, _r2) = &self.dp[r];
                self.dp[i] = (M::rake(l1, r1), M::compress3(l2, r1));
            }
        }
    }

    pub fn prod_all(&self, v: usize) -> M::X {
        let mut i = v;
        let mut a = Some(self.dp[i].1.clone());
        let mut b: Option<M::X> = None;
        let mut c: Option<M::X> = None;
        while i != usize::MAX {
            let p = self.stt.p[i];
            if p == usize::MAX {
                break;
            }
            let l = self.stt.l[p];
            let r = self.stt.r[p];
            match self.stt.typ[p] {
                StaticTopTreeNodeType::Vertex => unreachable!(),
                StaticTopTreeNodeType::Compress => {
                    if l == i {
                        let r_fi = &self.dp[r].0;
                        b = Some(match b {
                            None => r_fi.clone(),
                            Some(val) => M::compress(&val, r_fi),
                        });
                    } else {
                        let l_se = &self.dp[l].1;
                        a = Some(match a {
                            None => l_se.clone(),
                            Some(val) => M::compress2(&val, l_se),
                        });
                    }
                }
                StaticTopTreeNodeType::Rake => {
                    if l == i {
                        if a.is_none() {
                            let r_fi = &self.dp[r].0;
                            b = Some(match b {
                                None => r_fi.clone(),
                                Some(val) => M::rake(&val, r_fi),
                            });
                        } else {
                            let r_fi = &self.dp[r].0;
                            a = Some(M::compress3(a.as_ref().unwrap(), r_fi));
                        }
                    } else {
                        if a.is_none() {
                            if let Some(cur_c) = c {
                                if let Some(cur_b) = b {
                                    c = Some(M::compress3(&cur_c, &cur_b));
                                } else {
                                    c = Some(cur_c);
                                }
                            }
                            b = Some(self.dp[l].0.clone());
                        } else {
                            if let Some(val_b) = b {
                                a = Some(M::rake2(a.as_ref().unwrap(), &val_b));
                            }
                            c = match c {
                                None => a.clone(),
                                Some(val_c) => Some(M::compress2(&val_c, a.as_ref().unwrap())),
                            };
                            a = None;
                            b = Some(self.dp[l].0.clone());
                        }
                    }
                }
                StaticTopTreeNodeType::AddVertex => {
                    if let Some(val_a) = a {
                        a = Some(M::add_vertex2(&val_a, p));
                    }
                    if let Some(val_b) = b {
                        b = Some(M::add_vertex(&val_b, p));
                    }
                    if let Some(val_c) = c {
                        c = Some(M::add_vertex(&val_c, p));
                    }
                }
                StaticTopTreeNodeType::AddEdge => {
                    if let Some(val_a) = a {
                        a = Some(M::add_edge2(&val_a));
                    }
                    // Update siblings (b, c)
                    if let Some(val_b) = b {
                        b = Some(M::add_edge(&val_b));
                    }
                    if let Some(val_c) = c {
                        c = Some(M::add_edge(&val_c));
                    }
                }
            }
            i = p;
        }

        if let Some(val_b) = b {
            if let Some(val_a) = a {
                a = Some(M::rake2(&val_a, &val_b));
            }
        }

        if let Some(val_c) = c {
            if let Some(val_a) = a {
                M::compress2(&val_c, &val_a)
            } else {
                val_c
            }
        } else {
            a.unwrap()
        }
    }
}

// TODO: top tree
// https://codeforces.com/blog/entry/103726
// https://codeforces.com/blog/entry/128556
// https://blog.niuez.net/cp-cpp-library/data_structures/trees/toptree.html
// https://judge.yosupo.jp/submission/205066

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

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[derive(Clone, Debug, PartialEq)]
//     struct SizeData {
//         sz: usize,
//     }

//     struct TreeSize;
//     impl RerootTreeDpTrait for TreeSize {
//         type X = SizeData;
//         fn vertex(_: usize) -> SizeData {
//             SizeData { sz: 1 }
//         }
//         fn vertex2(_: usize) -> SizeData {
//             SizeData { sz: 1 }
//         }
//         fn add_vertex(x: &SizeData, _: usize) -> SizeData {
//             SizeData { sz: x.sz + 1 }
//         }
//         fn add_edge(x: &SizeData) -> SizeData {
//             SizeData { sz: x.sz }
//         }
//         fn rake(l: &SizeData, r: &SizeData) -> SizeData {
//             SizeData { sz: l.sz + r.sz }
//         }
//         fn compress(l: &SizeData, r: &SizeData) -> SizeData {
//             SizeData { sz: l.sz + r.sz }
//         }
//         fn add_vertex2(x: &SizeData, _: usize) -> SizeData {
//             SizeData { sz: x.sz + 1 }
//         }
//         fn add_edge2(x: &SizeData) -> SizeData {
//             SizeData { sz: x.sz }
//         }
//         fn rake2(l: &SizeData, r: &SizeData) -> SizeData {
//             SizeData { sz: l.sz + r.sz }
//         }
//         fn compress2(l: &SizeData, r: &SizeData) -> SizeData {
//             SizeData { sz: l.sz + r.sz }
//         }
//         fn compress3(l: &SizeData, r: &SizeData) -> SizeData {
//             SizeData { sz: l.sz + r.sz }
//         }
//     }

//     #[derive(Clone, Debug, PartialEq)]
//     struct DistData {
//         sz: usize,
//         sum: usize,
//         len: usize,
//     }

//     struct TreeDist;
//     impl RerootTreeDpTrait for TreeDist {
//         type X = DistData;

//         fn vertex(_: usize) -> DistData {
//             DistData {
//                 sz: 1,
//                 sum: 0,
//                 len: 0,
//             }
//         }
//         fn vertex2(_: usize) -> DistData {
//             DistData {
//                 sz: 1,
//                 sum: 0,
//                 len: 0,
//             }
//         }

//         fn add_vertex(x: &DistData, _: usize) -> DistData {
//             DistData {
//                 sz: x.sz + 1,
//                 sum: x.sum,
//                 len: x.len,
//             }
//         }

//         fn add_edge(x: &DistData) -> DistData {
//             // Edge weight 1.
//             DistData {
//                 sz: x.sz,
//                 sum: x.sum + x.sz,
//                 len: x.len + 1,
//             }
//         }

//         fn rake(l: &DistData, r: &DistData) -> DistData {
//             DistData {
//                 sz: l.sz + r.sz,
//                 sum: l.sum + r.sum,
//                 len: l.len,
//             }
//         }

//         // Implicit edge of weight 1 between L and R in heavy path
//         fn compress(l: &DistData, r: &DistData) -> DistData {
//             DistData {
//                 sz: l.sz + r.sz,
//                 sum: l.sum + r.sum + (r.sz * (l.len + 1)),
//                 len: l.len + r.len + 1,
//             }
//         }

//         fn add_vertex2(x: &DistData, _: usize) -> DistData {
//             DistData {
//                 sz: x.sz + 1,
//                 sum: x.sum,
//                 len: x.len,
//             }
//         }
//         fn add_edge2(x: &DistData) -> DistData {
//             DistData {
//                 sz: x.sz,
//                 sum: x.sum + x.sz,
//                 len: x.len + 1,
//             }
//         }
//         fn rake2(l: &DistData, r: &DistData) -> DistData {
//             DistData {
//                 sz: l.sz + r.sz,
//                 sum: l.sum + r.sum,
//                 len: l.len,
//             }
//         }

//         fn compress2(l: &DistData, r: &DistData) -> DistData {
//             DistData {
//                 sz: l.sz + r.sz,
//                 sum: l.sum + r.sum + (r.sz * (l.len + 1)),
//                 len: l.len + r.len + 1,
//             }
//         }

//         fn compress3(l: &DistData, r: &DistData) -> DistData {
//             DistData {
//                 sz: l.sz + r.sz,
//                 sum: l.sum + r.sum + (r.sz * l.len),
//                 len: l.len,
//             }
//         }
//     }

//     #[test]
//     fn test_reroot_chain_dist() {
//         // Chain 0-1-2-3
//         let parent = vec![0, 0, 1, 2];
//         let stt = StaticTopTree::new(&parent);
//         let dp = DynamicRerootingTreeDp::<TreeDist>::new(&stt);
//         assert_eq!(dp.prod_all(0).sum, 6);
//         assert_eq!(dp.prod_all(1).sum, 4);
//         assert_eq!(dp.prod_all(2).sum, 4);
//         assert_eq!(dp.prod_all(3).sum, 6);
//     }

//     #[test]
//     fn test_reroot_star_dist() {
//         // Star 1 center
//         let parent = vec![0, 0, 0, 0];
//         let stt = StaticTopTree::new(&parent);
//         let dp = DynamicRerootingTreeDp::<TreeDist>::new(&stt);
//         assert_eq!(dp.prod_all(0).sum, 3);
//         assert_eq!(dp.prod_all(1).sum, 5);
//     }
// }
