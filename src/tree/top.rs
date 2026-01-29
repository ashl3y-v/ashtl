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

pub trait TopTreeMonoid {
    type Path: Clone;
    type Point: Clone;

    fn vertex(i: usize) -> Self::Path;
    fn add_vertex(pt: &Self::Point, i: usize) -> Self::Path;
    fn add_edge(ph: &Self::Path) -> Self::Point;
    fn compress(l: &Self::Path, r: &Self::Path) -> Self::Path;
    fn rake(l: &Self::Point, r: &Self::Point) -> Self::Point;
}

pub struct DynamicTreeDp<'a, M: TopTreeMonoid> {
    stt: &'a StaticTopTree,
    pub path: Vec<Option<M::Path>>,
    pub point: Vec<Option<M::Point>>,
}

impl<'a, M: TopTreeMonoid> DynamicTreeDp<'a, M> {
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

// TODO: top tree
// https://codeforces.com/blog/entry/103726
// https://codeforces.com/blog/entry/128556
// https://blog.niuez.net/cp-cpp-library/data_structures/trees/toptree.html
// https://judge.yosupo.jp/submission/205066

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
                    // Update siblings (b, c) too because they are passing through the wrapper
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

// ==========================================================
// Tests
// ==========================================================
#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    struct SizeData {
        sz: usize,
    }

    struct TreeSize;
    impl RerootTreeDpTrait for TreeSize {
        type X = SizeData;
        fn vertex(_: usize) -> SizeData {
            SizeData { sz: 1 }
        }
        fn vertex2(_: usize) -> SizeData {
            SizeData { sz: 1 }
        }
        fn add_vertex(x: &SizeData, _: usize) -> SizeData {
            SizeData { sz: x.sz + 1 }
        }
        fn add_edge(x: &SizeData) -> SizeData {
            SizeData { sz: x.sz }
        }
        fn rake(l: &SizeData, r: &SizeData) -> SizeData {
            SizeData { sz: l.sz + r.sz }
        }
        fn compress(l: &SizeData, r: &SizeData) -> SizeData {
            SizeData { sz: l.sz + r.sz }
        }
        fn add_vertex2(x: &SizeData, _: usize) -> SizeData {
            SizeData { sz: x.sz + 1 }
        }
        fn add_edge2(x: &SizeData) -> SizeData {
            SizeData { sz: x.sz }
        }
        fn rake2(l: &SizeData, r: &SizeData) -> SizeData {
            SizeData { sz: l.sz + r.sz }
        }
        fn compress2(l: &SizeData, r: &SizeData) -> SizeData {
            SizeData { sz: l.sz + r.sz }
        }
        fn compress3(l: &SizeData, r: &SizeData) -> SizeData {
            SizeData { sz: l.sz + r.sz }
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    struct DistData {
        sz: usize,
        sum: usize,
        len: usize,
    }

    struct TreeDist;
    impl RerootTreeDpTrait for TreeDist {
        type X = DistData;

        fn vertex(_: usize) -> DistData {
            DistData {
                sz: 1,
                sum: 0,
                len: 0,
            }
        }
        fn vertex2(_: usize) -> DistData {
            DistData {
                sz: 1,
                sum: 0,
                len: 0,
            }
        }

        fn add_vertex(x: &DistData, _: usize) -> DistData {
            DistData {
                sz: x.sz + 1,
                sum: x.sum,
                len: x.len,
            }
        }

        fn add_edge(x: &DistData) -> DistData {
            // Edge weight 1.
            DistData {
                sz: x.sz,
                sum: x.sum + x.sz,
                len: x.len + 1,
            }
        }

        fn rake(l: &DistData, r: &DistData) -> DistData {
            DistData {
                sz: l.sz + r.sz,
                sum: l.sum + r.sum,
                len: l.len,
            }
        }

        // Implicit edge of weight 1 between L and R in heavy path
        fn compress(l: &DistData, r: &DistData) -> DistData {
            DistData {
                sz: l.sz + r.sz,
                sum: l.sum + r.sum + (r.sz * (l.len + 1)),
                len: l.len + r.len + 1,
            }
        }

        fn add_vertex2(x: &DistData, _: usize) -> DistData {
            DistData {
                sz: x.sz + 1,
                sum: x.sum,
                len: x.len,
            }
        }
        fn add_edge2(x: &DistData) -> DistData {
            DistData {
                sz: x.sz,
                sum: x.sum + x.sz,
                len: x.len + 1,
            }
        }
        fn rake2(l: &DistData, r: &DistData) -> DistData {
            DistData {
                sz: l.sz + r.sz,
                sum: l.sum + r.sum,
                len: l.len,
            }
        }

        fn compress2(l: &DistData, r: &DistData) -> DistData {
            DistData {
                sz: l.sz + r.sz,
                sum: l.sum + r.sum + (r.sz * (l.len + 1)),
                len: l.len + r.len + 1,
            }
        }

        fn compress3(l: &DistData, r: &DistData) -> DistData {
            DistData {
                sz: l.sz + r.sz,
                sum: l.sum + r.sum + (r.sz * l.len),
                len: l.len,
            }
        }
    }

    #[test]
    fn test_reroot_chain_dist() {
        // Chain 0-1-2-3
        let parent = vec![0, 0, 1, 2];
        let stt = StaticTopTree::new(&parent);
        let dp = DynamicRerootingTreeDp::<TreeDist>::new(&stt);
        assert_eq!(dp.prod_all(0).sum, 6);
        assert_eq!(dp.prod_all(1).sum, 4);
        assert_eq!(dp.prod_all(2).sum, 4);
        assert_eq!(dp.prod_all(3).sum, 6);
    }

    #[test]
    fn test_reroot_star_dist() {
        // Star 1 center
        let parent = vec![0, 0, 0, 0];
        let stt = StaticTopTree::new(&parent);
        let dp = DynamicRerootingTreeDp::<TreeDist>::new(&stt);
        assert_eq!(dp.prod_all(0).sum, 3);
        assert_eq!(dp.prod_all(1).sum, 5);
    }
}
