#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeType {
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
    pub typ: Vec<NodeType>,
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
            typ: vec![NodeType::Vertex; n],
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

    fn add(&mut self, k: usize, l: usize, r: usize, t: NodeType) -> usize {
        let v = if k == usize::MAX { self.p.len() } else { k };
        if v >= self.p.len() {
            self.p.resize(v + 1, usize::MAX);
            self.l.resize(v + 1, usize::MAX);
            self.r.resize(v + 1, usize::MAX);
            self.typ.resize(v + 1, NodeType::Vertex);
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

    fn merge(&mut self, items: &[(usize, usize)], t: NodeType) -> (usize, usize) {
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
        self.merge(&chs, NodeType::Compress)
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
            self.merge(&chs, NodeType::Rake)
        }
    }

    fn add_edge(&mut self, adj: &[Vec<usize>], i: usize) -> (usize, usize) {
        let (j, sj) = self.compress(adj, i);
        (self.add(usize::MAX, j, usize::MAX, NodeType::AddEdge), sj)
    }

    fn add_vertex(&mut self, adj: &[Vec<usize>], i: usize) -> (usize, usize) {
        let (j, sj) = self.rake(adj, i);
        let t = if j == usize::MAX {
            NodeType::Vertex
        } else {
            NodeType::AddVertex
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
            NodeType::Vertex => v(k),
            NodeType::AddVertex => {
                let raked = if self.l[k] == usize::MAX {
                    id.clone()
                } else {
                    self.point(self.l[k], v, cmpr, rake, add_e, add_v, id)
                };
                add_v(raked, k)
            }
            NodeType::Compress => {
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
            NodeType::Rake => {
                let lpt = self.point(self.l[k], v, cmpr, rake, add_e, add_v, id);
                let rpt = self.point(self.r[k], v, cmpr, rake, add_e, add_v, id);
                rake(lpt, rpt)
            }
            NodeType::AddEdge => {
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
                NodeType::Vertex => {
                    path[k] = v(k);
                }
                NodeType::AddVertex => {
                    let raked = if self.l[k] == usize::MAX {
                        id.clone()
                    } else {
                        pt[self.l[k]].clone()
                    };
                    path[k] = add_v(&raked, k);
                }
                NodeType::Compress => {
                    path[k] = cmpr(&path[self.l[k]], &path[self.r[k]]);
                }
                NodeType::Rake => {
                    pt[k] = rake(&pt[self.l[k]], &pt[self.r[k]]);
                }
                NodeType::AddEdge => {
                    pt[k] = add_e(&path[self.l[k]]);
                }
            }
            k = self.p[k];
        }
    }

    pub fn len(&self) -> usize {
        self.p.len()
    }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }
}

// TODO: dyanmic (rerooting) tree DP structure
// https://maspypy.github.io/library/graph/ds/dynamic_tree_dp.hpp
// https://maspypy.github.io/library/graph/ds/dynamic_rerooting_tree_dp.hpp

// TODO: top tree
// https://codeforces.com/blog/entry/103726
// https://codeforces.com/blog/entry/128556
// https://blog.niuez.net/cp-cpp-library/data_structures/trees/toptree.html
