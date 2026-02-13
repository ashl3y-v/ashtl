use std::collections::BinaryHeap;
use std::ops::{Add, Neg, Sub};

use crate::ds::score::MinScore;

const INF: i64 = i64::MAX / 2;

pub trait Weight:
    Copy + Neg<Output = Self> + Add<Output = Self> + Sub<Output = Self> + PartialOrd + Default
{
    fn max() -> Self;
}

impl Weight for i64 {
    fn max() -> Self {
        INF
    }
}

pub trait MatroidRmAdd {
    fn size(&self) -> usize;

    fn prepare(&mut self, i: &[bool]);

    fn can_add(&self, i: usize) -> bool;

    fn for_rm_add(&self, i: usize, f: impl FnMut(usize));
}

pub trait MatroidAddRm {
    fn size(&self) -> usize;

    fn prepare(&mut self, i: &[bool]);

    fn can_add(&self, i: usize) -> bool;

    fn for_add_rm(&self, i: usize, f: impl FnMut(usize));
}

pub struct MatroidIntersection {
    par: Vec<Option<usize>>,
    dist: Vec<usize>,
    que: Vec<usize>,
}

impl MatroidIntersection {
    pub fn new(n: usize) -> Self {
        Self {
            par: vec![None; n],
            dist: vec![usize::MAX; n],
            que: Vec::with_capacity(n),
        }
    }

    /// O(r n T_ind)
    pub fn step<M1, M2>(&mut self, m1: &mut M1, m2: &mut M2, i: &mut [bool]) -> bool
    where
        M1: MatroidRmAdd,
        M2: MatroidAddRm,
    {
        let n = i.len();
        assert_eq!(n, m1.size());
        assert_eq!(n, m2.size());
        m1.prepare(i);
        m2.prepare(i);
        self.dist.fill(usize::MAX);
        self.par.fill(None);
        self.que.clear();
        for v in 0..n {
            if !i[v] && m1.can_add(v) {
                self.dist[v] = 0;
                self.que.push(v);
            }
        }
        let mut ql = 0;
        let mut t = None;
        while ql < self.que.len() {
            let v = self.que[ql];
            ql += 1;
            if !i[v] && m2.can_add(v) {
                t = Some(v);
                break;
            }
            if i[v] {
                m1.for_rm_add(v, |w| {
                    if self.dist[w] == usize::MAX {
                        self.dist[w] = self.dist[v] + 1;
                        self.par[w] = Some(v);
                        self.que.push(w);
                    }
                });
            } else {
                m2.for_add_rm(v, |w| {
                    if self.dist[w] == usize::MAX {
                        self.dist[w] = self.dist[v] + 1;
                        self.par[w] = Some(v);
                        self.que.push(w);
                    }
                });
            }
        }
        let Some(t) = t else {
            return false;
        };
        let mut v = t;
        loop {
            i[v] = !i[v];
            match self.par[v] {
                Some(p) => v = p,
                None => break,
            }
        }
        true
    }
}

pub struct WeightedMatroidIntersection<W> {
    weight: Vec<W>,
    pt: Vec<W>,
    dist: Vec<(W, usize)>,
    par: Vec<Option<usize>>,
}

impl<W: Weight> WeightedMatroidIntersection<W> {
    pub fn new(weight: Vec<W>) -> Self {
        let n = weight.len();
        Self {
            pt: vec![W::default(); n],
            dist: vec![(W::default(), usize::MAX); n],
            par: vec![None; n],
            weight,
        }
    }

    /// O(r^2 n (T_ind + log n))
    pub fn calc<M1, M2>(&mut self, m1: &mut M1, m2: &mut M2) -> Vec<bool>
    where
        M1: MatroidRmAdd,
        M2: MatroidAddRm,
    {
        let n = self.weight.len();
        let mut i = vec![false; n];
        loop {
            let gain = self.augment(m1, m2, &mut i);
            if gain <= W::default() {
                break;
            }
        }
        i
    }

    /// O(r n (T_ind + log n))
    pub fn step<M1, M2>(&mut self, m1: &mut M1, m2: &mut M2, wt: &mut W, i: &mut [bool]) -> bool
    where
        M1: MatroidRmAdd,
        M2: MatroidAddRm,
    {
        let n = self.weight.len();
        assert_eq!(n, i.len());
        assert_eq!(n, m1.size());
        assert_eq!(n, m2.size());
        let delta = self.augment(m1, m2, i);
        *wt = *wt + delta;
        delta > W::default()
    }

    fn augment<M1, M2>(&mut self, m1: &mut M1, m2: &mut M2, i: &mut [bool]) -> W
    where
        M1: MatroidRmAdd,
        M2: MatroidAddRm,
    {
        let n = self.weight.len();
        m1.prepare(i);
        m2.prepare(i);
        self.dist.fill((W::max(), usize::MAX));
        self.par.fill(None);
        let mut heap: BinaryHeap<MinScore<(W, usize), usize>> = BinaryHeap::new();
        for v in 0..n {
            if !i[v] && m1.can_add(v) {
                self.dist[v] = (-self.weight[v] - self.pt[v], 0);
                heap.push(MinScore(self.dist[v], v));
            }
        }
        let mut best = (W::max(), usize::MAX);
        let mut t = None::<usize>;
        while let Some(MinScore(d_tuple, v)) = heap.pop() {
            if d_tuple != self.dist[v] {
                continue;
            }
            let (d, hops) = d_tuple;
            if m2.can_add(v) {
                let cand = (d + self.pt[v], hops);
                if cand < best {
                    best = cand;
                    t = Some(v);
                }
            }
            if i[v] {
                m1.for_rm_add(v, |w| {
                    let x = self.pt[v] - self.weight[w] - self.pt[w];
                    let new_dist = (d + x, hops + 1);
                    if x >= W::default() && new_dist < self.dist[w] {
                        self.dist[w] = new_dist;
                        self.par[w] = Some(v);
                        heap.push(MinScore(self.dist[w], w));
                    }
                });
            } else {
                m2.for_add_rm(v, |w| {
                    let x = self.weight[w] + self.pt[v] - self.pt[w];
                    let new_dist = (d + x, hops + 1);
                    if x >= W::default() && new_dist < self.dist[w] {
                        self.dist[w] = new_dist;
                        self.par[w] = Some(v);
                        heap.push(MinScore(self.dist[w], w));
                    }
                });
            }
        }
        let Some(t) = t else {
            return W::default();
        };
        let ans = -self.pt[t] - self.dist[t].0;
        for v in 0..n {
            if self.dist[v].0 < W::max() {
                self.pt[v] = self.pt[v] + self.dist[v].0;
            }
        }
        let mut w1 = vec![W::default(); n];
        let mut w2 = vec![W::default(); n];
        for v in 0..n {
            if i[v] {
                w1[v] = self.pt[v];
                w2[v] = self.weight[v] - self.pt[v];
            } else {
                w1[v] = self.weight[v] + self.pt[v];
                w2[v] = -self.pt[v];
            }
        }
        let mut v = t;
        loop {
            i[v] = !i[v];
            match self.par[v] {
                Some(p) => v = p,
                None => break,
            }
        }
        for v in 0..n {
            self.pt[v] = if i[v] { w1[v] } else { -w2[v] };
        }
        ans
    }
}

pub struct GraphicMatroid {
    n: usize,
    edges: Vec<(usize, usize)>,
    root: Vec<usize>,
    dep: Vec<usize>,
    par: Vec<usize>,
    que: Vec<usize>,
    i_ref: Option<Box<[bool]>>,
}

impl GraphicMatroid {
    pub fn new(n: usize, edges: Vec<(usize, usize)>) -> Self {
        Self {
            n,
            edges,
            root: vec![0; n],
            dep: vec![0; n],
            par: vec![usize::MAX; n],
            que: vec![0; n],
            i_ref: None,
        }
    }

    fn bfs(&mut self, s: usize) {
        let i = self.i_ref.as_ref().unwrap();
        let mut ql = 0;
        let mut qr = 0;
        self.root[s] = s;
        self.dep[s] = 0;
        self.par[s] = usize::MAX;
        self.que[qr] = s;
        qr += 1;
        while ql < qr {
            let v = self.que[ql];
            ql += 1;
            for (eid, &(a, b)) in self.edges.iter().enumerate() {
                if !i[eid] {
                    continue;
                }
                let to = if a == v {
                    b
                } else if b == v {
                    a
                } else {
                    continue;
                };
                if self.root[to] == usize::MAX {
                    self.root[to] = s;
                    self.dep[to] = self.dep[v] + 1;
                    self.par[to] = eid;
                    self.que[qr] = to;
                    qr += 1;
                }
            }
        }
    }
}

impl MatroidAddRm for GraphicMatroid {
    fn size(&self) -> usize {
        self.edges.len()
    }

    fn prepare(&mut self, i: &[bool]) {
        assert_eq!(i.len(), self.edges.len());
        self.i_ref = Some(i.to_vec().into_boxed_slice());
        self.root.fill(usize::MAX);
        for s in 0..self.n {
            if self.root[s] == usize::MAX {
                self.bfs(s);
            }
        }
    }

    fn can_add(&self, eid: usize) -> bool {
        let (a, b) = self.edges[eid];
        self.root[a] != self.root[b]
    }

    fn for_add_rm(&self, eid: usize, mut f: impl FnMut(usize)) {
        let i = self.i_ref.as_ref().unwrap();
        assert!(!i[eid]);
        let (mut a, mut b) = self.edges[eid];
        if self.root[a] != self.root[b] {
            for j in 0..self.edges.len() {
                if i[j] {
                    f(j);
                }
            }
            return;
        }
        if self.dep[a] > self.dep[b] {
            std::mem::swap(&mut a, &mut b);
        }
        while self.dep[a] < self.dep[b] {
            let j = self.par[b];
            f(j);
            let (x, y) = self.edges[j];
            b = x ^ y ^ b;
        }
        while a != b {
            let j = self.par[a];
            f(j);
            let (x, y) = self.edges[j];
            a = x ^ y ^ a;
            let j = self.par[b];
            f(j);
            let (x, y) = self.edges[j];
            b = x ^ y ^ b;
        }
    }
}

pub struct PartitionMatroid {
    color: Vec<usize>,
    cap: Vec<usize>,
    indptr: Vec<usize>,
    ids: Vec<usize>,
    cnt: Vec<usize>,
    i_ref: Option<Box<[bool]>>,
}

impl PartitionMatroid {
    pub fn new(color: Vec<usize>, cap: Vec<usize>) -> Self {
        let n = color.len();
        let c = cap.len();
        let mut indptr = vec![0; c + 1];
        for i in 0..n {
            let col = color[i];
            indptr[col + 1] += 1;
        }
        for i in 0..c {
            indptr[i + 1] += indptr[i];
        }
        let mut ids = vec![0; n];
        let mut ptr = indptr.clone();
        for i in 0..n {
            let col = color[i];
            ids[ptr[col]] = i;
            ptr[col] += 1;
        }
        for i in (1..=c).rev() {
            indptr[i] = indptr[i - 1];
        }
        indptr[0] = 0;
        Self {
            color,
            cap,
            indptr,
            ids,
            cnt: vec![0; c],
            i_ref: None,
        }
    }
}

impl MatroidRmAdd for PartitionMatroid {
    fn size(&self) -> usize {
        self.color.len()
    }

    fn prepare(&mut self, i: &[bool]) {
        assert_eq!(i.len(), self.color.len());
        self.i_ref = Some(i.to_vec().into_boxed_slice());
        self.cnt.resize(self.cap.len(), 0);
        self.cnt.fill(0);
        for (idx, &in_set) in i.iter().enumerate() {
            if in_set {
                self.cnt[self.color[idx]] += 1;
            }
        }
    }

    fn can_add(&self, idx: usize) -> bool {
        self.cnt[self.color[idx]] < self.cap[self.color[idx]]
    }

    fn for_rm_add(&self, idx: usize, mut f: impl FnMut(usize)) {
        let i = self.i_ref.as_ref().unwrap();
        assert!(i[idx]);
        let c = self.color[idx];
        if self.cnt[c] < self.cap[c] {
            return;
        }
        for k in self.indptr[c]..self.indptr[c + 1] {
            let j = self.ids[k];
            if !i[j] {
                f(j);
            }
        }
    }
}
