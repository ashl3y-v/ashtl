use std::ops::{AddAssign, SubAssign};

use crate::ds::bit_vec::BitVec;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PushRelabelEdge<F> {
    pub to: usize,
    pub rev: usize,
    pub f: F,
    pub c: F,
}

pub struct PushRelabel<F> {
    pub n: usize,
    pub g: Vec<Vec<PushRelabelEdge<F>>>,
    pub ec: Vec<F>,
    pub cur: Vec<usize>,
    pub hs: Vec<Vec<usize>>,
    pub h: Vec<usize>,
    pub co: Vec<usize>,
}

impl<F: Copy + Default + PartialOrd + AddAssign + SubAssign> PushRelabel<F> {
    #[inline]
    pub fn new(n: usize) -> Self {
        Self {
            n,
            g: vec![Vec::new(); n],
            ec: vec![F::default(); n],
            cur: vec![0; n],
            hs: vec![Vec::new(); 2 * n],
            h: vec![0; n],
            co: vec![0; 2 * n],
        }
    }

    #[inline]
    pub fn reset(&mut self) -> &mut Self {
        self.ec.fill(F::default());
        self.cur.fill(0);
        self.hs.iter_mut().for_each(Vec::clear);
        self.h.fill(0);
        self.co.fill(0);
        self.g
            .iter_mut()
            .flatten()
            .for_each(|PushRelabelEdge { f, c, .. }| {
                *c += *f;
                *f = F::default();
            });
        self
    }

    #[inline]
    pub fn full_reset(&mut self) -> &mut Self {
        self.g.iter_mut().for_each(Vec::clear);
        self.ec.fill(F::default());
        self.cur.fill(0);
        self.hs.iter_mut().for_each(Vec::clear);
        self.h.fill(0);
        self.co.fill(0);
        self
    }

    #[inline]
    pub fn add_edge(&mut self, s: usize, t: usize, cap: F, rcap: F) -> &mut Self {
        if s == t {
            return self;
        }
        let back_s = self.g[t].len();
        let back_t = self.g[s].len();
        self.g[s].push(PushRelabelEdge {
            to: t,
            rev: back_s,
            f: F::default(),
            c: cap,
        });
        self.g[t].push(PushRelabelEdge {
            to: s,
            rev: back_t,
            f: F::default(),
            c: rcap,
        });
        self
    }

    fn push(&mut self, u: usize, ei: usize, f: F, t: usize) -> &mut Self {
        let v = self.g[u][ei].to;
        let back_idx = self.g[u][ei].rev;
        if v != t && self.ec[v] == F::default() && f > F::default() {
            self.hs[self.h[v]].push(v);
        }
        let e = &mut self.g[u][ei];
        e.f += f;
        e.c -= f;
        self.ec[v] += f;
        let be = &mut self.g[v][back_idx];
        be.f -= f;
        be.c += f;
        self.ec[be.to] -= f;
        self
    }

    #[inline]
    fn relabel(&mut self, u: usize, hi: usize) -> usize {
        let n = self.n;
        let mut nh = usize::MAX;
        let mut nc = 0;
        let ws = &self.g[u];
        for i in 0..self.g[u].len() {
            let PushRelabelEdge { to: w, c, .. } = ws[i];
            let cand = self.h[w] + 1;
            if c > F::default() && cand < nh {
                nh = cand;
                nc = i;
            }
        }
        self.h[u] = nh;
        self.cur[u] = nc;
        self.co[nh] += 1;
        self.co[hi] -= 1;
        if hi < n && self.co[hi] == 0 {
            for i in 0..n {
                if self.h[i] > hi && self.h[i] < n {
                    self.co[self.h[i]] = 0;
                    self.h[i] = n + 1;
                }
            }
        }
        return self.h[u];
    }

    /// O(n^2 √m)
    pub fn calc(&mut self, s: usize, t: usize) -> F {
        if s == t {
            return F::default();
        }
        let n = self.n;
        self.h[s] = n;
        self.co[0] = n - 1;
        for ei in 0..self.g[s].len() {
            let cap = self.g[s][ei].c;
            if cap > F::default() {
                self.push(s, ei, cap, t);
            }
        }
        let mut hi = 0;
        loop {
            while self.hs[hi].is_empty() {
                if hi == 0 {
                    return self.ec[t];
                }
                hi -= 1;
            }
            let u = unsafe { self.hs[hi].pop().unwrap_unchecked() };
            while self.ec[u] > F::default() {
                if self.cur[u] == self.g[u].len() {
                    hi = self.relabel(u, hi);
                } else {
                    let i = self.cur[u];
                    let PushRelabelEdge { to: w, c, .. } = self.g[u][i];
                    if c > F::default() && self.h[u] == self.h[w] + 1 {
                        let v = if self.ec[u] < c { self.ec[u] } else { c };
                        self.push(u, i, v, t);
                    } else {
                        self.cur[u] += 1;
                    }
                }
            }
        }
    }

    pub fn left_of_min_cut(&self, a: usize) -> bool {
        self.h[a] >= self.n
    }

    pub fn flows(&self) -> Vec<(usize, usize, F)> {
        self.g
            .iter()
            .enumerate()
            .flat_map(|(u, edges)| {
                edges
                    .iter()
                    .filter(|e| e.f > F::default())
                    .map(move |e| (u, e.to, e.f))
            })
            .collect()
    }

    /// O(F (n + m))
    pub fn path_decomposition(&self, s: usize, t: usize, one: F) -> Vec<Vec<usize>> {
        let mut adj: Vec<Vec<(usize, F)>> = vec![Vec::new(); self.n];
        let zero = F::default();
        for (u, edges) in self.g.iter().enumerate() {
            for e in edges {
                if e.f > zero {
                    adj[u].push((e.to, e.f));
                }
            }
        }
        let mut paths = Vec::new();
        let mut vis = BitVec::new(self.n, false);
        loop {
            while let Some((_, flow)) = adj[s].last() {
                if *flow <= zero {
                    adj[s].pop();
                } else {
                    break;
                }
            }
            if adj[s].is_empty() {
                break;
            }
            let mut path = vec![s];
            vis.set(s, true);
            while *path.last().unwrap() != t {
                let u = *path.last().unwrap();
                let mut next_v = None;
                while let Some((v, flow)) = adj[u].last_mut() {
                    if *flow <= zero {
                        adj[u].pop();
                        continue;
                    }
                    *flow -= one;
                    next_v = Some(*v);
                    break;
                }
                if let Some(v) = next_v {
                    while vis[v] {
                        vis.set(path.pop().unwrap(), false);
                    }
                    path.push(v);
                    vis.set(v, true);
                } else {
                    break;
                }
            }
            for &v in &path {
                vis.set(v, false);
            }
            paths.push(path);
        }
        paths
    }
}

// TODO: cost scaling min-cost max flow
// https://koosaga.com/289
// https://ideone.com/q6PWgB
// https://codeforces.com/blog/entry/104075
// https://codeforces.com/blog/entry/95823
// https://developers.google.com/optimization/reference/graph/min_cost_flow
// https://www.cs.cmu.edu/~avrim/451f13/lectures/lect1010.pdf
// https://ocw.mit.edu/courses/6-854j-advanced-algorithms-fall-2005/b312c6aa208fc322bab7654e55c0ab01_lec14_1999.pdf
// https://people.orie.cornell.edu/dpw/orie633/LectureNotes/lecture14.pdf

pub struct CostScaling {}

// TODO: min cost b-flow using network simplex
// https://judge.yosupo.jp/submission/313861
