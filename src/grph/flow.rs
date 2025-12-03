use std::ops::{AddAssign, SubAssign};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<F> {
    pub to: usize,
    pub rev: usize,
    pub f: F,
    pub c: F,
}

pub struct PushRelabel<F> {
    pub n: usize,
    pub g: Vec<Vec<Edge<F>>>,
    pub ec: Vec<F>,
    pub cur: Vec<usize>,
    pub hs: Vec<Vec<usize>>,
    pub h: Vec<usize>,
    pub co: Vec<usize>,
}

impl<F: Copy + Default + Ord + AddAssign + SubAssign> PushRelabel<F> {
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
        self.g.iter_mut().flatten().for_each(|Edge { f, c, .. }| {
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
        self.g[s].push(Edge {
            to: t,
            rev: back_s,
            f: F::default(),
            c: cap,
        });
        self.g[t].push(Edge {
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
            let Edge { to: w, c, .. } = ws[i];
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

    /// O(V^2 √E)
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
                    let Edge { to: w, c, .. } = self.g[u][i];
                    if c > F::default() && self.h[u] == self.h[w] + 1 {
                        self.push(u, i, self.ec[u].min(c), t);
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
}

// TODO: path decomposition
// https://maspypy.github.io/library/flow/maxflow.hpp

// TODO: add dinic's implementation

// TODO: min-cost max flow
// https://koosaga.com/289
// https://ideone.com/q6PWgB
// https://judge.yosupo.jp/submission/218137
// https://codeforces.com/blog/entry/104075
// https://codeforces.com/blog/entry/95823

// TODO: flow with demands
// https://usaco.guide/adv/flow-lb?lang=cpp

// TODO: DAG path cover
// https://maspypy.github.io/library/graph/dag_path_cover.hpp

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_no_edges() {
        let mut fl = PushRelabel::<i64>::new(2);
        assert_eq!(fl.calc(0, 1), 0);
    }

    #[test]
    fn single_edge() {
        let mut fl = PushRelabel::new(2);
        fl.add_edge(0, 1, 7, 0);
        assert_eq!(fl.calc(0, 1), 7);
    }

    #[test]
    fn parallel_edges() {
        let mut fl = PushRelabel::new(3);
        assert_eq!(
            fl.add_edge(0, 1, 3, 0)
                .add_edge(0, 1, 2, 0)
                .add_edge(1, 2, 5, 0)
                .calc(0, 2),
            5
        );
    }

    #[test]
    fn diamond() {
        let mut fl = PushRelabel::new(5);
        fl.add_edge(0, 1, 10, 0)
            .add_edge(1, 4, 10, 0)
            .add_edge(0, 2, 10, 0)
            .add_edge(2, 4, 10, 0)
            .add_edge(1, 2, 1, 0)
            .add_edge(2, 1, 1, 0);
        assert_eq!(fl.calc(0, 4), 20);
    }

    #[test]
    fn bottleneck_paths() {
        let mut fl = PushRelabel::new(6);
        fl.add_edge(0, 1, 5, 0)
            .add_edge(1, 5, 1, 0)
            .add_edge(0, 2, 5, 0)
            .add_edge(2, 5, 2, 0)
            .add_edge(0, 3, 5, 0)
            .add_edge(3, 5, 3, 0);
        assert_eq!(fl.calc(0, 5), 6);
    }

    #[test]
    fn disconnected_and_gap() {
        let mut fl = PushRelabel::new(4);
        fl.add_edge(0, 1, 5, 0)
            .add_edge(1, 3, 0, 0)
            .add_edge(0, 2, 3, 0)
            .add_edge(2, 3, 3, 0);
        assert_eq!(fl.calc(0, 3), 3);
    }

    #[test]
    fn bipartite_matching_4x4() {
        let n = 2 + 4 + 4;
        let s = 0;
        let t = n - 1;
        let mut fl = PushRelabel::new(n);
        for u in 0..4 {
            fl.add_edge(s, 1 + u, 1, 0);
        }
        for i in 0..4 {
            for j in 0..4 {
                if (i + j) % 2 == 0 {
                    fl.add_edge(1 + i, 1 + 4 + j, 1, 0);
                }
            }
        }
        for v in 0..4 {
            fl.add_edge(1 + 4 + v, t, 1, 0);
        }
        assert_eq!(fl.calc(s, t), 4);
    }

    #[test]
    fn long_chain() {
        let n = 101;
        let mut fl = PushRelabel::new(n);
        for i in 0..100 {
            fl.add_edge(i, i + 1, (i + 1) as i64, 0);
        }
        assert_eq!(fl.calc(0, 100), 1);
    }

    #[test]
    fn grid_5x5() {
        let w = 5;
        let h = 5;
        let n = w * h + 2;
        let s = w * h;
        let t = w * h + 1;
        let mut fl = PushRelabel::new(n);
        for c in 0..w {
            fl.add_edge(s, c, 2, 0);
        }
        for c in 0..w {
            fl.add_edge((h - 1) * w + c, t, 2, 0);
        }
        let dirs = [(1, 0), (-1, 0), (0, 1), (0, -1)];
        for r in 0..h {
            for c in 0..w {
                for &(dr, dc) in &dirs {
                    let nr = r as isize + dr;
                    let nc = c as isize + dc;
                    if nr >= 0 && nr < h as isize && nc >= 0 && nc < w as isize {
                        let u = r * w + c;
                        let v = (nr as usize) * w + (nc as usize);
                        fl.add_edge(u, v, 1, 0);
                    }
                }
            }
        }
        let got = fl.calc(s, t);
        assert!(got >= 5 && got <= 10, "unexpected grid flow = {}", got);
    }

    #[test]
    fn self_loops_and_zero_caps() {
        let mut fl = PushRelabel::new(3);
        fl.add_edge(0, 0, 10, 0)
            .add_edge(0, 1, 0, 0)
            .add_edge(0, 2, 5, 0)
            .add_edge(2, 1, 5, 0);
        assert_eq!(fl.calc(0, 1), 5);
    }

    #[test]
    fn complete_graph_4() {
        let n = 4;
        let mut fl = PushRelabel::new(n);
        for u in 0..n {
            for v in 0..n {
                if u != v {
                    fl.add_edge(u, v, 1, 0);
                }
            }
        }
        assert_eq!(fl.calc(0, 3), 3);
    }

    #[test]
    fn small_deterministic_random() {
        let mut fl = PushRelabel::new(7);
        let edges = [
            (0, 1, 3),
            (0, 2, 5),
            (1, 3, 4),
            (2, 3, 2),
            (1, 4, 2),
            (4, 5, 3),
            (5, 3, 1),
            (2, 6, 1),
            (6, 3, 2),
        ];
        for &(u, v, c) in &edges {
            fl.add_edge(u, v, c, 0);
        }
        assert_eq!(fl.calc(0, 3), 6);
    }

    fn max_flow(n: usize, edges: &[(usize, usize, i64, i64)], s: usize, t: usize) -> i64 {
        let mut pr = PushRelabel::new(n);
        for &(u, v, cap, rcap) in edges {
            pr.add_edge(u, v, cap, rcap);
        }
        pr.calc(s, t)
    }

    #[test]
    fn empty_single_node() {
        assert_eq!(max_flow(1, &[], 0, 0), 0);
    }

    #[test]
    fn two_nodes_no_edges() {
        assert_eq!(max_flow(2, &[], 0, 1), 0);
    }

    #[test]
    fn zero_capacity_edge() {
        let edges = &[(0, 1, 0, 0)];
        assert_eq!(max_flow(2, edges, 0, 1), 0);
    }

    #[test]
    fn simple_chain() {
        let edges = &[(0, 1, 5, 0), (1, 2, 6, 0), (2, 3, 7, 0)];
        assert_eq!(max_flow(4, edges, 0, 3), 5);
    }

    #[test]
    fn diamond_structure() {
        let edges = &[(0, 1, 5, 0), (0, 2, 7, 0), (1, 3, 4, 0), (2, 3, 8, 0)];
        assert_eq!(max_flow(4, edges, 0, 3), 11);
    }

    #[test]
    fn disconnected_sink() {
        let edges = &[(0, 1, 5, 0)];
        assert_eq!(max_flow(3, edges, 0, 2), 0);
    }

    #[test]
    fn reverse_capacity_only() {
        let edges = &[(0, 1, 0, 5)];
        assert_eq!(max_flow(2, edges, 0, 1), 0);
    }

    #[test]
    fn small_cycle_with_two_exits() {
        let edges = &[
            (0, 1, 10, 0),
            (1, 2, 5, 0),
            (2, 1, 0, 0),
            (1, 3, 3, 0),
            (2, 3, 7, 0),
        ];
        assert_eq!(max_flow(4, edges, 0, 3), 8);
    }

    #[test]
    fn cross_edge_enhancement() {
        let edges = &[
            (0, 1, 3, 0),
            (0, 2, 2, 0),
            (1, 2, 1, 0),
            (1, 3, 2, 0),
            (2, 3, 3, 0),
        ];
        assert_eq!(max_flow(4, edges, 0, 3), 5);
    }

    #[test]
    fn bipartite_matching_k3_3() {
        let mut edges = Vec::new();
        for u in 1..=3 {
            edges.push((0, u, 1, 0));
        }
        for u in 1..=3 {
            for v in 4..=6 {
                edges.push((u, v, 1, 0));
            }
        }
        for v in 4..=6 {
            edges.push((v, 7, 1, 0));
        }
        assert_eq!(max_flow(8, &edges, 0, 7), 3);
    }

    #[test]
    fn layered_network_many_paths() {
        let layers = 6;
        let width = 30;
        let mut edges = Vec::new();
        let mut next_id = 1;
        let mut layer_nodes = vec![vec![0]];
        for _ in 1..layers {
            let mut this = Vec::with_capacity(width);
            for _ in 0..width {
                this.push(next_id);
                next_id += 1;
            }
            layer_nodes.push(this);
        }
        let sink = next_id;
        let n = sink + 1;
        layer_nodes.push(vec![sink]);
        for l in 0..layers {
            for &u in &layer_nodes[l] {
                for &v in &layer_nodes[l + 1] {
                    edges.push((u, v, 1, 0));
                }
            }
        }
        assert_eq!(max_flow(n, &edges, 0, sink), width as i64);
    }

    #[test]
    fn massive_parallel_edges() {
        let m = 10_000;
        let edges = vec![(0, 1, 1, 0); m];
        assert_eq!(max_flow(2, &edges, 0, 1), m as i64);
    }

    #[test]
    fn complete_bipartite_k50_50() {
        let left = 50;
        let right = 50;
        let source = 0;
        let sink = left + right + 1;
        let n = sink + 1;
        let mut edges = Vec::new();
        for u in 1..=left {
            edges.push((source, u, 1, 0));
        }
        for u in 1..=left {
            for v in (left + 1)..=(left + right) {
                edges.push((u, v, 1, 0));
            }
        }
        for v in (left + 1)..=(left + right) {
            edges.push((v, sink, 1, 0));
        }
        assert_eq!(max_flow(n, &edges, source, sink), left as i64);
    }

    #[test]
    fn dead_end_branches_trigger_gap() {
        let edges = &[
            (0, 1, 5, 0),
            (1, 2, 5, 0),
            (2, 3, 5, 0),
            (0, 4, 10, 0),
            (4, 5, 10, 0),
        ];
        assert_eq!(max_flow(6, edges, 0, 3), 5);
    }

    #[test]
    fn decreasing_capacity_chain() {
        let mut edges = Vec::new();
        for i in 0..10 {
            let cap = 100 - i as i64;
            edges.push((i, i + 1, cap, 0));
        }
        assert_eq!(max_flow(11, &edges, 0, 10), 91);
    }

    #[test]
    fn reverse_capacity_doesnt_add_flow() {
        let mut fl = PushRelabel::new(3);
        fl.add_edge(0, 1, 5, 10);
        fl.add_edge(1, 2, 7, 3);
        assert_eq!(fl.calc(0, 2), 5);
    }

    #[test]
    fn cycle_flow() {
        let mut fl = PushRelabel::new(4);
        fl.add_edge(0, 1, 8, 0);
        fl.add_edge(1, 2, 3, 0);
        fl.add_edge(2, 0, 5, 0);
        fl.add_edge(2, 3, 4, 0);
        assert_eq!(fl.calc(0, 3), 3);
    }

    #[test]
    fn source_is_sink() {
        let mut fl = PushRelabel::new(3);
        fl.add_edge(0, 1, 10, 0);
        fl.add_edge(1, 2, 10, 0);
        assert_eq!(fl.calc(2, 2), 0);
    }

    #[test]
    fn star_graph() {
        let leaves = 100;
        let n = leaves + 2;
        let s = 0;
        let t = n - 1;
        let mut fl = PushRelabel::new(n);
        for i in 1..=leaves {
            fl.add_edge(s, i, 1, 0);
            fl.add_edge(i, t, 1, 0);
        }
        assert_eq!(fl.calc(s, t), leaves as i64);
    }

    #[test]
    fn large_capacities_sum() {
        let mut fl = PushRelabel::new(2);
        let large = 1_000_000_000_000_i64;
        fl.add_edge(0, 1, large, 0);
        fl.add_edge(0, 1, large, 0);
        assert_eq!(fl.calc(0, 1), large * 2);
    }

    #[test]
    fn massive_dead_ends_border() {
        let n = 50;
        let sink = n;
        let mut fl = PushRelabel::new(n + 1);
        for i in 0..n {
            fl.add_edge(i, i + 1, 1, 0);
        }
        for i in 0..n {
            fl.add_edge(0, i, 10, 0);
        }
        assert_eq!(fl.calc(0, sink), 1);
    }

    #[test]
    fn mixed_forward_reverse_capacities() {
        let mut fl = PushRelabel::new(4);
        fl.add_edge(0, 1, 10, 5);
        fl.add_edge(1, 2, 5, 2);
        fl.add_edge(2, 3, 7, 3);
        assert_eq!(fl.calc(0, 3), 5);
    }

    fn cut(n: usize, edges: &[(usize, usize, i64, i64)], s: usize, t: usize) -> Vec<bool> {
        let mut pr = PushRelabel::new(n);
        for &(u, v, c, rc) in edges {
            pr.add_edge(u, v, c, rc);
        }
        pr.calc(s, t);
        let mut cut = vec![false; n];
        for i in 0..n {
            if pr.left_of_min_cut(i) {
                cut[i] = true;
            }
        }
        cut
    }

    #[test]
    fn simple_chain_min_cut() {
        let edges = &[(0, 1, 5, 0), (1, 2, 3, 0)];
        assert_eq!(cut(3, edges, 0, 2), vec![true, true, false]);
    }

    #[test]
    fn diamond_min_cut() {
        let edges = &[(0, 1, 10, 0), (1, 3, 10, 0), (0, 2, 10, 0), (2, 3, 10, 0)];
        assert_eq!(cut(4, edges, 0, 3), vec![true, false, false, false]);
    }

    #[test]
    fn bottleneck_min_cut() {
        let edges = &[
            (0, 1, 5, 0),
            (1, 5, 1, 0),
            (0, 2, 5, 0),
            (2, 5, 2, 0),
            (0, 3, 5, 0),
            (3, 5, 3, 0),
        ];
        assert_eq!(
            cut(6, edges, 0, 5),
            vec![true, true, true, true, false, false]
        );
    }

    #[test]
    fn reverse_capacity_min_cut() {
        let edges = &[(0, 1, 0, 5)];
        assert_eq!(cut(2, edges, 0, 1), vec![true, false]);
    }

    #[test]
    fn cycle_with_exits_min_cut() {
        let edges = &[
            (0, 1, 10, 0),
            (1, 2, 5, 0),
            (2, 1, 0, 0),
            (1, 3, 3, 0),
            (2, 3, 7, 0),
        ];
        assert_eq!(cut(4, edges, 0, 3), vec![true, true, false, false]);
    }

    #[test]
    fn dead_arm_min_cut() {
        let edges = &[
            (0, 1, 5, 0),
            (1, 2, 5, 0),
            (2, 3, 5, 0),
            (0, 4, 10, 0),
            (4, 5, 10, 0),
        ];
        assert_eq!(
            cut(6, edges, 0, 3),
            vec![true, false, false, false, true, true]
        );
    }

    #[test]
    fn flow_recovery_chain() {
        let mut pr = PushRelabel::new(3);
        pr.add_edge(0, 1, 5, 0);
        pr.add_edge(1, 2, 3, 0);
        assert_eq!(pr.calc(0, 2), 3);
        let mut f = pr.flows();
        f.sort();
        assert_eq!(f, vec![(0, 1, 3), (1, 2, 3)]);
    }

    #[test]
    fn flow_recovery_parallel() {
        let mut pr = PushRelabel::new(3);
        pr.add_edge(0, 1, 3, 0);
        pr.add_edge(0, 1, 2, 0);
        pr.add_edge(1, 2, 5, 0);
        assert_eq!(pr.calc(0, 2), 5);
        let mut f = pr.flows();
        f.sort();
        assert_eq!(f, vec![(0, 1, 2), (0, 1, 3), (1, 2, 5)]);
    }

    #[test]
    fn flow_excludes_reverse() {
        let mut pr = PushRelabel::new(2);
        pr.add_edge(0, 1, 1, 0);
        assert_eq!(pr.calc(0, 1), 1);
        let f = pr.flows();
        assert_eq!(f, vec![(0, 1, 1)]);
    }

    #[test]
    fn flow_no_negative() {
        let mut pr = PushRelabel::new(3);
        pr.add_edge(0, 1, 1, 2);
        pr.add_edge(1, 2, 1, 0);
        assert_eq!(pr.calc(0, 2), 1);
        let f = pr.flows();
        assert!(f.iter().all(|&(_, _, flow)| flow >= 0));
    }
}
