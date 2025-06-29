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
            if c > F::default() {
                let cand = self.h[w] + 1;
                if cand < nh {
                    nh = cand;
                    nc = i;
                }
            }
        }
        self.h[u] = nh;
        self.cur[u] = nc;
        self.co[nh] += 1;
        self.co[hi] -= 1;
        if hi < n && self.co[hi] == 0 {
            for i in 0..n {
                if self.h[i] > hi && self.h[i] < n {
                    self.co[self.h[i]] -= 1;
                    self.h[i] = n + 1;
                }
            }
        }
        return self.h[u];
    }

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

#[cfg(test)]
mod tests {
    use super::*;

    /// 1) Trivial: no edges at all → flow = 0
    #[test]
    fn trivial_no_edges() {
        let mut fl = PushRelabel::<i64>::new(2);
        assert_eq!(fl.calc(0, 1), 0);
    }

    /// 2) Single edge
    #[test]
    fn single_edge() {
        let mut fl = PushRelabel::new(2);
        fl.add_edge(0, 1, 7, 0);
        assert_eq!(fl.calc(0, 1), 7);
    }

    /// 3) Parallel edges sum properly
    #[test]
    fn parallel_edges() {
        let mut fl = PushRelabel::new(3);
        // two edges 0→1 of caps 3 and 2, then 1→2 cap 5
        assert_eq!(
            fl.add_edge(0, 1, 3, 0)
                .add_edge(0, 1, 2, 0)
                .add_edge(1, 2, 5, 0)
                .calc(0, 2),
            5
        );
    }

    /// 4) Diamond (two disjoint paths)
    #[test]
    fn diamond() {
        let mut fl = PushRelabel::new(5);
        // 0→1→4 and 0→2→4, each cap 10
        fl.add_edge(0, 1, 10, 0)
            .add_edge(1, 4, 10, 0)
            .add_edge(0, 2, 10, 0)
            .add_edge(2, 4, 10, 0)
            .add_edge(1, 2, 1, 0)
            .add_edge(2, 1, 1, 0);
        assert_eq!(fl.calc(0, 4), 20);
    }

    /// 5) Bottle‐necked multiple paths
    #[test]
    fn bottleneck_paths() {
        let mut fl = PushRelabel::new(6);
        // three parallel paths from 0→5 but with bottlenecks
        fl.add_edge(0, 1, 5, 0)
            .add_edge(1, 5, 1, 0)
            .add_edge(0, 2, 5, 0)
            .add_edge(2, 5, 2, 0)
            .add_edge(0, 3, 5, 0)
            .add_edge(3, 5, 3, 0);
        // total = 1+2+3 = 6
        assert_eq!(fl.calc(0, 5), 6);
    }

    /// 6) Disconnected component + gap heuristic trigger
    #[test]
    fn disconnected_and_gap() {
        let mut fl = PushRelabel::new(4);
        // 0→1 cap=5 but 1→3 cap=0 → no flow via 1
        fl.add_edge(0, 1, 5, 0)
            .add_edge(1, 3, 0, 0)
            .add_edge(0, 2, 3, 0)
            .add_edge(2, 3, 3, 0);

        // we expect only the 0–2–3 path to carry flow
        assert_eq!(fl.calc(0, 3), 3);
    }

    /// 7) Unit‐capacity bipartite matching 4×4
    #[test]
    fn bipartite_matching_4x4() {
        let n = 2 + 4 + 4; // source + left + right + sink
        let s = 0;
        let t = n - 1;
        let mut fl = PushRelabel::new(n);

        // source to left
        for u in 0..4 {
            fl.add_edge(s, 1 + u, 1, 0);
        }
        // left to right: connect i→j if (i+j) even
        for i in 0..4 {
            for j in 0..4 {
                if (i + j) % 2 == 0 {
                    fl.add_edge(1 + i, 1 + 4 + j, 1, 0);
                }
            }
        }
        // right to sink
        for v in 0..4 {
            fl.add_edge(1 + 4 + v, t, 1, 0);
        }

        // In this pattern, maximum matching size = 4
        assert_eq!(fl.calc(s, t), 4);
    }

    /// 8) Long chain of size 100 with varying capacities
    #[test]
    fn long_chain() {
        let n = 101;
        let mut fl = PushRelabel::new(n);
        // chain 0→1→2→…→100
        for i in 0..100 {
            fl.add_edge(i, i + 1, (i + 1) as i64, 0);
        }
        // bottleneck is the smallest cap = 1
        assert_eq!(fl.calc(0, 100), 1);
    }

    /// 9) Layered grid: 5×5 grid where flow can snake through.
    #[test]
    fn grid_5x5() {
        let w = 5;
        let h = 5;
        // node index = r*w + c, plus s,t at the ends
        let n = w * h + 2;
        let s = w * h;
        let t = w * h + 1;
        let mut fl = PushRelabel::new(n);

        // connect source to top‐row
        for c in 0..w {
            fl.add_edge(s, c, 2, 0);
        }
        // connect bottom‐row to sink
        for c in 0..w {
            fl.add_edge((h - 1) * w + c, t, 2, 0);
        }
        // connect each cell to its 4‐neighbors with cap=1
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

        // Rough lower bound: can send at least w=5 units
        let got = fl.calc(s, t);
        assert!(got >= 5 && got <= 10, "unexpected grid flow = {}", got);
    }

    /// 10) Self‐loops and zero‐capacity edges are ignored
    #[test]
    fn self_loops_and_zero_caps() {
        let mut fl = PushRelabel::new(3);
        fl.add_edge(0, 0, 10, 0)
            .add_edge(0, 1, 0, 0)
            .add_edge(0, 2, 5, 0)
            .add_edge(2, 1, 5, 0);
        assert_eq!(fl.calc(0, 1), 5);
    }

    /// 11) Complete graph small: 4 nodes, all edges cap=1, flow = min‐cut = 3
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
        // With node 0 as s and 3 as t, min‐cut(s,t)=3
        assert_eq!(fl.calc(0, 3), 3);
    }

    /// 12) Random but deterministic small graph to catch subtle bugs
    #[test]
    fn small_deterministic_random() {
        let mut fl = PushRelabel::new(7);
        // a fixed “random” pattern of edges
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

    /// Helper: build a PushRelabel instance with `n` nodes, add all `edges`,
    /// then compute max_flow(s, t).
    fn max_flow(n: usize, edges: &[(usize, usize, i64, i64)], s: usize, t: usize) -> i64 {
        let mut pr = PushRelabel::new(n);
        for &(u, v, cap, rcap) in edges {
            pr.add_edge(u, v, cap, rcap);
        }
        pr.calc(s, t)
    }

    #[test]
    fn empty_single_node() {
        // n=1, source==sink, no edges => flow = 0
        assert_eq!(max_flow(1, &[], 0, 0), 0);
    }

    #[test]
    fn two_nodes_no_edges() {
        // n=2, no path from 0 to 1 => 0
        assert_eq!(max_flow(2, &[], 0, 1), 0);
    }

    #[test]
    fn zero_capacity_edge() {
        // edge of cap=0 should contribute nothing
        let edges = &[(0, 1, 0, 0)];
        assert_eq!(max_flow(2, edges, 0, 1), 0);
    }

    #[test]
    fn simple_chain() {
        // 0→1→2→3 with caps 5,6,7 => bottleneck=5
        let edges = &[(0, 1, 5, 0), (1, 2, 6, 0), (2, 3, 7, 0)];
        assert_eq!(max_flow(4, edges, 0, 3), 5);
    }

    #[test]
    fn diamond_structure() {
        //    0
        //   / \
        //  1   2
        //   \ /
        //    3
        //
        // caps: 0→1=5, 0→2=7, 1→3=4, 2→3=8 => max-flow = 4 + 7 = 11
        let edges = &[(0, 1, 5, 0), (0, 2, 7, 0), (1, 3, 4, 0), (2, 3, 8, 0)];
        assert_eq!(max_flow(4, edges, 0, 3), 11);
    }

    #[test]
    fn disconnected_sink() {
        // 0→1 exists but 1 is not connected to 2 (the sink) => 0
        let edges = &[(0, 1, 5, 0)];
        assert_eq!(max_flow(3, edges, 0, 2), 0);
    }

    #[test]
    fn reverse_capacity_only() {
        // rcap > 0 but forward cap = 0 => no forward flow possible
        let edges = &[(0, 1, 0, 5)];
        assert_eq!(max_flow(2, edges, 0, 1), 0);
    }

    #[test]
    fn small_cycle_with_two_exits() {
        // cycle between 1 and 2, flow can exit to 3:
        // 0→1 cap=10, 1→2 cap=5, 2→1 cap=0, 1→3 cap=3, 2→3 cap=7 => total 3+5=8
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
        // s=0, a=1, b=2, t=3:
        // 0→1 cap=3, 0→2 cap=2, 1→2 cap=1, 1→3 cap=2, 2→3 cap=3 => expected 5
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
        // K_{3,3} unit‐capacity matching:
        // nodes 1–3 on left, 4–6 on right, super-source=0, super-sink=7
        let mut edges = Vec::new();
        // source to left
        for u in 1..=3 {
            edges.push((0, u, 1, 0));
        }
        // left to right complete
        for u in 1..=3 {
            for v in 4..=6 {
                edges.push((u, v, 1, 0));
            }
        }
        // right to sink
        for v in 4..=6 {
            edges.push((v, 7, 1, 0));
        }
        assert_eq!(max_flow(8, &edges, 0, 7), 3);
    }

    #[test]
    fn layered_network_many_paths() {
        // 6 layers (including source+sink), width=30 → max flow = 30
        let layers = 6;
        let width = 30;
        let mut edges = Vec::new();
        // assign node IDs: layer 0 is source=0.
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
        // fully connect each layer to the next with cap=1
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
        // 10 000 parallel unit-cap edges between 0 and 1
        let m = 10_000;
        let edges = vec![(0, 1, 1, 0); m];
        assert_eq!(max_flow(2, &edges, 0, 1), m as i64);
    }

    #[test]
    fn complete_bipartite_k50_50() {
        // standard bipartite matching K₅₀,₅₀
        let left = 50;
        let right = 50;
        let source = 0;
        let sink = left + right + 1;
        let n = sink + 1;
        let mut edges = Vec::new();
        // source → left
        for u in 1..=left {
            edges.push((source, u, 1, 0));
        }
        // left → right (complete)
        for u in 1..=left {
            for v in (left + 1)..=(left + right) {
                edges.push((u, v, 1, 0));
            }
        }
        // right → sink
        for v in (left + 1)..=(left + right) {
            edges.push((v, sink, 1, 0));
        }
        assert_eq!(max_flow(n, &edges, source, sink), left as i64);
    }

    #[test]
    fn dead_end_branches_trigger_gap() {
        // main path 0→1→2→3 (cap=5), dead branch 0→4→5
        let edges = &[
            (0, 1, 5, 0),
            (1, 2, 5, 0),
            (2, 3, 5, 0),
            (0, 4, 10, 0),
            (4, 5, 10, 0),
        ];
        // only the 0→1→2→3 chain reaches sink=3
        assert_eq!(max_flow(6, edges, 0, 3), 5);
    }

    #[test]
    fn decreasing_capacity_chain() {
        // chain of length 10, capacities 100→99→…→91 → bottleneck = 91
        let mut edges = Vec::new();
        for i in 0..10 {
            let cap = 100 - i as i64;
            edges.push((i, i + 1, cap, 0));
        }
        assert_eq!(max_flow(11, &edges, 0, 10), 91);
    }

    /// 25) Reverse capacities do not spuriously increase forward flow.
    #[test]
    fn reverse_capacity_doesnt_add_flow() {
        let mut fl = PushRelabel::new(3);
        // 0→1 cap=5, 1→0 cap=10;  1→2 cap=7, 2→1 cap=3
        fl.add_edge(0, 1, 5, 10);
        fl.add_edge(1, 2, 7, 3);
        // Forward path is limited by 0→1 (5) and 1→2 (7) → min = 5
        assert_eq!(fl.calc(0, 2), 5);
    }

    /// 26) Complex cycle should not trap the algorithm or create extra flow.
    #[test]
    fn cycle_flow() {
        let mut fl = PushRelabel::new(4);
        fl.add_edge(0, 1, 8, 0);
        fl.add_edge(1, 2, 3, 0);
        fl.add_edge(2, 0, 5, 0);
        fl.add_edge(2, 3, 4, 0);
        // Only path to 3 is 0→1→2→3 with cap = 3.
        assert_eq!(fl.calc(0, 3), 3);
    }

    /// 27) When source == sink, max_flow should always be zero.
    #[test]
    fn source_is_sink() {
        let mut fl = PushRelabel::new(3);
        fl.add_edge(0, 1, 10, 0);
        fl.add_edge(1, 2, 10, 0);
        // Even though edges exist, s == t ⇒ flow = 0
        assert_eq!(fl.calc(2, 2), 0);
    }

    /// 28) Star graph: 100 leaves each providing a disjoint unit path.
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
        // Total disjoint unit‐capacity leaves = 100
        assert_eq!(fl.calc(s, t), leaves as i64);
    }

    /// 29) Large capacities accumulation to verify no overflow occurs.
    #[test]
    fn large_capacities_sum() {
        let mut fl = PushRelabel::new(2);
        let large = 1_000_000_000_000_i64;
        // Two parallel edges of size 10^12 each
        fl.add_edge(0, 1, large, 0);
        fl.add_edge(0, 1, large, 0);
        assert_eq!(fl.calc(0, 1), large * 2);
    }

    /// 30) Many dead ends attached to source to force gap‐relabel on interior nodes.
    #[test]
    fn massive_dead_ends_border() {
        let n = 50;
        let sink = n;
        let mut fl = PushRelabel::new(n + 1);
        // Primary chain 0→1→…→sink with unit capacity
        for i in 0..n {
            fl.add_edge(i, i + 1, 1, 0);
        }
        // Attach 50 “dead‐end” spokes from 0 that never reach the sink
        for i in 0..n {
            fl.add_edge(0, i, 10, 0);
        }
        // Only the main chain can carry flow = 1
        assert_eq!(fl.calc(0, sink), 1);
    }

    /// 31) Mixed forward/reverse capacities on a multi‐edge path.
    #[test]
    fn mixed_forward_reverse_capacities() {
        let mut fl = PushRelabel::new(4);
        // 0→1 cap=10, rev=5;  1→2 cap=5, rev=2;  2→3 cap=7, rev=3
        fl.add_edge(0, 1, 10, 5);
        fl.add_edge(1, 2, 5, 2);
        fl.add_edge(2, 3, 7, 3);
        // True max‐flow is limited by the smallest forward cap = 5
        assert_eq!(fl.calc(0, 3), 5);
    }

    /// Build, run max_flow, then compute min_cut from s.
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

    /// 1) Simple chain: 0→1 cap=5, 1→2 cap=3 -> reachable {0,1}.
    #[test]
    fn simple_chain_min_cut() {
        let edges = &[(0, 1, 5, 0), (1, 2, 3, 0)];
        assert_eq!(cut(3, edges, 0, 2), vec![true, true, false]);
    }

    /// 2) Diamond: two disjoint paths fully saturated -> only {0}.
    #[test]
    fn diamond_min_cut() {
        let edges = &[(0, 1, 10, 0), (1, 3, 10, 0), (0, 2, 10, 0), (2, 3, 10, 0)];
        assert_eq!(cut(4, edges, 0, 3), vec![true, false, false, false]);
    }

    /// 3) Bottleneck: three parallel paths -> reachable {0,1,2,3}.
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

    /// 4) Reverse-only capacity: no forward arc -> only {0}.
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
        // After maxflow=8, residual edges from 0: 0->1 has positive capacity,
        // but 1 has no outgoing to 2/3, so only {0,1} reachable.
        assert_eq!(cut(4, edges, 0, 3), vec![true, true, false, false]);
    }

    /// 6) Dead arm: a branch off source that never reaches sink remains on source side
    #[test]
    fn dead_arm_min_cut() {
        let edges = &[
            (0, 1, 5, 0),
            (1, 2, 5, 0),
            (2, 3, 5, 0),
            (0, 4, 10, 0),
            (4, 5, 10, 0),
        ];
        // Main chain sends 5 to sink; branch 0->4->5 pushes back to 0,
        // so residual has 0->4 and 4->5 positive -> reachable {0,4,5}.
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
