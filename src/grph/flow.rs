use std::{
    collections::VecDeque,
    ops::{AddAssign, SubAssign},
};

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
    pub fn add_edge(&mut self, s: usize, t: usize, c: F, rc: F) -> &mut Self {
        if s == t {
            return self;
        }
        let back_s = self.g[t].len();
        let back_t = self.g[s].len();
        self.g[s].push(PushRelabelEdge {
            to: t,
            rev: back_s,
            f: F::default(),
            c,
        });
        self.g[t].push(PushRelabelEdge {
            to: s,
            rev: back_t,
            f: F::default(),
            c: rc,
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
            let c = self.g[s][ei].c;
            if c > F::default() {
                self.push(s, ei, c, t);
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
// https://ocw.mit.edu/courses/6-854j-advanced-algorithms-fall-2005/b312c6aa208fc322bab7654e55c0ab01_lec14_1999.pdf
// https://people.orie.cornell.edu/dpw/orie633/LectureNotes/lecture14.pdf

#[derive(Clone, Copy, Debug)]
pub struct CostScalingInputEdge {
    pub from: usize,
    pub to: usize,
    pub b: i64,
    pub c: i64,
    pub cost: i64,
}

#[derive(Clone, Copy, Debug)]
struct CostScalingEdge {
    to: usize,
    rev: usize,
    c: i64,
    cost: i64,
}

pub struct CostScaling {
    n: usize,
    inf: i64,
    input_edges: Vec<CostScalingInputEdge>,
    edge_mp: Vec<usize>,
    g: Vec<CostScalingEdge>,
    d: Vec<usize>,
    init_cost: i64,
    init_excess: Vec<i64>,
    p: Vec<i64>,
    cur: Vec<usize>,
}

impl CostScaling {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            inf: i64::MAX / 2,
            input_edges: Vec::new(),
            edge_mp: Vec::new(),
            g: Vec::new(),
            d: Vec::new(),
            init_cost: 0,
            init_excess: Vec::new(),
            p: Vec::new(),
            cur: Vec::new(),
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize, cost: i64, c: i64, b: i64) {
        self.input_edges.push(CostScalingInputEdge {
            from: u,
            to: v,
            b,
            c,
            cost,
        });
    }

    fn construct(&mut self) {
        self.d = vec![0; self.n + 1];
        self.g = vec![
            CostScalingEdge {
                to: 0,
                rev: 0,
                c: 0,
                cost: 0
            };
            2 * self.input_edges.len()
        ];
        self.edge_mp = vec![0; self.input_edges.len()];
        self.init_excess = vec![0; self.n];
        self.init_cost = 0;
        self.p = vec![0; self.n];
        self.cur = vec![0; self.n];
        for e in &self.input_edges {
            self.d[e.from + 1] += 1;
            self.d[e.to + 1] += 1;
        }
        for i in 0..self.n {
            self.d[i + 1] += self.d[i];
        }
        for i in 0..self.n {
            self.cur[i] = self.d[i];
        }
        let mut current_d = self.d.clone();
        for (i, e) in self.input_edges.iter().enumerate() {
            self.init_excess[e.to] += e.c;
            self.init_excess[e.from] -= e.b;
            self.init_cost += e.cost * (e.c + e.b);
            let from_idx = current_d[e.from];
            let to_idx = current_d[e.to];
            self.edge_mp[i] = from_idx;
            current_d[e.from] += 1;
            current_d[e.to] += 1;
            self.g[from_idx] = CostScalingEdge {
                to: e.to,
                rev: to_idx,
                c: e.c - e.b,
                cost: e.cost,
            };
            self.g[to_idx] = CostScalingEdge {
                to: e.from,
                rev: from_idx,
                c: 0,
                cost: -e.cost,
            };
        }
    }

    fn is_feasible(&mut self) -> bool {
        let mut pr = PushRelabel::new(self.n + 2);
        let s = self.n;
        let t = self.n + 1;
        let mut total_demand = 0;
        let mut node_imbalance = vec![0; self.n];
        for e in &self.input_edges {
            node_imbalance[e.from] += e.b;
            node_imbalance[e.to] -= e.b;
        }
        for e in &self.input_edges {
            pr.add_edge(e.from, e.to, e.c - e.b, 0);
        }
        for i in 0..self.n {
            if node_imbalance[i] > 0 {
                pr.add_edge(s, i, node_imbalance[i], 0);
                total_demand += node_imbalance[i];
            } else if node_imbalance[i] < 0 {
                pr.add_edge(i, t, -node_imbalance[i], 0);
            }
        }
        pr.calc(s, t) == total_demand
    }

    pub fn mcc(&mut self) -> (bool, i64) {
        self.construct();
        if !self.is_feasible() {
            return (false, 0);
        }
        let cost_multiplier = self.n.next_power_of_two() as i64 * 2;
        let mut eps = 0;
        for e in &mut self.g {
            e.cost *= cost_multiplier;
            eps = eps.max(e.cost.abs());
        }
        while eps > 1 {
            eps = (eps / 4).max(1);
            self.refine(eps);
        }
        let mut ret = self.init_cost;
        for e in &self.g {
            ret -= (e.cost / cost_multiplier) * e.c;
        }
        (true, ret / 2)
    }

    /// O(n^3 log(n c))
    pub fn calc(&mut self, s: usize, t: usize) -> (bool, i64, i64, Vec<i64>) {
        let mut bridge_cap = 0;
        for e in &self.input_edges {
            if e.from == s {
                bridge_cap += e.c;
            }
        }
        bridge_cap = bridge_cap.max(1);
        let mut max_c = 1;
        for e in &self.input_edges {
            max_c = max_c.max(e.cost.abs());
        }
        let bridge_cost = -(max_c * self.n as i64).max(1);
        self.add_edge(t, s, bridge_cost, bridge_cap, 0);
        let (feasible, total_cost) = self.mcc();
        if !feasible {
            self.input_edges.pop();
            return (false, 0, 0, Vec::new());
        }
        let m = self.input_edges.len() - 1;
        let mut flows = Vec::with_capacity(m);
        for i in 0..m {
            let idx = self.edge_mp[i];
            let residual_cap = self.g[idx].c;
            let e = self.input_edges[i];
            let f = (e.c - e.b) - residual_cap;
            flows.push(f);
        }
        let bridge_idx = self.edge_mp[m];
        let total_flow = bridge_cap - self.g[bridge_idx].c;
        let actual_min_cost = total_cost - (total_flow * bridge_cost);
        self.input_edges.pop();
        (true, total_flow, actual_min_cost, flows)
    }

    fn refine(&mut self, eps: i64) {
        let n = self.n;
        for i in 0..n {
            self.cur[i] = self.d[i];
        }
        for u in 0..n {
            for i in self.d[u]..self.d[u + 1] {
                let e = self.g[i];
                let cp = e.cost + self.p[u] - self.p[e.to];
                if cp < 0 {
                    let cap = e.c;
                    let rev = e.rev;
                    self.g[rev].c += cap;
                    self.g[i].c = 0;
                }
            }
        }
        let mut excess = self.init_excess.clone();
        for e in &self.g {
            excess[e.to] -= e.c;
        }
        let mut q = VecDeque::with_capacity(n);
        for u in 0..n {
            if excess[u] > 0 {
                q.push_back(u);
            }
        }
        while let Some(u) = q.pop_front() {
            let mut delta = self.inf;
            let start_i = self.cur[u];
            let end_i = self.d[u + 1];
            let mut i = start_i;
            while i < end_i {
                let e = self.g[i];
                if e.c > 0 {
                    let cp = e.cost + self.p[u] - self.p[e.to];
                    if cp < 0 {
                        if excess[e.to] == 0 {
                            let mut delta_v = self.inf;
                            let v = e.to;
                            let mut can_relabel = true;
                            for j in self.d[v]..self.d[v + 1] {
                                let ev = self.g[j];
                                if ev.c > 0 {
                                    let cpv = ev.cost + self.p[v] - self.p[ev.to];
                                    if cpv < 0 {
                                        can_relabel = false;
                                        break;
                                    }
                                    delta_v = delta_v.min(cpv);
                                }
                            }
                            if can_relabel {
                                self.p[v] -= delta_v + eps;
                                self.cur[v] = self.d[v];
                                continue;
                            }
                        }
                        let df = excess[u].min(e.c);
                        self.g[i].c -= df;
                        let rev = self.g[i].rev;
                        self.g[rev].c += df;
                        excess[e.to] += df;
                        excess[u] -= df;
                        if excess[e.to] > 0 && excess[e.to] <= df {
                            q.push_front(e.to);
                        }
                        if excess[u] == 0 {
                            self.cur[u] = i;
                            break;
                        }
                    } else {
                        delta = delta.min(cp);
                    }
                }
                i += 1;
            }
            if excess[u] > 0 {
                if start_i > self.d[u] {
                    for j in self.d[u]..start_i {
                        let e = self.g[j];
                        if e.c > 0 {
                            let cp = e.cost + self.p[u] - self.p[e.to];
                            delta = delta.min(cp);
                        }
                    }
                }
                self.p[u] -= delta + eps;
                self.cur[u] = self.d[u];
                q.push_back(u);
            }
        }
    }
}

// TODO: min cost b-flow using network simplex
// https://judge.yosupo.jp/submission/313861

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_circulation() {
        // Simple triangle: 0->1 (cost 2), 1->2 (cost 2), 2->0 (cost -5)
        // All capacities 10. Minimum cost should be -1 * 10 = -10
        let mut mcc = CostScaling::new(3);
        mcc.add_edge(0, 1, 2, 10, 0);
        mcc.add_edge(1, 2, 2, 10, 0);
        mcc.add_edge(2, 0, -5, 10, 0);

        let (feasible, cost) = mcc.mcc();
        assert!(feasible);
        assert_eq!(cost, -10);
    }

    #[test]
    fn test_infeasible() {
        let mut mcc = CostScaling::new(2);
        // Demanding more than capacity allows
        mcc.add_edge(0, 1, 1, 5, 10);

        let (feasible, _) = mcc.mcc();
        assert!(!feasible);
    }

    #[test]
    fn test_min_cost_flow_as_circulation() {
        let n = 3;
        let mut mcc = CostScaling::new(n);

        // Path: 0 -> 1 -> 2
        // To make this a "circulation" with flow 2:
        // We add a return edge 2 -> 0 with cost 0 and capacity 2
        mcc.add_edge(0, 1, 1, 2, 2);
        mcc.add_edge(1, 2, 1, 2, 2);
        mcc.add_edge(2, 0, 0, 2, 2); // Return edge to satisfy flow conservation

        let (feasible, cost) = mcc.mcc();

        assert!(feasible, "Circulation should be feasible");
        // Cost: (1 * 2) + (1 * 2) + (0 * 2) = 4
        assert_eq!(cost, 4);
    }

    #[test]
    fn test_mcmf() {
        let mut mcc = CostScaling::new(3);
        // 0 -> 1 cost 10, cap 5
        // 1 -> 2 cost 10, cap 5
        mcc.add_edge(0, 1, 10, 5, 0);
        mcc.add_edge(1, 2, 10, 5, 0);

        let (success, _, _, _) = mcc.calc(0, 2);
        assert!(success);
        // Max flow is 5, cost per unit is 20, total 100
        // (Actual result will include the artificial negative cost;
        // you would typically normalize this by removing the t->s edge's contribution)
    }

    #[test]
    fn test_mcmf_success() {
        let mut mcc = CostScaling::new(4);
        // Source 0, Sink 3
        // 0 -> 1: cost 1, cap 10
        // 0 -> 2: cost 5, cap 10
        // 1 -> 3: cost 1, cap 5
        // 2 -> 3: cost 1, cap 5

        mcc.add_edge(0, 1, 1, 10, 0);
        mcc.add_edge(0, 2, 5, 10, 0);
        mcc.add_edge(1, 3, 1, 5, 0);
        mcc.add_edge(2, 3, 1, 5, 0);

        let (success, _, cost, _) = mcc.calc(0, 3);

        assert!(success);
        // Path 1: 0-1-3 (cap 5, cost 1+1=2) -> Cost 10
        // Path 2: 0-2-3 (cap 5, cost 5+1=6) -> Cost 30
        // Total Max Flow: 10, Total Min Cost: 40
        assert_eq!(cost, 40);
    }

    /// Helper to setup and run a simple case
    fn run_mcmf(n: usize, s: usize, t: usize, edges: &[(usize, usize, i64, i64)]) -> (bool, i64) {
        let mut mcc = CostScaling::new(n);
        for &(u, v, cost, cap) in edges {
            mcc.add_edge(u, v, cost, cap, 0);
        }
        let (success, _, cost, _) = mcc.calc(s, t);
        (success, cost)
    }

    #[test]
    fn test_single_edge() {
        // Simple 0 -> 1 with cost 5 and capacity 10
        let (feasible, cost) = run_mcmf(2, 0, 1, &[(0, 1, 5, 10)]);
        assert!(feasible);
        // Max flow is 10. Total cost = 10 * 5 = 50.
        assert_eq!(cost, 50);
    }

    #[test]
    fn test_parallel_edges() {
        // Two edges from 0 -> 1
        // Edge 1: Cost 10, Cap 10
        // Edge 2: Cost 5, Cap 10
        // Max flow should be 20.
        // Cost: (10 * 5) + (10 * 10) = 50 + 100 = 150
        let (feasible, cost) = run_mcmf(
            2,
            0,
            1,
            &[
                (0, 1, 10, 10), // Expensive
                (0, 1, 5, 10),  // Cheap
            ],
        );
        assert!(feasible);
        assert_eq!(cost, 150);
    }

    #[test]
    fn test_diamond_graph() {
        //      /-> 1 -\
        //     /        \
        //  0 -          -> 3
        //     \        /
        //      \-> 2 -/
        //
        // Path 0->1->3: Cost 1+1=2, Cap min(10,10)=10
        // Path 0->2->3: Cost 2+2=4, Cap min(10,10)=10
        // Total Max Flow: 20
        // Total Cost: (10 * 2) + (10 * 4) = 20 + 40 = 60
        let edges = vec![(0, 1, 1, 10), (1, 3, 1, 10), (0, 2, 2, 10), (2, 3, 2, 10)];
        let (feasible, cost) = run_mcmf(4, 0, 3, &edges);
        assert!(feasible);
        assert_eq!(cost, 60);
    }

    #[test]
    fn test_diamond_bottleneck() {
        // Similar to above, but the sink edges have limited capacity.
        // 0->1 (Cap 10, Cost 1)
        // 0->2 (Cap 10, Cost 1)
        // 1->3 (Cap 5, Cost 1)  <-- Bottleneck
        // 2->3 (Cap 5, Cost 1)  <-- Bottleneck
        // Max Flow: 10
        // Cost: 5*(1+1) + 5*(1+1) = 20
        let edges = vec![(0, 1, 1, 10), (1, 3, 1, 5), (0, 2, 1, 10), (2, 3, 1, 5)];
        let (feasible, cost) = run_mcmf(4, 0, 3, &edges);
        assert!(feasible);
        assert_eq!(cost, 20);
    }

    #[test]
    fn test_negative_costs() {
        // 0 -> 1 (Cost 10, Cap 10)
        // 1 -> 2 (Cost -5, Cap 10)
        // Net cost per unit: 5.
        // Max flow 10. Total cost 50.
        let edges = vec![(0, 1, 10, 10), (1, 2, -5, 10)];
        let (feasible, cost) = run_mcmf(3, 0, 2, &edges);
        assert!(feasible);
        assert_eq!(cost, 50);
    }

    #[test]
    fn test_negative_cycle_logic_check() {
        // Note: Standard Min-Cost Max-Flow usually assumes no negative cycles reachable
        // from the source in the residual graph initially, OR the algorithm must handle them.
        // Cost scaling generally handles negative costs robustly.
        //
        // Path: 0 -> 1 -> 2 (Cost 10+10 = 20)
        // Shortcut: 0 -> 2 (Cost 100)
        // Negative edge 2 -> 1 (Cost -50) creating cycle 1->2->1 cost -40?
        // If the algorithm detects negative cycles correctly, it might push infinite flow
        // if capacities were infinite, but here capacities are finite.

        // However, this specific function is "Min Cost Max Flow".
        // It should saturate the flow first.
        // 0->1 (Cap 10, Cost 10)
        // 1->2 (Cap 10, Cost 10)
        // Max Flow 10 via 0->1->2. Cost 200.

        // Add a disjoint negative cycle 3->4->3?
        // If the cycle is not reachable from S or T, it shouldn't affect the S-T flow cost
        // unless we are doing min-cost circulation over the whole graph.
        // The implementation calculates circulation, so it MIGHT find the negative cycle.
        // Let's test if it returns the cost of the flow + the cost of the negative cycle.

        let mut mcc = CostScaling::new(5);
        // Flow path
        mcc.add_edge(0, 1, 10, 10, 0);
        mcc.add_edge(1, 2, 10, 10, 0);

        // Disconnected negative cycle
        // 3->4 (Cost -10, Cap 1)
        // 4->3 (Cost 5, Cap 1)
        // Cycle cost -5, Cap 1. Total cost -5.
        mcc.add_edge(3, 4, -10, 1, 0);
        mcc.add_edge(4, 3, 5, 1, 0);

        let (feasible, _, cost, ..) = mcc.calc(0, 2);
        assert!(feasible);

        // Flow cost: 10 * (10+10) = 200.
        // Circulation cost: 1 * (-10+5) = -5.
        // Total expected: 195.
        assert_eq!(cost, 195);
    }

    #[test]
    fn test_disconnected() {
        let edges = vec![(0, 1, 10, 10), (2, 3, 10, 10)];
        // No path from 0 to 3
        let (feasible, cost) = run_mcmf(4, 0, 3, &edges);
        // It is "feasible" to have 0 max flow.
        assert!(feasible);
        assert_eq!(cost, 0);
    }

    #[test]
    fn test_large_capacities_overflow_regression() {
        // This test specifically targets the overflow bug you encountered.
        // We use large capacities and costs that would overflow i64 if multiplied blindly
        // or if i64::MAX/2 was used as a bridge capacity.

        let n = 3;
        let s = 0;
        let t = 2;
        let mut mcc = CostScaling::new(n);

        // Large capacity: 1 billion.
        // Large cost: 1 million.
        // Total cost ~ 10^15, which fits in i64 (max ~9*10^18).
        let cap = 1_000_000_000;
        let cost_val = 1_000_000;

        mcc.add_edge(0, 1, cost_val, cap, 0);
        mcc.add_edge(1, 2, cost_val, cap, 0);

        let (feasible, _, cost, ..) = mcc.calc(s, t);

        assert!(feasible);
        // Expected: 1_000_000_000 * (1_000_000 + 1_000_000) = 2_000_000_000_000_000
        assert_eq!(cost, cap * (cost_val * 2));
    }

    #[test]
    fn test_high_cost_scaling() {
        // Test ensuring the internal scaling (multiplying by N) doesn't panic.
        let n = 4;
        let mut mcc = CostScaling::new(n);

        // Costs near the edge of what's reasonable before scaling logic applies
        let high_cost = 1_000_000_000;

        mcc.add_edge(0, 1, high_cost, 1, 0);
        mcc.add_edge(1, 2, high_cost, 1, 0);
        mcc.add_edge(2, 3, high_cost, 1, 0);

        let (feasible, _, cost, ..) = mcc.calc(0, 3);
        assert!(feasible);
        assert_eq!(cost, 3 * high_cost);
    }

    #[test]
    fn test_split_merge_varied_costs() {
        // S -> A (Cap 10, Cost 10)
        // S -> B (Cap 10, Cost 2)
        // A -> T (Cap 10, Cost 2)
        // B -> T (Cap 10, Cost 10)
        // A -> B (Cap 10, Cost 1)  <-- Cross edge

        // Optimal flow of 20:
        // Path 1: S -> B -> T (Cost 2+10=12). Cap 10.
        // Path 2: S -> A -> T (Cost 10+2=12). Cap 10.
        // Cross edge S->A->B->T cost is 10+1+10=21 (Worse).
        // Cross edge S->B (no reverse to A).

        // Total cost: 10*12 + 10*12 = 240.

        let mut mcc = CostScaling::new(4);
        mcc.add_edge(0, 1, 10, 10, 0); // S->A
        mcc.add_edge(0, 2, 2, 10, 0); // S->B
        mcc.add_edge(1, 3, 2, 10, 0); // A->T
        mcc.add_edge(2, 3, 10, 10, 0); // B->T
        mcc.add_edge(1, 2, 1, 10, 0); // A->B

        let (feasible, _, cost, ..) = mcc.calc(0, 3);
        assert!(feasible);
        assert_eq!(cost, 240);
    }

    #[test]
    fn test_mcmf_flow_values_simple_path() {
        // Path: 0 -> 1 -> 2
        // Cap 10 on both, Cost 1 on both.
        let mut mcc = CostScaling::new(3);
        mcc.add_edge(0, 1, 1, 10, 0); // Edge 0
        mcc.add_edge(1, 2, 1, 10, 0); // Edge 1

        let (_, total_flow, total_cost, flows) = mcc.calc(0, 2);

        assert_eq!(total_flow, 10);
        assert_eq!(total_cost, 20);
        assert_eq!(flows.len(), 2);
        assert_eq!(flows[0], 10, "Flow on 0->1 should be 10");
        assert_eq!(flows[1], 10, "Flow on 1->2 should be 10");
    }

    #[test]
    fn test_mcmf_flow_values_split() {
        // Source 0, Sink 3
        // Path A: 0 -> 1 -> 3 (Cost 10, Cap 10)
        // Path B: 0 -> 2 -> 3 (Cost 20, Cap 10)
        // Max flow should be 20.
        // We add edges in a specific order to verify the returned vector maps correctly.

        let mut mcc = CostScaling::new(4);
        mcc.add_edge(0, 1, 5, 10, 0); // Edge 0: 0->1 (Part of Cheap Path)
        mcc.add_edge(0, 2, 10, 10, 0); // Edge 1: 0->2 (Part of Expensive Path)
        mcc.add_edge(1, 3, 5, 10, 0); // Edge 2: 1->3 (Part of Cheap Path)
        mcc.add_edge(2, 3, 10, 10, 0); // Edge 3: 2->3 (Part of Expensive Path)

        let (_, total_flow, total_cost, flows) = mcc.calc(0, 3);

        assert_eq!(total_flow, 20);
        assert_eq!(total_cost, 10 * 10 + 10 * 20); // 300

        // Verify individual edges
        assert_eq!(flows[0], 10); // 0->1
        assert_eq!(flows[1], 10); // 0->2
        assert_eq!(flows[2], 10); // 1->3
        assert_eq!(flows[3], 10); // 2->3
    }

    #[test]
    fn test_mcmf_flow_values_limited_cap() {
        // Source 0, Sink 2
        // Two parallel paths with different costs.
        // Edge 0: 0->1 (Cost 10, Cap 5)
        // Edge 1: 0->1 (Cost 2, Cap 5)
        // Edge 2: 1->2 (Cost 0, Cap 10)
        // Total flow 10.
        // Flow should saturate Edge 1 (cheaper) and Edge 0.

        let mut mcc = CostScaling::new(3);
        mcc.add_edge(0, 1, 10, 5, 0); // Edge 0 (Expensive)
        mcc.add_edge(0, 1, 2, 5, 0); // Edge 1 (Cheap)
        mcc.add_edge(1, 2, 0, 10, 0); // Edge 2 (Bottleneck)

        let (_, total_flow, total_cost, flows) = mcc.calc(0, 2);

        assert_eq!(total_flow, 10);
        assert_eq!(total_cost, 5 * 10 + 5 * 2); // 60

        assert_eq!(flows[0], 5, "Expensive edge should be saturated");
        assert_eq!(flows[1], 5, "Cheap edge should be saturated");
        assert_eq!(flows[2], 10, "Sink edge should carry all flow");
    }

    #[test]
    fn test_mcmf_flow_values_partial_saturation() {
        // Source 0, Sink 2
        // Edge 0: 0->1 (Cost 10, Cap 10)
        // Edge 1: 0->1 (Cost 2, Cap 10)
        // Edge 2: 1->2 (Cost 0, Cap 15)

        // Max flow is limited by edge 2 (Cap 15).
        // Flow should prioritize Edge 1 (Cost 2).
        // Edge 1 should have 10 flow.
        // Edge 0 should have 5 flow.

        let mut mcc = CostScaling::new(3);
        mcc.add_edge(0, 1, 10, 10, 0); // Edge 0 (Expensive)
        mcc.add_edge(0, 1, 2, 10, 0); // Edge 1 (Cheap)
        mcc.add_edge(1, 2, 0, 15, 0); // Edge 2 (Bottleneck)

        let (_, total_flow, total_cost, flows) = mcc.calc(0, 2);

        assert_eq!(total_flow, 15);
        assert_eq!(total_cost, 10 * 2 + 5 * 10); // 20 + 50 = 70

        assert_eq!(flows[0], 5, "Expensive edge should take overflow (5)");
        assert_eq!(flows[1], 10, "Cheap edge should be saturated (10)");
        assert_eq!(flows[2], 15, "Sink edge saturated");
    }

    #[test]
    fn test_reusability() {
        // Ensure that calling min_cost_max_flow doesn't corrupt the struct
        // and we can add more edges and solve again.
        let mut mcc = CostScaling::new(3);
        mcc.add_edge(0, 1, 10, 10, 0);

        // Solve 1: 0->1
        let (_, f1, c1, _) = mcc.calc(0, 1);
        assert_eq!(f1, 10);
        assert_eq!(c1, 100);

        // Add 1->2 and solve 0->2
        mcc.add_edge(1, 2, 10, 10, 0);
        let (_, f2, c2, flows) = mcc.calc(0, 2);

        assert_eq!(f2, 10);
        assert_eq!(c2, 200); // 10*10 + 10*10
        assert_eq!(flows.len(), 2);
        assert_eq!(flows[0], 10);
        assert_eq!(flows[1], 10);
    }
}
