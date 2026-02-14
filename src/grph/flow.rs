use std::{
    collections::{BinaryHeap, VecDeque},
    ops::{AddAssign, SubAssign},
};

use crate::ds::{bit_vec::BitVec, score::MinScore};

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
        if nh == usize::MAX {
            nh = n + 1;
        }
        self.h[u] = nh;
        self.cur[u] = nc;
        if nh < self.co.len() {
            self.co[nh] += 1;
        }
        self.co[hi] = self.co[hi].saturating_sub(1);
        if hi < n && self.co[hi] == 0 {
            for i in 0..n {
                if self.h[i] > hi && self.h[i] < n {
                    self.co[self.h[i]] = self.co[self.h[i]].saturating_sub(1);
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
            let u = self.hs[hi].pop().unwrap();
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

    #[inline]
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
            eps = (eps / 2).max(1);
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

#[derive(Clone, Copy, Debug)]
pub struct DinitzEdge {
    to: usize,
    rev: usize,
    c: i64,
    oc: i64,
}

impl DinitzEdge {
    #[inline]
    pub fn flow(&self) -> i64 {
        (self.oc - self.c).max(0)
    }
}

pub struct Dinitz {
    n: usize,
    g: Vec<Vec<DinitzEdge>>,
    lvl: Vec<i32>,
    cur: Vec<usize>,
    q: Vec<usize>,
}

impl Dinitz {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            g: vec![Vec::new(); n],
            lvl: vec![0; n],
            cur: vec![0; n],
            q: vec![0; n],
        }
    }

    pub fn add_edge(&mut self, a: usize, b: usize, cap: i64, rcap: i64) -> &mut Self {
        if a == b || a >= self.n || b >= self.n {
            return self;
        }
        let rev_b = self.g[b].len();
        let rev_a = self.g[a].len();
        self.g[a].push(DinitzEdge {
            to: b,
            rev: rev_b,
            c: cap,
            oc: cap,
        });
        self.g[b].push(DinitzEdge {
            to: a,
            rev: rev_a,
            c: rcap,
            oc: rcap,
        });
        self
    }

    fn bfs(&mut self, s: usize, t: usize, lim: i64) -> bool {
        self.lvl.fill(0);
        self.cur.fill(0);
        self.lvl[s] = 1;
        self.q[0] = s;
        let mut qi = 0;
        let mut qe = 1;
        while qi < qe && self.lvl[t] == 0 {
            let v = self.q[qi];
            qi += 1;
            for e in &self.g[v] {
                if self.lvl[e.to] == 0 && e.c >= lim {
                    self.lvl[e.to] = self.lvl[v] + 1;
                    self.q[qe] = e.to;
                    qe += 1;
                }
            }
        }
        self.lvl[t] != 0
    }

    fn dfs(&mut self, v: usize, t: usize, flow: i64) -> i64 {
        if v == t || flow == 0 {
            return flow;
        }
        while self.cur[v] < self.g[v].len() {
            let e = self.g[v][self.cur[v]];
            if self.lvl[e.to] == self.lvl[v] + 1 {
                let pushed = self.dfs(e.to, t, flow.min(e.c));
                if pushed > 0 {
                    self.g[v][self.cur[v]].c -= pushed;
                    let rev = self.g[v][self.cur[v]].rev;
                    self.g[e.to][rev].c += pushed;
                    return pushed;
                }
            }
            self.cur[v] += 1;
        }
        0
    }

    /// O(n m log U)
    /// O(min(m^1/2, n^2/3) m) if U = 1
    pub fn calc(&mut self, s: usize, t: usize) -> i64 {
        if s == t {
            return 0;
        }
        let mut max_cap = 0;
        for es in &self.g {
            for e in es {
                if e.c > max_cap {
                    max_cap = e.c;
                }
            }
        }
        if max_cap == 0 {
            return 0;
        }
        let mut lim = 1;
        while lim <= max_cap {
            lim <<= 1;
        }
        lim >>= 1;
        let mut total = 0;
        while lim > 0 {
            while self.bfs(s, t, lim) {
                loop {
                    let pushed = self.dfs(s, t, i64::MAX);
                    if pushed == 0 {
                        break;
                    }
                    total += pushed;
                }
            }
            lim >>= 1;
        }
        total
    }

    #[inline]
    pub fn left_of_min_cut(&self, a: usize) -> bool {
        a < self.n && self.lvl[a] != 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapacityScalingEdge {
    to: usize,
    rev: usize,
    cap: i64,
    cost: i64,
}

#[derive(Clone, Copy, Debug)]
pub struct CapacityScalingInputEdge {
    from: usize,
    to: usize,
    cap: i64,
    cost: i64,
}

pub struct CapacityScaling {
    n: usize,
    input_edges: Vec<CapacityScalingInputEdge>,
    adj: Vec<Vec<CapacityScalingEdge>>,
    p: Vec<i64>,
    dist: Vec<i64>,
    parent_edge: Vec<(usize, usize)>,
}

impl CapacityScaling {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            input_edges: Vec::new(),
            adj: vec![Vec::new(); n],
            p: vec![0; n],
            dist: vec![0; n],
            parent_edge: vec![(0, 0); n],
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
        self.input_edges.push(CapacityScalingInputEdge {
            from,
            to,
            cap,
            cost,
        });
    }

    fn reduced_cost(&self, u: usize, edge: &CapacityScalingEdge) -> i64 {
        edge.cost + self.p[u] - self.p[edge.to]
    }

    fn dijkstra(&mut self, s: usize, t: usize) -> bool {
        let inf = i64::MAX / 2;
        self.dist.fill(inf);
        self.dist[s] = 0;
        let mut pq = BinaryHeap::new();
        pq.push(MinScore(0, s));
        while let Some(MinScore(d, u)) = pq.pop() {
            if d > self.dist[u] {
                continue;
            }
            if u == t {
                return true;
            }
            for (i, e) in self.adj[u].iter().enumerate() {
                if e.cap > 0 {
                    let rc = self.reduced_cost(u, e);
                    if self.dist[e.to] > self.dist[u] + rc {
                        self.dist[e.to] = self.dist[u] + rc;
                        self.parent_edge[e.to] = (u, i);
                        pq.push(MinScore(self.dist[e.to], e.to));
                    }
                }
            }
        }
        false
    }

    fn push_capacity(&mut self, u: usize, idx: usize) {
        self.adj[u][idx].cap += 1;
        let rc = self.reduced_cost(u, &self.adj[u][idx]);
        if rc >= 0 {
            return;
        }
        let v = self.adj[u][idx].to;
        let found = self.dijkstra(v, u);
        let inf = i64::MAX / 2;
        if found {
            let mut curr = u;
            while curr != v {
                let (p_node, p_idx) = self.parent_edge[curr];
                self.adj[p_node][p_idx].cap -= 1;
                let rev = self.adj[p_node][p_idx].rev;
                self.adj[curr][rev].cap += 1;
                curr = p_node;
            }
            self.adj[u][idx].cap -= 1;
            let rev = self.adj[u][idx].rev;
            self.adj[v][rev].cap += 1;
        }
        let fix_val = if found {
            self.dist[u]
        } else {
            let max_dist = self
                .dist
                .iter()
                .filter(|&&d| d != inf)
                .max()
                .cloned()
                .unwrap_or(0);
            max_dist - rc
        };
        for i in 0..self.n {
            if self.dist[i] != inf {
                self.p[i] += self.dist[i];
            } else {
                self.p[i] += fix_val;
            }
        }
    }

    /// O(m (n + m) log n log U)
    pub fn calc(&mut self, s: usize, t: usize) -> (i64, i64, Vec<i64>) {
        self.adj.iter_mut().for_each(|adj| adj.clear());
        let mut edge_locs = Vec::with_capacity(self.input_edges.len());
        let mut max_cap = 0;
        let mut sum_cap = 0;
        let mut sum_cost_abs = 0;
        for e in &self.input_edges {
            max_cap = max_cap.max(e.cap);
            sum_cap += e.cap;
            sum_cost_abs += e.cost.abs();
            let fwd_idx = self.adj[e.from].len();
            let rev_idx = self.adj[e.to].len();
            edge_locs.push((e.from, fwd_idx));
            self.adj[e.from].push(CapacityScalingEdge {
                to: e.to,
                rev: rev_idx,
                cap: 0,
                cost: e.cost,
            });
            self.adj[e.to].push(CapacityScalingEdge {
                to: e.from,
                rev: fwd_idx,
                cap: 0,
                cost: -e.cost,
            });
        }
        let inf_cost = -(sum_cost_abs + 1);
        let t_s_idx = self.adj[t].len();
        let s_t_idx = self.adj[s].len();
        self.adj[t].push(CapacityScalingEdge {
            to: s,
            rev: s_t_idx,
            cap: 0,
            cost: inf_cost,
        });
        self.adj[s].push(CapacityScalingEdge {
            to: t,
            rev: t_s_idx,
            cap: 0,
            cost: -inf_cost,
        });
        let bits = (sum_cap as u64).next_power_of_two().ilog2() + 1;
        self.p.fill(0);
        for bit in (0..bits).rev() {
            for u in 0..self.n {
                for e in self.adj[u].iter_mut() {
                    e.cap <<= 1;
                }
            }
            for (i, &(u, idx)) in edge_locs.iter().enumerate() {
                if (self.input_edges[i].cap >> bit) & 1 == 1 {
                    self.push_capacity(u, idx);
                }
            }
            self.push_capacity(t, t_s_idx);
        }
        let flow = self.adj[s][s_t_idx].cap;
        let mut cost = 0;
        let mut flows = Vec::with_capacity(self.input_edges.len());
        for (i, &(u, idx)) in edge_locs.iter().enumerate() {
            let e_orig = &self.input_edges[i];
            let rev_idx = self.adj[u][idx].rev;
            let v = self.adj[u][idx].to;
            let edge_flow = self.adj[v][rev_idx].cap;
            flows.push(edge_flow);
            cost += edge_flow * e_orig.cost;
        }
        (flow, cost, flows)
    }
}

#[cfg(test)]
mod dinic_tests {
    use super::{Dinitz, PushRelabel};

    fn add_dinic_edges(d: &mut Dinitz, edges: &[(usize, usize, i64)]) {
        for &(a, b, cap) in edges {
            d.add_edge(a, b, cap, 0);
        }
    }

    fn add_pr_edges(pr: &mut PushRelabel<i64>, edges: &[(usize, usize, i64)]) {
        for &(a, b, cap) in edges {
            pr.add_edge(a, b, cap, 0);
        }
    }

    #[test]
    fn dinic_single_edge() {
        let mut d = Dinitz::new(2);
        d.add_edge(0, 1, 10, 0);
        assert_eq!(d.calc(0, 1), 10);
    }

    #[test]
    fn dinic_path_bottleneck() {
        // 0 -> 1 -> 2 -> 3, caps 5, 3, 7 => flow 3
        let mut d = Dinitz::new(4);
        add_dinic_edges(&mut d, &[(0, 1, 5), (1, 2, 3), (2, 3, 7)]);
        assert_eq!(d.calc(0, 3), 3);
    }

    #[test]
    fn dinic_disconnected() {
        let mut d = Dinitz::new(4);
        add_dinic_edges(&mut d, &[(0, 1, 1), (2, 3, 1)]);
        assert_eq!(d.calc(0, 3), 0);
    }

    #[test]
    fn dinic_same_source_sink() {
        let mut d = Dinitz::new(2);
        d.add_edge(0, 1, 10, 0);
        assert_eq!(d.calc(0, 0), 0);
        assert_eq!(d.calc(1, 1), 0);
    }

    #[test]
    fn dinic_two_paths() {
        // s=0, t=3. Paths 0->1->3 and 0->2->3 with caps 2 and 3 => flow 5
        let mut d = Dinitz::new(4);
        add_dinic_edges(&mut d, &[(0, 1, 2), (1, 3, 2), (0, 2, 3), (2, 3, 3)]);
        assert_eq!(d.calc(0, 3), 5);
    }

    #[test]
    fn dinic_matches_push_relabel() {
        let edges = &[(0, 1, 10), (0, 2, 5), (1, 2, 15), (1, 3, 10), (2, 3, 10)];
        let n = 4;
        let mut d = Dinitz::new(n);
        add_dinic_edges(&mut d, edges);
        let flow_dinic = d.calc(0, 3);

        let mut pr = PushRelabel::<i64>::new(n);
        add_pr_edges(&mut pr, edges);
        let flow_pr = pr.calc(0, 3);

        assert_eq!(flow_dinic, flow_pr, "Dinic and PushRelabel must agree");
        assert_eq!(flow_dinic, 15);
    }

    #[test]
    fn dinic_left_of_min_cut() {
        // 0 -> 1 -> 2, cap 1. After calc(0,2), flow is 1. Source 0 is left of min cut; sink 2 is not.
        // (Exact cut side depends on last BFS; we only require s is left, t is not.)
        let mut d = Dinitz::new(3);
        add_dinic_edges(&mut d, &[(0, 1, 1), (1, 2, 1)]);
        assert_eq!(d.calc(0, 2), 1);
        assert!(d.left_of_min_cut(0), "source must be left of min cut");
        assert!(!d.left_of_min_cut(2), "sink must be right of min cut");
    }

    #[test]
    fn dinic_flow_on_edge() {
        let mut d = Dinitz::new(2);
        d.add_edge(0, 1, 7, 0);
        assert_eq!(d.calc(0, 1), 7);
        assert_eq!(d.g[0][0].flow(), 7);
        assert_eq!(d.g[1][0].flow(), 0);
    }
}

// TODO: min cost b-flow using network simplex
// https://judge.yosupo.jp/submission/313861
