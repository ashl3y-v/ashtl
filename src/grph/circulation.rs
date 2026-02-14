use crate::ds::sort::counting_sort_by_key;
use crate::tree::lct::{LCT, LCTNode};

const EPS: f64 = 1e-12;

#[derive(Clone, Debug)]
pub struct CirculationRoundEdge {
    pub from: usize,
    pub to: usize,
    pub flow: f64,
    pub cost: f64,
}

fn is_integral(f: f64) -> bool {
    (f - f.round()).abs() < EPS
}

fn avail_fwd(f: f64) -> f64 {
    f.ceil() - f
}

fn avail_bwd(f: f64) -> f64 {
    f - f.floor()
}

/// O(m log n)
pub fn round_circulation(n: usize, edges: &mut [CirculationRoundEdge]) {
    #[derive(Clone, Debug)]
    struct CircLCTNode {
        vertex_id: usize,
        cost: f64,
        flow: f64,
        lazy: f64,
        has_edge: bool,
        edge_index: usize,
        cost_sum: f64,
        min_fwd: f64,
        min_fwd_node: usize,
        min_bwd: f64,
        min_bwd_node: usize,
    }
    impl Default for CircLCTNode {
        fn default() -> Self {
            Self {
                vertex_id: 0,
                cost: 0.0,
                flow: 0.0,
                lazy: 0.0,
                has_edge: false,
                edge_index: usize::MAX,
                cost_sum: 0.0,
                min_fwd: f64::INFINITY,
                min_fwd_node: usize::MAX,
                min_bwd: f64::INFINITY,
                min_bwd_node: usize::MAX,
            }
        }
    }
    fn circ_lct_pull([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<CircLCTNode>]) {
        if x == 0 {
            return;
        }
        let mut cost_sum = ns[x].v.cost;
        let mut min_fwd = ns[x].v.min_fwd;
        let mut min_fwd_node = ns[x].v.min_fwd_node;
        let mut min_bwd = ns[x].v.min_bwd;
        let mut min_bwd_node = ns[x].v.min_bwd_node;
        if ns[x].v.has_edge {
            let flow_eff = ns[x].v.flow + ns[x].v.lazy;
            let af = avail_fwd(flow_eff);
            let ab = avail_bwd(flow_eff);
            if af < min_fwd {
                min_fwd = af;
                min_fwd_node = ns[x].v.vertex_id;
            }
            if ab < min_bwd {
                min_bwd = ab;
                min_bwd_node = ns[x].v.vertex_id;
            }
        }
        if ch0 != 0 {
            cost_sum += ns[ch0].v.cost_sum;
            if ns[ch0].v.min_fwd < min_fwd {
                min_fwd = ns[ch0].v.min_fwd;
                min_fwd_node = ns[ch0].v.min_fwd_node;
            }
            if ns[ch0].v.min_bwd < min_bwd {
                min_bwd = ns[ch0].v.min_bwd;
                min_bwd_node = ns[ch0].v.min_bwd_node;
            }
        }
        if ch1 != 0 {
            cost_sum += ns[ch1].v.cost_sum;
            if ns[ch1].v.min_fwd < min_fwd {
                min_fwd = ns[ch1].v.min_fwd;
                min_fwd_node = ns[ch1].v.min_fwd_node;
            }
            if ns[ch1].v.min_bwd < min_bwd {
                min_bwd = ns[ch1].v.min_bwd;
                min_bwd_node = ns[ch1].v.min_bwd_node;
            }
        }
        ns[x].v.cost_sum = cost_sum;
        ns[x].v.min_fwd = min_fwd;
        ns[x].v.min_fwd_node = min_fwd_node;
        ns[x].v.min_bwd = min_bwd;
        ns[x].v.min_bwd_node = min_bwd_node;
    }
    fn circ_lct_push([x, ch0, ch1]: [usize; 3], ns: &mut [LCTNode<CircLCTNode>]) {
        if x == 0 {
            return;
        }
        let delta = ns[x].v.lazy;
        if delta.abs() < EPS {
            ns[x].v.lazy = 0.0;
            return;
        }
        if ns[x].v.has_edge {
            ns[x].v.flow += delta;
            if (ns[x].v.flow - ns[x].v.flow.round()).abs() < EPS {
                ns[x].v.flow = ns[x].v.flow.round();
            }
        }
        if ch0 != 0 {
            ns[ch0].v.lazy += delta;
        }
        if ch1 != 0 {
            ns[ch1].v.lazy += delta;
        }
        ns[x].v.lazy = 0.0;
    }
    fn circ_lct_rev(x: usize, ns: &mut [LCTNode<CircLCTNode>]) {
        if x == 0 {
            return;
        }
        ns[x].v.cost_sum = -ns[x].v.cost_sum;
        std::mem::swap(&mut ns[x].v.min_fwd, &mut ns[x].v.min_bwd);
        std::mem::swap(&mut ns[x].v.min_fwd_node, &mut ns[x].v.min_bwd_node);
    }
    if n == 0 || edges.is_empty() {
        return;
    }
    let m = edges.len();
    let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
    let floor_ceil: Vec<(f64, f64)> = initial.iter().map(|&f| (f.floor(), f.ceil())).collect();
    let init = CircLCTNode::default();
    let mut lct = LCT::with_capacity(n + m, init, circ_lct_pull, circ_lct_push, circ_lct_rev);
    for i in 0..n {
        let mut node = CircLCTNode::default();
        node.vertex_id = i;
        node.min_fwd_node = i;
        node.min_bwd_node = i;
        lct.add_node(node);
    }
    let mut eidx = 0;
    while eidx < m {
        let (u, v) = (edges[eidx].from, edges[eidx].to);
        let mut flow = edges[eidx].flow;
        let cost = edges[eidx].cost;
        if is_integral(flow) {
            eidx += 1;
            continue;
        }
        let ru = lct.first_on_path(u);
        let rv = lct.first_on_path(v);
        if ru != rv {
            lct.link(u, v);
            lct.update(u, |idx, _ch, ns| {
                ns[idx].v.cost = cost;
                ns[idx].v.flow = flow;
                ns[idx].v.has_edge = true;
                ns[idx].v.edge_index = eidx;
                ns[idx].v.cost_sum = cost;
                let af = avail_fwd(flow);
                let ab = avail_bwd(flow);
                ns[idx].v.min_fwd = af;
                ns[idx].v.min_fwd_node = u;
                ns[idx].v.min_bwd = ab;
                ns[idx].v.min_bwd_node = u;
            });
            eidx += 1;
            continue;
        }
        lct.make_root(u + 1);
        lct.access(v + 1);
        let (path_cost, path_min_fwd, path_min_bwd) = (
            lct.ns[v + 1].v.cost_sum,
            lct.ns[v + 1].v.min_fwd,
            lct.ns[v + 1].v.min_bwd,
        );
        let cycle_cost = path_cost + cost;
        let (push_dir_fwd, avail_path, avail_edge) = if cycle_cost >= 0.0 {
            (false, path_min_bwd, avail_bwd(flow))
        } else {
            (true, path_min_fwd, avail_fwd(flow))
        };
        let f = avail_path.min(avail_edge).max(0.0);
        if f <= EPS {
            eidx += 1;
            continue;
        }
        let delta = if push_dir_fwd { f } else { -f };
        let mut x = v + 1;
        while x != 0 {
            lct.push(x);
            lct.ns[x].v.lazy += delta;
            circ_lct_push([x, lct.ns[x].ch[0], 0], &mut lct.ns);
            x = lct.ns[x].ch[0];
        }
        lct.splay(x);
        flow += delta;
        edges[eidx].flow = flow;
        if is_integral(flow) {
            eidx += 1;
            continue;
        }
        let (path_min_fwd, path_min_bwd, min_fwd_node, min_bwd_node) = (
            lct.ns[v + 1].v.min_fwd,
            lct.ns[v + 1].v.min_bwd,
            lct.ns[v + 1].v.min_fwd_node,
            lct.ns[v + 1].v.min_bwd_node,
        );
        debug_assert!(path_min_fwd <= EPS || path_min_bwd <= EPS);
        let remove_node = if path_min_fwd <= EPS {
            min_fwd_node
        } else {
            min_bwd_node
        };
        let parent_of = |lct: &LCT<CircLCTNode, _, _, _>, node: usize| {
            let idx = node + 1;
            if lct.ns[idx].p == 0 {
                None
            } else {
                Some(lct.ns[idx].p - 1)
            }
        };
        let other = parent_of(&lct, remove_node).unwrap_or(u);
        lct.make_root(remove_node + 1);
        lct.access(other + 1);
        lct.push(remove_node);
        let flow_on_edge = lct.ns[remove_node + 1].v.flow;
        let ei = lct.ns[remove_node + 1].v.edge_index;
        let from = remove_node;
        let raw = if edges[ei].from == from {
            flow_on_edge
        } else {
            -flow_on_edge
        };
        edges[ei].flow = raw;
        lct.cut(remove_node, other);
    }
    for i in 1..=n {
        if lct.ns[i].v.has_edge && lct.ns[i].p != 0 {
            lct.access(i);
            let ei = lct.ns[i].v.edge_index;
            if ei != usize::MAX && ei < edges.len() {
                let flow = lct.ns[i].v.flow;
                let from = lct.ns[i].v.vertex_id;
                let raw = if edges[ei].from == from { flow } else { -flow };
                let (lo, hi) = floor_ceil[ei];
                edges[ei].flow = raw.clamp(lo, hi);
            }
        }
    }
    for e in edges.iter_mut() {
        e.flow = e.flow.floor();
    }
}

/// O(m + n)
pub fn greedy_round_circulation(
    n: usize,
    edges: &mut [CirculationRoundEdge],
    root: usize,
    parent: &[usize],
    is_tree_edge: impl Fn(usize) -> bool,
) {
    if n == 0 || edges.is_empty() {
        return;
    }
    let floor_ceil: Vec<(f64, f64)> = edges
        .iter()
        .map(|e| (e.flow.floor(), e.flow.ceil()))
        .collect();
    let mut depth = vec![0_usize; n];
    for u in 0..n {
        if u != root {
            depth[u] = depth[parent[u]] + 1;
        }
    }
    let mut tree_edge_idx = vec![usize::MAX; n];
    for (i, e) in edges.iter().enumerate() {
        if !is_tree_edge(i) {
            continue;
        }
        let (a, b) = (e.from, e.to);
        if a < n && parent[a] == b {
            tree_edge_idx[a] = i;
        } else if b < n && parent[b] == a {
            tree_edge_idx[b] = i;
        }
    }
    for e in edges.iter_mut() {
        e.flow = e.flow.floor();
    }
    let mut excess: Vec<i64> = vec![0; n];
    for e in edges.iter() {
        let f = e.flow as i64;
        excess[e.from] -= f;
        excess[e.to] += f;
    }
    let mut back_edges: Vec<(usize, usize, usize)> = Vec::new();
    for (i, e) in edges.iter().enumerate() {
        if is_tree_edge(i) {
            continue;
        }
        let (from, to) = (e.from, e.to);
        if from >= n || to >= n {
            continue;
        }
        if depth[to] < depth[from] {
            back_edges.push((i, to, from));
        } else if depth[from] < depth[to] {
            back_edges.push((i, from, to));
        }
    }
    counting_sort_by_key(&mut back_edges, n + 1, |(_, anc, _)| depth[*anc]);
    let mut tin = vec![0; n];
    let mut tout = vec![0; n];
    let mut tick = 0;
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n];
    for u in 0..n {
        if u != root {
            children[parent[u]].push(u);
        }
    }
    fn dfs_time(
        u: usize,
        children: &[Vec<usize>],
        in_time: &mut [usize],
        out_time: &mut [usize],
        time: &mut usize,
    ) {
        in_time[u] = *time;
        *time += 1;
        for &c in &children[u] {
            dfs_time(c, children, in_time, out_time, time);
        }
        out_time[u] = *time;
        *time += 1;
    }
    dfs_time(root, &children, &mut tin, &mut tout, &mut tick);
    fn rec(
        u: usize,
        n: usize,
        root: usize,
        in_time: &[usize],
        out_time: &[usize],
        parent: &[usize],
        children: &[Vec<usize>],
        tree_edge_idx: &[usize],
        excess: &mut [i64],
        edges: &mut [CirculationRoundEdge],
        floor_ceil: &[(f64, f64)],
        back_edges: &[(usize, usize, usize)],
        idx: &mut usize,
    ) {
        for &c in &children[u] {
            rec(
                c,
                n,
                root,
                in_time,
                out_time,
                parent,
                children,
                tree_edge_idx,
                excess,
                edges,
                floor_ceil,
                back_edges,
                idx,
            );
        }
        let need = excess[u];
        if need > 0 {
            let mut back_used = 0;
            while back_used < need && *idx < back_edges.len() {
                let (ei, anc, desc) = back_edges[*idx];
                let in_u = in_time[u];
                let out_u = out_time[u];
                let in_d = in_time[desc];
                if in_d >= in_u && in_d <= out_u {
                    let (_lo, hi) = floor_ceil[ei];
                    let add = 1.0_f64.min(hi - edges[ei].flow);
                    if add > 0.0 {
                        edges[ei].flow += add;
                        excess[anc] += add as i64;
                        back_used += add as i64;
                    }
                }
                *idx += 1;
            }
            let rest = need - back_used;
            if rest > 0 && u != root && tree_edge_idx[u] != usize::MAX {
                let te = tree_edge_idx[u];
                let (_lo, hi) = floor_ceil[te];
                let add = rest as f64;
                edges[te].flow = (edges[te].flow + add).min(hi);
                excess[parent[u]] += rest;
            }
        } else if need < 0 && u != root && tree_edge_idx[u] != usize::MAX {
            let te = tree_edge_idx[u];
            let (lo, _hi) = floor_ceil[te];
            edges[te].flow = (edges[te].flow + need as f64).max(lo);
            excess[parent[u]] += need;
        }
    }
    let mut idx = 0;
    rec(
        root,
        n,
        root,
        &tin,
        &tout,
        parent,
        &children,
        &tree_edge_idx,
        &mut excess,
        edges,
        &floor_ceil,
        &back_edges,
        &mut idx,
    );
    for (e, &(lo, hi)) in edges.iter_mut().zip(floor_ceil.iter()) {
        e.flow = e.flow.clamp(lo, hi);
    }
}

/// O(d (m + n))
pub fn greedy_split_circulation(
    n: usize,
    edges: &[CirculationRoundEdge],
    root: usize,
    parent: &[usize],
    is_tree_edge: impl Fn(usize) -> bool,
    d: usize,
) -> Vec<Vec<i64>> {
    let m = edges.len();
    let d = d.max(1);
    if n == 0 || m == 0 {
        return vec![vec![0; m]; d];
    }
    if d == 1 {
        return vec![edges.iter().map(|e| e.flow.round() as i64).collect()];
    }
    let mut layer0_edges: Vec<CirculationRoundEdge> = edges
        .iter()
        .map(|e| CirculationRoundEdge {
            from: e.from,
            to: e.to,
            flow: e.flow / d as f64,
            cost: e.cost,
        })
        .collect();
    greedy_round_circulation(n, &mut layer0_edges, root, parent, &is_tree_edge);
    let layer0 = layer0_edges
        .iter()
        .map(|e| e.flow as i64)
        .collect::<Vec<_>>();
    let rest_edges: Vec<CirculationRoundEdge> = edges
        .iter()
        .zip(layer0.iter())
        .map(|(e, &a)| CirculationRoundEdge {
            from: e.from,
            to: e.to,
            flow: e.flow - a as f64,
            cost: e.cost,
        })
        .collect();
    let mut rest_layers =
        greedy_split_circulation(n, &rest_edges, root, parent, is_tree_edge, d - 1);
    let mut out = vec![layer0];
    out.append(&mut rest_layers);
    out
}

#[cfg(test)]
mod circulation_rounding_tests {
    use super::{
        CirculationRoundEdge, greedy_round_circulation, greedy_split_circulation, round_circulation,
    };
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    const EPS: f64 = 1e-9;

    fn is_integral(f: f64) -> bool {
        (f - f.round()).abs() < 1e-9
    }

    fn assert_initial_circulation(n: usize, edges: &[CirculationRoundEdge], eps: f64) {
        let mut balance = vec![0.0_f64; n];
        for e in edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for (i, &b) in balance.iter().enumerate() {
            assert!(
                b.abs() < eps,
                "node {} imbalance {} (initial not a circulation)",
                i,
                b
            );
        }
    }

    fn assert_valid_rounding(n: usize, edges: &[CirculationRoundEdge], initial_flows: &[f64]) {
        const EPS: f64 = 1e-9;
        for (i, e) in edges.iter().enumerate() {
            let f = e.flow;
            assert!(
                (f - f.round()).abs() < EPS,
                "edge {} ({},{}) flow {} not integral",
                i,
                e.from,
                e.to,
                f
            );
            let lo = initial_flows[i].floor();
            let hi = initial_flows[i].ceil();
            assert!(
                f >= lo - EPS && f <= hi + EPS,
                "edge {} flow {} outside [floor,ceil] = [{},{}] of initial {}",
                i,
                f,
                lo,
                hi,
                initial_flows[i]
            );
        }
        let mut balance = vec![0.0_f64; n];
        for e in edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for (i, &b) in balance.iter().enumerate() {
            assert!(
                b.abs() < EPS,
                "node {} imbalance {} (not a circulation)",
                i,
                b
            );
        }
    }

    fn round_and_assert(n: usize, edges: &mut [CirculationRoundEdge], initial: &[f64]) {
        assert_initial_circulation(n, edges, EPS);
        round_circulation(n, edges);
        assert_valid_rounding(n, edges, initial);
    }

    fn round_and_assert_o_m_log_n(n: usize, edges: &mut [CirculationRoundEdge], initial: &[f64]) {
        round_and_assert(n, edges, initial);
    }

    #[test]
    fn regression_sparse_must_succeed_theta() {
        let f = 0.25;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 0,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: 2.0 * f,
                cost: 0.0,
            },
        ];
        assert_initial_circulation(4, &edges, EPS);
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_circulation(4, &mut edges);
        assert_valid_rounding(4, &edges, &initial);
    }

    #[test]
    fn regression_sparse_must_succeed_wheel_fractional() {
        let n = 8;
        let mut edges = wheel_edges(n, 0.3, 0.2);
        assert_initial_circulation(n, &edges, EPS);
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_circulation(n, &mut edges);
        assert_valid_rounding(n, &edges, &initial);
    }

    #[test]
    fn regression_sparse_must_succeed_barbell_two_triangles() {
        let f = 1.0 / 3.0;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 2.0 * f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: f,
                cost: 0.0,
            },
        ];
        round_and_assert(4, &mut edges, &[2.0 * f, f, f, f, f]);
    }

    #[test]
    fn round_circulation_triangle_conservation() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 1.0,
            },
        ];
        round_and_assert(3, &mut edges, &[0.4, 0.4, 0.4]);
    }

    #[test]
    fn round_circulation_small_graph() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 1.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: 1.5,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(2, &mut edges, &initial);
    }

    #[test]
    fn greedy_round_circulation_four_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.7,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.7,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.7,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.7,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        assert_initial_circulation(4, &edges, EPS);
        let parent = [0, 0, 1, 2];
        greedy_round_circulation(4, &mut edges, 0, &parent, |i| i < 3);
        assert_valid_rounding(4, &edges, &initial);
    }

    #[test]
    fn greedy_circulation_split_four_cycle() {
        let edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 2.0,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 2.0,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 2.0,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 2.0,
                cost: 0.0,
            },
        ];
        let parent = [0, 0, 1, 2];
        let layers = greedy_split_circulation(4, &edges, 0, &parent, |i| i < 3, 2);
        assert_eq!(layers.len(), 2);
        assert_eq!(layers[0].len(), 4);
        for k in 0..2 {
            let mut balance = vec![0.0; 4];
            for (e, &f) in edges.iter().zip(layers[k].iter()) {
                balance[e.from] -= f as f64;
                balance[e.to] += f as f64;
            }
            for &b in &balance {
                assert!(
                    b.abs() < EPS,
                    "layer {} not a circulation: balance {:?}",
                    k,
                    balance
                );
            }
        }
        for (ei, e) in edges.iter().enumerate() {
            let sum: f64 = layers.iter().map(|l| l[ei] as f64).sum();
            assert!(
                (sum - e.flow).abs() < EPS,
                "edge {} flow sum {} != {}",
                ei,
                sum,
                e.flow
            );
        }
    }

    #[test]
    fn round_circulation_four_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.7,
                cost: -1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.7,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(4, &mut edges, &initial);
    }

    #[test]
    fn round_circulation_two_triangles() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 4,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 4,
                to: 5,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 5,
                to: 3,
                flow: 0.8,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(6, &mut edges, &initial);
    }

    #[test]
    fn round_circulation_all_integral_unchanged() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 1.0,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 1.0,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 1.0,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(3, &mut edges, &initial);
        assert_eq!(edges[0].flow, 1.0);
        assert_eq!(edges[1].flow, 1.0);
        assert_eq!(edges[2].flow, 1.0);
    }

    #[test]
    fn round_circulation_mixed_fractional_integral() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.5,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(3, &mut edges, &initial);
    }

    #[test]
    fn round_circulation_floor_preserves_conservation() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.3,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: 0.3,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(2, &mut edges, &initial);
        assert_eq!(edges[0].flow, 0.0);
        assert_eq!(edges[1].flow, 0.0);
    }

    #[test]
    fn round_circulation_chain_with_back_flow() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.5,
                cost: 0.0,
            },
        ];
        let mut bal = vec![0.0_f64; 4];
        for e in &edges {
            bal[e.from] -= e.flow;
            bal[e.to] += e.flow;
        }
        for &b in &bal {
            assert!(b.abs() < 1e-9, "initial not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(4, &mut edges, &initial);
    }

    #[test]
    fn round_circulation_cost_direction_negative_cost_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.5,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.5,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.5,
                cost: -3.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(3, &mut edges, &initial);
    }

    #[test]
    fn round_circulation_larger_n() {
        let n = 20;
        let mut edges = Vec::new();
        for i in 0..n {
            let j = (i + 1) % n;
            edges.push(CirculationRoundEdge {
                from: i,
                to: j,
                flow: 0.33,
                cost: 1.0,
            });
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(n, &mut edges, &initial);
    }

    #[test]
    fn rigorous_exhaustive_triangle_flows() {
        for f in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 0,
                    flow: f,
                    cost: 1.0,
                },
            ];
            let initial = vec![f, f, f];
            round_and_assert(3, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_exhaustive_two_node_flows() {
        for f in [0.1, 0.5, 0.99, 1.0, 1.5, 2.3, 10.0] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 0,
                    flow: f,
                    cost: 0.0,
                },
            ];
            let initial = vec![f, f];
            round_and_assert(2, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_random_cycle_100() {
        let mut rng = rand::rng();
        for _ in 0..100 {
            let n = rng.random_range(3..=50);
            let f: f64 = rng.random_range(0.01..=1.0);
            let mut edges = Vec::new();
            for i in 0..n {
                let j = (i + 1) % n;
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: j,
                    flow: f,
                    cost: rng.random_range(-10.0..10.0),
                });
            }
            let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_and_assert(n, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_random_two_node_50() {
        let mut rng = rand::rng();
        for _ in 0..50 {
            let f: f64 = rng.random_range(0.01..=10.0);
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: rng.random_range(-5.0..5.0),
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 0,
                    flow: f,
                    cost: rng.random_range(-5.0..5.0),
                },
            ];
            let initial = vec![f, f];
            round_and_assert(2, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_random_triangle_50() {
        let mut rng = rand::rng();
        for _ in 0..50 {
            let f: f64 = rng.random_range(0.01..=2.0);
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: rng.random_range(-3.0..3.0),
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: rng.random_range(-3.0..3.0),
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 0,
                    flow: f,
                    cost: rng.random_range(-3.0..3.0),
                },
            ];
            let initial = vec![f, f, f];
            round_and_assert(3, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_bipartite_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 1,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 3,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.25,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(4, &mut edges, &initial);
    }

    #[test]
    fn rigorous_four_cycle_many_flows() {
        for f in [0.25, 0.5, 0.7, 0.99, 1.0] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 3,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 3,
                    to: 0,
                    flow: f,
                    cost: 0.0,
                },
            ];
            let initial = vec![f, f, f, f];
            round_and_assert(4, &mut edges, &initial);
        }
    }

    #[test]
    fn rigorous_reverse_edge_availability_trap() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 1.0,
            },
        ];
        let initial = vec![0.4, 0.4, 0.4];
        round_and_assert(3, &mut edges, &initial);
        for (i, e) in edges.iter().enumerate() {
            assert!(is_integral(e.flow), "edge {} not integral: {}", i, e.flow);
            assert!(
                (0.0..=1.0).contains(&e.flow),
                "edge {} flow {} outside [0,1]",
                i,
                e.flow
            );
        }
    }

    #[test]
    fn rigorous_path_down_mark_trap() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.7,
                cost: -1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.7,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(4, &mut edges, &initial);
    }

    #[test]
    fn rigorous_disjoint_components() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 4,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 4,
                to: 5,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 5,
                to: 3,
                flow: 0.8,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(6, &mut edges, &initial);
    }

    #[test]
    fn rigorous_large_cycle_stress() {
        let n = 100;
        let mut edges = Vec::new();
        for i in 0..n {
            let j = (i + 1) % n;
            edges.push(CirculationRoundEdge {
                from: i,
                to: j,
                flow: 0.12345,
                cost: 1.0,
            });
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert(n, &mut edges, &initial);
    }

    #[test]
    fn rigorous_reproducible_seed() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for &n in &[3, 4, 5, 10, 15] {
            let f: f64 = rng.random_range(0.1..=0.9);
            let mut edges = Vec::new();
            for i in 0..n {
                let j = (i + 1) % n;
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: j,
                    flow: f,
                    cost: 1.0,
                });
            }
            let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_and_assert(n, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_triangle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 1.0,
            },
        ];
        let initial = vec![0.4, 0.4, 0.4];
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_four_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.25,
                cost: 1.0,
            },
        ];
        let initial = vec![0.25, 0.25, 0.25, 0.25];
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_two_triangles() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.2,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 4,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 4,
                to: 5,
                flow: 0.8,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 5,
                to: 3,
                flow: 0.8,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(6, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_path_down_trap() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.7,
                cost: -1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.7,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.7,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_large_cycle() {
        let n = 100;
        let mut edges = Vec::new();
        for i in 0..n {
            let j = (i + 1) % n;
            edges.push(CirculationRoundEdge {
                from: i,
                to: j,
                flow: 0.12345,
                cost: 1.0,
            });
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_simple_4_and_5_cycle() {
        let f4 = 1.0 / 3.0;
        let mut edges4 = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: f4,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: f4,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: f4,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: f4,
                cost: 0.0,
            },
        ];
        let initial4: Vec<f64> = edges4.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges4, &initial4);

        let f5 = 0.2;
        let mut edges5 = Vec::new();
        for i in 0..5 {
            edges5.push(CirculationRoundEdge {
                from: i,
                to: (i + 1) % 5,
                flow: f5,
                cost: 0.0,
            });
        }
        let initial5: Vec<f64> = edges5.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(5, &mut edges5, &initial5);
    }

    #[test]
    fn o_m_log_n_k4() {
        let f = 1.0 / 3.0;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: f,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_empty() {
        let mut edges: Vec<CirculationRoundEdge> = Vec::new();
        round_circulation(0, &mut edges);
        assert!(edges.is_empty());
    }

    #[test]
    fn o_m_log_n_single_node_no_edges() {
        let mut edges: Vec<CirculationRoundEdge> = Vec::new();
        round_circulation(1, &mut edges);
        assert!(edges.is_empty());
    }

    #[test]
    fn o_m_log_n_all_integral_unchanged() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 1.0,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 1.0,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 1.0,
                cost: 1.0,
            },
        ];
        let initial = vec![1.0, 1.0, 1.0];
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
        assert_eq!(edges[0].flow, 1.0, "integral edge must stay 1");
        assert_eq!(edges[1].flow, 1.0, "integral edge must stay 1");
        assert_eq!(edges[2].flow, 1.0, "integral edge must stay 1");
    }

    #[test]
    fn o_m_log_n_floor_preserves_conservation() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.3,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: 0.3,
                cost: 0.0,
            },
        ];
        let initial = vec![0.3, 0.3];
        round_and_assert_o_m_log_n(2, &mut edges, &initial);
        assert_eq!(edges[0].flow, 0.0);
        assert_eq!(edges[1].flow, 0.0);
    }

    #[test]
    fn o_m_log_n_idempotence() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 1.0,
            },
        ];
        let initial = vec![0.4, 0.4, 0.4];
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
        let after_first: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_circulation(3, &mut edges);
        for (i, e) in edges.iter().enumerate() {
            assert!(
                (e.flow - after_first[i]).abs() < EPS,
                "idempotence: edge {} flow changed from {} to {}",
                i,
                after_first[i],
                e.flow
            );
        }
    }

    #[test]
    fn o_m_log_n_rigorous_reverse_edge_availability_trap() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 1.0,
            },
        ];
        let initial = vec![0.4, 0.4, 0.4];
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
        for (i, e) in edges.iter().enumerate() {
            assert!(is_integral(e.flow), "edge {} not integral: {}", i, e.flow);
            assert!(
                (0.0..=1.0).contains(&e.flow),
                "edge {} flow {} outside [0,1]",
                i,
                e.flow
            );
        }
    }

    #[test]
    fn o_m_log_n_rigorous_bipartite_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 1,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 3,
                flow: 0.25,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.25,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_rigorous_four_cycle_many_flows() {
        for f in [0.25, 0.5, 0.7, 0.99, 1.0] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 3,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 3,
                    to: 0,
                    flow: f,
                    cost: 0.0,
                },
            ];
            let initial = vec![f, f, f, f];
            round_and_assert_o_m_log_n(4, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_stress_small_dense() {
        let mut edges = Vec::new();
        for i in 0..4 {
            for j in 0..4 {
                if i != j {
                    edges.push(CirculationRoundEdge {
                        from: i,
                        to: j,
                        flow: 0.25,
                        cost: 1.0,
                    });
                }
            }
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        assert_initial_circulation(4, &edges, EPS);
        round_circulation(4, &mut edges);
        assert_valid_rounding(4, &edges, &initial);
    }

    #[test]
    fn o_m_log_n_chain_with_back_flow() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: 0.5,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: 0.5,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_cost_direction_negative_cost_cycle() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.5,
                cost: 1.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.5,
                cost: -2.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.5,
                cost: 1.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_exhaustive_triangle_flows() {
        for f in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 0,
                    flow: f,
                    cost: 1.0,
                },
            ];
            let initial = vec![f, f, f];
            round_and_assert_o_m_log_n(3, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_exhaustive_two_node_flows() {
        for f in [0.1, 0.5, 0.99, 1.0, 1.5, 2.3, 10.0] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 0,
                    flow: f,
                    cost: 0.0,
                },
            ];
            let initial = vec![f, f];
            round_and_assert_o_m_log_n(2, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_reproducible_seed() {
        let mut rng = StdRng::seed_from_u64(42);
        for &n in &[3, 4, 5, 10, 15, 20] {
            let f: f64 = rng.random_range(0.1..=0.9);
            let mut edges = Vec::new();
            for i in 0..n {
                let j = (i + 1) % n;
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: j,
                    flow: f,
                    cost: 1.0,
                });
            }
            let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_and_assert_o_m_log_n(n, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_random_many_seeds() {
        let pairs: Vec<(usize, f64)> = (3..=25)
            .flat_map(|n| [0.2, 0.33, 0.5, 0.7, 0.9].iter().map(move |&f| (n, f)))
            .take(50)
            .collect();
        for (n, f) in pairs {
            let mut edges = Vec::new();
            for i in 0..n {
                let j = (i + 1) % n;
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: j,
                    flow: f,
                    cost: 1.0,
                });
            }
            let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_and_assert_o_m_log_n(n, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_larger_stress() {
        let n = 200;
        let mut edges = Vec::new();
        for i in 0..n {
            let j = (i + 1) % n;
            edges.push(CirculationRoundEdge {
                from: i,
                to: j,
                flow: 0.33333,
                cost: 1.0,
            });
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn exhaustive_triangle_and_two_node_flows() {
        for f in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 2,
                    flow: f,
                    cost: 1.0,
                },
                CirculationRoundEdge {
                    from: 2,
                    to: 0,
                    flow: f,
                    cost: 1.0,
                },
            ];
            let initial = vec![f, f, f];
            round_and_assert(3, &mut edges, &initial);
        }
        for f in [0.1, 0.5, 0.99, 1.0, 1.5, 2.3, 10.0] {
            let mut edges = vec![
                CirculationRoundEdge {
                    from: 0,
                    to: 1,
                    flow: f,
                    cost: 0.0,
                },
                CirculationRoundEdge {
                    from: 1,
                    to: 0,
                    flow: f,
                    cost: 0.0,
                },
            ];
            let initial = vec![f, f];
            round_and_assert(2, &mut edges, &initial);
        }
    }

    #[test]
    fn cycles_various_sizes() {
        for &(n, f) in &[
            (3, 0.4),
            (4, 0.25),
            (5, 0.5),
            (6, 0.2),
            (10, 0.33),
            (15, 0.7),
            (20, 0.123),
        ] {
            let mut edges = Vec::new();
            for i in 0..n {
                let j = (i + 1) % n;
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: j,
                    flow: f,
                    cost: 1.0,
                });
            }
            let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_and_assert(n, &mut edges, &initial);
        }
    }

    #[test]
    fn tricky_instances() {
        let instances: Vec<(usize, Vec<CirculationRoundEdge>)> = vec![
            (
                6,
                vec![
                    CirculationRoundEdge {
                        from: 0,
                        to: 1,
                        flow: 0.2,
                        cost: 0.0,
                    },
                    CirculationRoundEdge {
                        from: 1,
                        to: 2,
                        flow: 0.2,
                        cost: 0.0,
                    },
                    CirculationRoundEdge {
                        from: 2,
                        to: 0,
                        flow: 0.2,
                        cost: 0.0,
                    },
                    CirculationRoundEdge {
                        from: 3,
                        to: 4,
                        flow: 0.8,
                        cost: 0.0,
                    },
                    CirculationRoundEdge {
                        from: 4,
                        to: 5,
                        flow: 0.8,
                        cost: 0.0,
                    },
                    CirculationRoundEdge {
                        from: 5,
                        to: 3,
                        flow: 0.8,
                        cost: 0.0,
                    },
                ],
            ),
            (
                4,
                vec![
                    CirculationRoundEdge {
                        from: 0,
                        to: 1,
                        flow: 0.7,
                        cost: -1.0,
                    },
                    CirculationRoundEdge {
                        from: 1,
                        to: 2,
                        flow: 0.7,
                        cost: 1.0,
                    },
                    CirculationRoundEdge {
                        from: 2,
                        to: 3,
                        flow: 0.7,
                        cost: 1.0,
                    },
                    CirculationRoundEdge {
                        from: 3,
                        to: 0,
                        flow: 0.7,
                        cost: 1.0,
                    },
                ],
            ),
            (
                4,
                vec![
                    CirculationRoundEdge {
                        from: 0,
                        to: 2,
                        flow: 0.25,
                        cost: 1.0,
                    },
                    CirculationRoundEdge {
                        from: 2,
                        to: 1,
                        flow: 0.25,
                        cost: 1.0,
                    },
                    CirculationRoundEdge {
                        from: 1,
                        to: 3,
                        flow: 0.25,
                        cost: 1.0,
                    },
                    CirculationRoundEdge {
                        from: 3,
                        to: 0,
                        flow: 0.25,
                        cost: 1.0,
                    },
                ],
            ),
        ];
        for (n, edges_input) in instances {
            let initial: Vec<f64> = edges_input.iter().map(|e| e.flow).collect();
            let mut edges = edges_input;
            round_and_assert(n, &mut edges, &initial);
        }
    }

    #[test]
    fn o_m_log_n_wheel() {
        let n = 8;
        let mut edges = wheel_edges(n, 0.25, 0.25);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    fn wheel_edges(n: usize, f_spoke: f64, f_rim: f64) -> Vec<CirculationRoundEdge> {
        let mut edges = Vec::new();
        for i in 1..n {
            edges.push(CirculationRoundEdge {
                from: 0,
                to: i,
                flow: f_spoke,
                cost: 0.0,
            });
            edges.push(CirculationRoundEdge {
                from: i,
                to: 0,
                flow: f_spoke,
                cost: 0.0,
            });
        }
        for i in 1..n {
            let j = if i == n - 1 { 1 } else { i + 1 };
            edges.push(CirculationRoundEdge {
                from: i,
                to: j,
                flow: f_rim,
                cost: 0.0,
            });
        }
        edges
    }

    #[test]
    fn o_m_log_n_wheel_n_6() {
        let n = 6;
        let mut edges = wheel_edges(n, 0.25, 0.25);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_wheel_n_10() {
        let n = 10;
        let mut edges = wheel_edges(n, 0.25, 0.25);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_wheel_n_12() {
        let n = 12;
        let mut edges = wheel_edges(n, 0.25, 0.25);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_wheel_fractional() {
        let n = 8;
        let mut edges = wheel_edges(n, 0.3, 0.2);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_wheel_odd() {
        let n = 7;
        let mut edges = wheel_edges(n, 1.0 / 7.0, 1.0 / 7.0);
        let mut balance = vec![0.0; n];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "wheel not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_three_overlapping_triangles() {
        let f = 1.0 / 3.0;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 0,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: f,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_barbell_two_triangles() {
        let f = 1.0 / 3.0;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 2.0 * f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 0,
                flow: f,
                cost: 0.0,
            },
        ];
        let mut balance = vec![0.0; 4];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "barbell not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_theta() {
        let f = 0.25;
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 2,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 0,
                to: 3,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 3,
                to: 1,
                flow: f,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 0,
                flow: 2.0 * f,
                cost: 0.0,
            },
        ];
        let mut balance = vec![0.0; 4];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "theta not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_k4_uniform() {
        let f = 1.0 / 3.0;
        let mut edges = Vec::new();
        for i in 0..4 {
            for j in 0..4 {
                if i != j {
                    edges.push(CirculationRoundEdge {
                        from: i,
                        to: j,
                        flow: f,
                        cost: 0.0,
                    });
                }
            }
        }
        let mut balance = vec![0.0; 4];
        for e in &edges {
            balance[e.from] -= e.flow;
            balance[e.to] += e.flow;
        }
        for &b in &balance {
            assert!(b.abs() < EPS, "K4 not a circulation");
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(4, &mut edges, &initial);
    }

    #[test]
    fn o_m_log_n_stress_500_cycle() {
        let n = 500;
        let mut edges = Vec::new();
        for i in 0..n {
            edges.push(CirculationRoundEdge {
                from: i,
                to: (i + 1) % n,
                flow: 0.27182,
                cost: 1.0,
            });
        }
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(n, &mut edges, &initial);
    }

    #[test]
    fn cycles_many_fixed() {
        for n in [4, 5, 6, 8, 10, 12, 15, 20, 25] {
            for f in [0.2, 0.25, 0.33, 0.5, 0.67, 0.8] {
                let mut edges = Vec::new();
                for i in 0..n {
                    edges.push(CirculationRoundEdge {
                        from: i,
                        to: (i + 1) % n,
                        flow: f,
                        cost: 1.0,
                    });
                }
                let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
                round_and_assert(n, &mut edges, &initial);
            }
        }
    }

    #[test]
    fn o_m_log_n_idempotence_three_cases() {
        for (n, flows) in [
            (3, vec![0.4, 0.4, 0.4]),
            (4, vec![0.25, 0.25, 0.25, 0.25]),
            (5, vec![0.2, 0.2, 0.2, 0.2, 0.2]),
        ] {
            let mut edges = Vec::new();
            for i in 0..n {
                edges.push(CirculationRoundEdge {
                    from: i,
                    to: (i + 1) % n,
                    flow: flows[i],
                    cost: 1.0,
                });
            }
            round_circulation(n, &mut edges);
            let after_first: Vec<f64> = edges.iter().map(|e| e.flow).collect();
            round_circulation(n, &mut edges);
            for (i, e) in edges.iter().enumerate() {
                assert!(
                    (e.flow - after_first[i]).abs() < EPS,
                    "idempotence failed at edge {}: {} vs {}",
                    i,
                    after_first[i],
                    e.flow
                );
            }
        }
    }

    #[test]
    fn o_m_log_n_sum_flow_invariant() {
        let mut edges = vec![
            CirculationRoundEdge {
                from: 0,
                to: 1,
                flow: 0.4,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 1,
                to: 2,
                flow: 0.4,
                cost: 0.0,
            },
            CirculationRoundEdge {
                from: 2,
                to: 0,
                flow: 0.4,
                cost: 0.0,
            },
        ];
        let initial: Vec<f64> = edges.iter().map(|e| e.flow).collect();
        round_and_assert_o_m_log_n(3, &mut edges, &initial);
        let mut out0 = 0.0;
        let mut in0 = 0.0;
        for e in &edges {
            if e.from == 0 {
                out0 += e.flow;
            }
            if e.to == 0 {
                in0 += e.flow;
            }
        }
        assert!(
            (out0 - in0).abs() < EPS,
            "conservation at 0: out {} in {}",
            out0,
            in0
        );
    }
}
