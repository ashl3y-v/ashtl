use std::{collections::HashMap, f64::consts::SQRT_2};

use crate::ds::dsu::DSU;
use rand::prelude::SliceRandom;

/// O(m α(n))
pub fn contract(
    n: usize,
    es: &[(usize, usize, usize)],
    t: usize,
) -> (usize, Vec<(usize, usize, usize)>) {
    let m = es.len();
    if m == 0 || n < 2 {
        return (n, es.to_vec());
    }
    let mut rng = rand::rng();
    let mut indices: Vec<usize> = (0..m).collect();
    indices.shuffle(&mut rng);
    let mut dsu = DSU::new(n);
    let mut current_components = n;
    for &i in &indices {
        if current_components <= t {
            break;
        }
        let (u, v, _) = es[i];
        if dsu.union(u, v).1 {
            current_components -= 1;
        }
    }
    let mut component_ids = vec![usize::MAX; n];
    let mut next_comp_id = 0;
    let mut root_to_comp = vec![usize::MAX; n];
    for i in 0..n {
        let root = dsu.find(i);
        if root_to_comp[root] == usize::MAX {
            root_to_comp[root] = next_comp_id;
            next_comp_id += 1;
        }
        component_ids[i] = root_to_comp[root];
    }
    let mut new_edges = Vec::with_capacity(m);
    for &(u, v, id) in es {
        let comp_u = component_ids[u];
        let comp_v = component_ids[v];
        if comp_u != comp_v {
            new_edges.push((comp_u, comp_v, id));
        }
    }

    (next_comp_id, new_edges)
}

/// O(n^2 log^3 n α(n))
pub fn karger_stein(n: usize, raw_edges: &[(usize, usize)]) -> (usize, Vec<usize>) {
    let edges_with_id: Vec<(usize, usize, usize)> = raw_edges
        .iter()
        .enumerate()
        .map(|(i, &(u, v))| (u, v, i))
        .collect();
    fn calc_p(n: usize, memo: &mut HashMap<usize, f64>) -> f64 {
        if n <= 6 {
            return 1.0;
        } else if let Some(&p) = memo.get(&n) {
            return p;
        }
        let t = (1.0 + (n as f64) / SQRT_2).ceil() as usize;
        let p_next = calc_p(t, memo);
        let term = 1.0 - 0.5 * p_next;
        let p_n = 1.0 - (term * term);
        memo.insert(n, p_n);
        p_n
    }
    fn rec(n: usize, es: &[(usize, usize, usize)]) -> Vec<usize> {
        if n <= 6 {
            let (_, final_edges) = contract(n, es, 2);
            return final_edges.iter().map(|&(_, _, id)| id).collect();
        }
        let t = (1.0 + (n as f64) / SQRT_2).ceil() as usize;
        let (n1, e1) = contract(n, es, t);
        let cut1 = rec(n1, &e1);
        let (n2, e2) = contract(n, es, t);
        let cut2 = rec(n2, &e2);
        if cut1.len() < cut2.len() { cut1 } else { cut2 }
    }
    let mut memo = HashMap::new();
    let p_n = calc_p(n, &mut memo);
    let mut repetitions = (((n / 5) as f64).ln() / p_n).ceil() as usize;
    if n <= 6 {
        repetitions = n * (n - 1) / 2 * (n as f64).ln().ceil() as usize;
    }
    let repetitions = repetitions.max(1);
    let mut best_cut = Vec::new();
    let mut min_cut_size = usize::MAX;
    for _ in 0..repetitions {
        let cut_indices = rec(n, &edges_with_id);
        if cut_indices.len() < min_cut_size {
            min_cut_size = cut_indices.len();
            best_cut = cut_indices;
        }
    }
    (min_cut_size, best_cut)
}

/// Approximate Cheeger partition by spectral sweep on the normalized Laplacian.
///
/// Returns `(phi, side)` where `phi` is the conductance of `side`.
/// `adj` is an undirected adjacency list (multi-edges are allowed).
///
/// Time: `O(iters * (m + n) + n log n)`.
pub fn cheeger(adj: &[Vec<usize>]) -> (f64, Vec<usize>) {
    let n = adj.len();
    if n <= 1 {
        return (0.0, (0..n).collect());
    }
    let deg: Vec<usize> = adj.iter().map(Vec::len).collect();
    let total_vol: usize = deg.iter().sum();
    if total_vol == 0 {
        return (0.0, vec![0]);
    }
    // If disconnected, a whole component gives conductance 0.
    let mut vis = vec![false; n];
    let mut q = std::collections::VecDeque::new();
    vis[0] = true;
    q.push_back(0usize);
    while let Some(u) = q.pop_front() {
        for &v in &adj[u] {
            if !vis[v] {
                vis[v] = true;
                q.push_back(v);
            }
        }
    }
    if vis.iter().any(|&x| !x) {
        let mut side = Vec::new();
        for (u, &seen) in vis.iter().enumerate() {
            if seen {
                side.push(u);
            }
        }
        if !side.is_empty() && side.len() < n {
            return (0.0, side);
        }
    }

    // Power iteration on lazy normalized adjacency:
    // B = (I + D^{-1/2} A D^{-1/2}) / 2,
    // projected orthogonally to sqrt(deg), to approximate the Fiedler direction.
    let mut y = vec![0.0_f64; n];
    for u in 0..n {
        if deg[u] == 0 {
            continue;
        }
        let seed = (u as u64).wrapping_mul(1_103_515_245).wrapping_add(12_345) % 1_000_003;
        y[u] = (seed as f64) / 500_001.5 - 1.0;
    }
    let mut sqrt_deg = vec![0.0_f64; n];
    for u in 0..n {
        sqrt_deg[u] = (deg[u] as f64).sqrt();
    }
    let proj_and_norm = |v: &mut [f64]| {
        let mut dot_vp = 0.0;
        let mut dot_pp = 0.0;
        for u in 0..n {
            dot_vp += v[u] * sqrt_deg[u];
            dot_pp += sqrt_deg[u] * sqrt_deg[u];
        }
        if dot_pp > 0.0 {
            let alpha = dot_vp / dot_pp;
            for u in 0..n {
                v[u] -= alpha * sqrt_deg[u];
            }
        }
        let mut norm2 = 0.0;
        for &x in v.iter() {
            norm2 += x * x;
        }
        if norm2 > 0.0 {
            let inv = norm2.sqrt().recip();
            for x in v.iter_mut() {
                *x *= inv;
            }
            true
        } else {
            false
        }
    };
    if !proj_and_norm(&mut y) {
        for u in 0..n {
            if deg[u] > 0 {
                y[u] = if u % 2 == 0 { 1.0 } else { -1.0 };
            }
        }
        let _ = proj_and_norm(&mut y);
    }
    let iters = (40usize + ((n + 1) as f64).log2().ceil() as usize * 8).min(160);
    let mut ny = vec![0.0_f64; n];
    for _ in 0..iters {
        ny.fill(0.0);
        for u in 0..n {
            if deg[u] == 0 {
                continue;
            }
            let su = sqrt_deg[u];
            ny[u] += 0.5 * y[u];
            for &v in &adj[u] {
                if deg[v] == 0 {
                    continue;
                }
                ny[u] += 0.5 * y[v] / (su * sqrt_deg[v]);
            }
        }
        if !proj_and_norm(&mut ny) {
            break;
        }
        std::mem::swap(&mut y, &mut ny);
    }

    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| {
        let sa = if deg[a] == 0 {
            f64::NEG_INFINITY
        } else {
            y[a] / sqrt_deg[a]
        };
        let sb = if deg[b] == 0 {
            f64::NEG_INFINITY
        } else {
            y[b] / sqrt_deg[b]
        };
        sa.total_cmp(&sb)
    });

    let mut in_set = vec![false; n];
    let mut side = Vec::new();
    let mut best_side = Vec::new();
    let mut vol_s = 0usize;
    let mut cut_edges = 0usize;
    let mut best_phi = f64::INFINITY;
    for (i, &u) in order.iter().enumerate() {
        in_set[u] = true;
        side.push(u);
        vol_s += deg[u];
        for &v in &adj[u] {
            if in_set[v] {
                cut_edges = cut_edges.saturating_sub(1);
            } else {
                cut_edges += 1;
            }
        }
        if i + 1 == n {
            break;
        }
        let vol_t = total_vol - vol_s;
        let denom = vol_s.min(vol_t);
        if denom == 0 {
            continue;
        }
        let phi = cut_edges as f64 / denom as f64;
        if phi < best_phi {
            best_phi = phi;
            best_side.clear();
            best_side.extend(side.iter().copied());
        }
    }
    if best_phi.is_infinite() {
        return (0.0, vec![order[0]]);
    }
    (best_phi, best_side)
}

#[cfg(test)]
mod tests {
    use super::cheeger;

    fn undir(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
        let mut adj = vec![Vec::new(); n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        adj
    }

    fn conductance(adj: &[Vec<usize>], side: &[usize]) -> f64 {
        let n = adj.len();
        let mut in_s = vec![false; n];
        for &u in side {
            in_s[u] = true;
        }
        let mut cut = 0usize;
        let mut vol_s = 0usize;
        let mut vol_t = 0usize;
        for u in 0..n {
            if in_s[u] {
                vol_s += adj[u].len();
                for &v in &adj[u] {
                    if !in_s[v] {
                        cut += 1;
                    }
                }
            } else {
                vol_t += adj[u].len();
            }
        }
        let denom = vol_s.min(vol_t);
        if denom == 0 {
            0.0
        } else {
            cut as f64 / denom as f64
        }
    }

    #[test]
    fn cheeger_path_is_nontrivial() {
        let adj = undir(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]);
        let (phi, side) = cheeger(&adj);
        assert!(!side.is_empty() && side.len() < adj.len());
        assert!(phi <= 0.5, "unexpectedly weak cut on path: {phi}");
        let chk = conductance(&adj, &side);
        assert!((phi - chk).abs() < 1e-9);
    }

    #[test]
    fn cheeger_barbell_finds_sparse_bridge_cut() {
        // Two K4s connected by one bridge (3,4).
        let mut edges = Vec::new();
        for i in 0..4 {
            for j in i + 1..4 {
                edges.push((i, j));
            }
        }
        for i in 4..8 {
            for j in i + 1..8 {
                edges.push((i, j));
            }
        }
        edges.push((3, 4));
        let adj = undir(8, &edges);
        let (phi, side) = cheeger(&adj);
        assert!(!side.is_empty() && side.len() < 8);
        assert!(phi < 0.2, "expected low conductance for barbell, got {phi}");
        let chk = conductance(&adj, &side);
        assert!((phi - chk).abs() < 1e-9);
    }

    #[test]
    fn cheeger_disconnected_has_zero_conductance_cut() {
        let adj = undir(6, &[(0, 1), (1, 2), (3, 4)]);
        let (phi, side) = cheeger(&adj);
        assert!(!side.is_empty() && side.len() < 6);
        assert!(
            phi <= 1e-12,
            "disconnected graph should have zero-cut partition"
        );
        let chk = conductance(&adj, &side);
        assert!((phi - chk).abs() < 1e-9);
    }
}
