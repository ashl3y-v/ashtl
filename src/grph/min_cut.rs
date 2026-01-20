use std::{
    collections::{HashMap, VecDeque},
    f64::consts::SQRT_2,
};

use crate::ds::{dsu::DSU, sort::counting_sort_by_key};
use rand::prelude::*;

#[derive(Debug, Clone, Copy)]
struct KargerEdge {
    u: usize,
    v: usize,
    weight: usize,
}

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
    let mut weights: Vec<usize> = (0..m).collect();
    weights.shuffle(&mut rng);
    let mut edges = Vec::with_capacity(m);
    for (i, &(u, v, _)) in es.iter().enumerate() {
        edges.push(KargerEdge {
            u,
            v,
            weight: weights[i],
        });
    }
    counting_sort_by_key(&mut edges, m, |a| a.weight);
    let mut dsu = DSU::new(n);
    let mut mst_edges = Vec::with_capacity(n - 1);
    for e in edges {
        if dsu.union(e.u, e.v).1 {
            mst_edges.push(e);
        }
    }
    if mst_edges.is_empty() {
        return (n, es.to_vec());
    }
    let edges_to_keep_count = mst_edges.len().saturating_sub(t - 1);
    mst_edges.truncate(edges_to_keep_count);
    let mut forest_adj = vec![vec![]; n];
    for e in &mst_edges {
        forest_adj[e.u].push(e.v);
        forest_adj[e.v].push(e.u);
    }
    let mut component_ids = vec![usize::MAX; n];
    let mut next_comp_id = 0;
    let mut queue = VecDeque::new();
    for i in 0..n {
        if component_ids[i] == usize::MAX {
            component_ids[i] = next_comp_id;
            queue.push_back(i);
            while let Some(u) = queue.pop_front() {
                for &v in &forest_adj[u] {
                    if component_ids[v] == usize::MAX {
                        component_ids[v] = next_comp_id;
                        queue.push_back(v);
                    }
                }
            }
            next_comp_id += 1;
        }
    }
    let mut new_edges = Vec::new();
    for &(u, v, id) in es {
        let comp_u = component_ids[u];
        let comp_v = component_ids[v];
        if comp_u != comp_v {
            new_edges.push((comp_u, comp_v, id));
        }
    }
    (next_comp_id, new_edges)
}

/// O(n^2 log^3 n)
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
    let scale = 1500 * n;
    let repetitions = ((scale as f64).ln() / p_n).ceil() as usize;
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
