use std::collections::VecDeque;

/// O(m + n)
pub fn ldd(adj: &[Vec<usize>], beta: f64) -> Vec<usize> {
    let n = adj.len();
    let mut cluster = vec![usize::MAX; n];
    if n == 0 {
        return cluster;
    }
    let beta = beta.max(0.0);
    let mut unseen = vec![true; n];
    let mut in_ball = vec![false; n];
    let mut in_next_layer = vec![false; n];
    let mut q = VecDeque::new();
    let mut cluster_id = 0;
    for start in 0..n {
        if !unseen[start] {
            continue;
        }
        let mut members = Vec::new();
        let mut internal_edges = 0;
        let mut boundary_edges = 0usize;
        in_ball[start] = true;
        members.push(start);
        q.push_back(start);
        for &v in &adj[start] {
            if unseen[v] && v != start {
                boundary_edges += 1;
            }
        }
        while (boundary_edges as f64) > beta * (internal_edges as f64) {
            let layer_sz = q.len();
            if layer_sz == 0 {
                break;
            }
            let mut next_layer = Vec::new();
            for _ in 0..layer_sz {
                let u = q.pop_front().unwrap();
                for &v in &adj[u] {
                    if unseen[v] && !in_ball[v] {
                        in_ball[v] = true;
                        members.push(v);
                        next_layer.push(v);
                    }
                }
            }
            if next_layer.is_empty() {
                break;
            }
            for &u in &next_layer {
                in_next_layer[u] = true;
            }
            let mut same_layer_twice = 0;
            for &u in &next_layer {
                for &v in &adj[u] {
                    if !unseen[v] || v == u {
                        continue;
                    }
                    if in_next_layer[v] {
                        same_layer_twice += 1;
                    } else if in_ball[v] {
                        boundary_edges = boundary_edges.saturating_sub(1);
                        internal_edges += 1;
                    } else {
                        boundary_edges += 1;
                    }
                }
            }
            internal_edges += same_layer_twice / 2;
            for &u in &next_layer {
                in_next_layer[u] = false;
            }
            q.extend(next_layer);
        }
        for &u in &members {
            in_ball[u] = false;
            unseen[u] = false;
            cluster[u] = cluster_id;
        }
        cluster_id += 1;
        q.clear();
    }
    cluster
}
