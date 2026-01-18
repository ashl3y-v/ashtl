use crate::ds::bit_vec::BitVec;
use crate::ds::score::MinScore;
use std::{collections::BinaryHeap, ops::Add};

/// O(n m)
pub fn bellman_ford<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> Result<(Vec<Option<T>>, Vec<usize>), (usize, Vec<Option<T>>, Vec<usize>)> {
    let n = adj.len();
    let (d, p) = bellman_ford_unchecked(v, adj);
    for i in 0..n {
        if let Some(d_i) = d[i] {
            for &(j, w) in &adj[i] {
                let dist = d_i + w;
                if d[j].is_none() || Some(dist) < d[j] {
                    return Err((i, d, p));
                }
            }
        }
    }
    Ok((d, p))
}

/// O(n m)
pub fn spfa<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> Result<(Vec<Option<T>>, Vec<usize>), (usize, Vec<Option<T>>, Vec<usize>)> {
    let n = adj.len();
    let mut p = vec![usize::MAX; n];
    let mut d = vec![None; n];
    d[v] = Some(T::default());
    let mut q = Vec::with_capacity(n);
    let mut in_q = BitVec::new(n, false);
    q.push(v);
    in_q.set(v, true);
    let mut visits = vec![0; n];
    while let Some(i) = q.pop() {
        in_q.set(i, false);
        if visits[i] >= n {
            return Err((i, d, p));
        }
        visits[i] += 1;
        if let Some(d_i) = d[i] {
            for &(j, w) in &adj[i] {
                let dist = d_i + w;
                if d[j].is_none() || Some(dist) < d[j] {
                    d[j] = Some(dist);
                    p[j] = i;
                    if !in_q[j] {
                        in_q.set(j, true);
                        q.push(j);
                    }
                }
            }
        }
    }
    Ok((d, p))
}

/// O(n)
pub fn recover_negative_cycle<T>(v: usize, d: &[T], p: &[usize]) -> Vec<usize> {
    let n = d.len();
    let mut path = Vec::new();
    let start = v;
    let mut node = start;
    let mut visited = BitVec::new(n, false);
    loop {
        let ancestor = if p[node] == usize::MAX { node } else { p[node] };
        if ancestor == start {
            path.push(ancestor);
            break;
        } else if visited[ancestor] {
            let pos = path.iter().position(|&p| p == ancestor).unwrap();
            path = path[pos..].to_vec();
            break;
        }
        path.push(ancestor);
        visited.set(ancestor, true);
        node = ancestor;
    }
    path.reverse();
    path
}

/// O(n m)
pub fn bellman_ford_unchecked<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    v: usize,
    adj: &[Vec<(usize, T)>],
) -> (Vec<Option<T>>, Vec<usize>) {
    let n = adj.len();
    let mut p = vec![usize::MAX; n];
    let mut d = vec![None; n];
    d[v] = Some(T::default());
    for _ in 0..n {
        let mut did_update = false;
        for i in 0..n {
            if let Some(d_i) = d[i] {
                for &(j, w) in &adj[i] {
                    let dist = d_i + w;
                    if d[j].is_none() || Some(dist) < d[j] {
                        d[j] = Some(dist);
                        p[j] = i;
                        did_update = true;
                    }
                }
            }
        }
        if !did_update {
            break;
        }
    }
    (d, p)
}

/// O((n + m) log n)
/// Works for any type T such that:
/// For source T::default() is correct initialization
/// sum(p) + v >= sum(p) if v adjacent to end of p
/// if p, q have same end and sum(p) >= sum(q), then sum(p) + v >= sum(q) + v for all v adjacent to end
/// https://codeforces.com/blog/entry/107810
pub fn dijkstra<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    u: usize,
    v: Option<usize>,
    adj: &[Vec<(usize, T)>],
) -> Vec<Option<T>> {
    let n = adj.len();
    let mut seen = BitVec::new(n, false);
    let mut scores = vec![None; n];
    let mut visit = BinaryHeap::new();
    scores[u] = Some(T::default());
    visit.push(MinScore(T::default(), u));
    while let Some(MinScore(s, i)) = visit.pop() {
        if seen[i] {
            continue;
        }
        if v == Some(i) {
            break;
        }
        for &(j, w) in &adj[i] {
            if seen[j] {
                continue;
            }
            let ns = s + w;
            if scores[j].is_none() || Some(ns) < scores[j] {
                scores[j] = Some(ns);
                visit.push(MinScore(ns, j));
            }
        }
        seen.set(i, true);
    }
    scores
}

/// O(n^3)
pub fn floyd_warshall(d: &mut [Vec<i64>], mut p: Option<&mut [Vec<usize>]>) {
    let n = d.len();
    for i in 0..n {
        d[i][i] = d[i][i].min(0);
    }
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                let (dist, overflow) = d[i][k].overflowing_add(d[k][j]);
                if !overflow && d[i][j] > dist {
                    d[i][j] = dist;
                    if let Some(ref mut p) = p {
                        p[i][j] = p[k][j];
                    }
                }
            }
        }
    }
    for k in 0..n {
        if d[k][k] < 0 {
            for i in 0..n {
                for j in 0..n {
                    if d[i][k] != i64::MAX && d[k][j] != i64::MAX {
                        d[i][j] = i64::MIN;
                    }
                }
            }
        }
    }
}

/// O(n)
pub fn recover_path(u: usize, v: usize, p: &[Vec<usize>]) -> Vec<usize> {
    if u == v {
        return vec![u];
    }
    if p[u][v] == usize::MAX {
        return Vec::new();
    }
    let mut path = Vec::new();
    let mut cur = v;
    path.push(cur);
    while cur != u {
        cur = p[u][cur];
        path.push(cur);
    }
    path.reverse();
    path
}

/// O(n^2 log n + n m)
pub fn johnson(adj: &[Vec<(usize, i64)>]) -> Option<Vec<Vec<i64>>> {
    let n = adj.len();
    if n == 0 {
        return Some(vec![]);
    }
    let mut h = vec![0; n];
    for _ in 0..n {
        let mut updated = false;
        for u in 0..n {
            if h[u] != i64::MAX {
                for &(v, w) in &adj[u] {
                    let nd = h[u].saturating_add(w);
                    if nd < h[v] {
                        h[v] = nd;
                        updated = true;
                    }
                }
            }
        }
        if !updated {
            break;
        }
    }
    for u in 0..n {
        for &(v, w) in &adj[u] {
            if h[u] != i64::MAX && h[u].saturating_add(w) < h[v] {
                return None;
            }
        }
    }
    let mut dist = vec![vec![i64::MAX; n]; n];
    for src in 0..n {
        let mut d = vec![i64::MAX; n];
        let mut seen = BitVec::new(n, false);
        let mut pq = BinaryHeap::new();
        d[src] = 0;
        pq.push(MinScore(0, src));
        while let Some(MinScore(du, u)) = pq.pop() {
            if seen[u] {
                continue;
            }
            seen.set(u, true);
            for &(v, w) in &adj[u] {
                if seen[v] {
                    continue;
                }
                let w_reweighted = w + h[u] - h[v];
                let dv = du + w_reweighted;
                if dv < d[v] {
                    d[v] = dv;
                    pq.push(MinScore(dv, v));
                }
            }
        }
        for v in 0..n {
            if d[v] != i64::MAX {
                dist[src][v] = d[v] - h[src] + h[v];
            }
        }
    }
    Some(dist)
}

/// O((m + n) log n + k log k)
pub fn eppstein(adj: &[Vec<(usize, i64)>], s: usize, t: usize, k: usize) -> Vec<i64> {
    if k == 0 {
        return vec![];
    }
    let n = adj.len();
    let mut radj: Vec<Vec<(usize, i64)>> = vec![vec![]; n];
    for u in 0..n {
        for &(v, w) in &adj[u] {
            radj[v].push((u, w));
        }
    }
    let mut dist = vec![i64::MAX; n];
    let mut tree_edge: Vec<Option<(usize, i64)>> = vec![None; n];
    dist[t] = 0;
    let mut pq = BinaryHeap::new();
    pq.push(MinScore(0, t));
    while let Some(MinScore(d, v)) = pq.pop() {
        if d != dist[v] {
            continue;
        }
        for &(u, w) in &radj[v] {
            let nd = d + w;
            if nd < dist[u] {
                dist[u] = nd;
                tree_edge[u] = Some((v, w));
                pq.push(MinScore(nd, u));
            }
        }
    }
    if dist[s] == i64::MAX {
        return vec![];
    }
    let mut nodes: Vec<(i64, usize, usize, usize)> = vec![(0, 0, 0, 0)];
    fn meld(n: &mut Vec<(i64, usize, usize, usize)>, a: usize, b: usize) -> usize {
        if a == 0 {
            return b;
        } else if b == 0 {
            return a;
        }
        let (mut a, mut b) = (a, b);
        if n[a].0 > n[b].0 {
            std::mem::swap(&mut a, &mut b);
        }
        let (val, dest, left, right) = n[a];
        let new_right = meld(n, right, b);
        n.push((val, dest, new_right, left));
        n.len() - 1
    }
    fn insert(n: &mut Vec<(i64, usize, usize, usize)>, r: usize, val: i64, dest: usize) -> usize {
        n.push((val, dest, 0, 0));
        meld(n, r, n.len() - 1)
    }
    let mut heap_root = vec![0; n];
    let mut order: Vec<usize> = (0..n).filter(|&u| dist[u] < i64::MAX).collect();
    order.sort_by_key(|&u| dist[u]);
    for u in order {
        let mut root = if let Some((next, _)) = tree_edge[u] {
            heap_root[next]
        } else {
            0
        };
        for &(v, w) in &adj[u] {
            if dist[v] == i64::MAX {
                continue;
            }
            if tree_edge[u] == Some((v, w)) {
                continue;
            }
            let delta = w + dist[v] - dist[u];
            root = insert(&mut nodes, root, delta, v);
        }
        heap_root[u] = root;
    }
    let mut res = Vec::with_capacity(k);
    let mut epq: BinaryHeap<MinScore<i64, usize>> = BinaryHeap::new();
    nodes.push((dist[s], s, 0, 0));
    let init = nodes.len() - 1;
    epq.push(MinScore(dist[s], init));
    while let Some(MinScore(len, idx)) = epq.pop() {
        if res.len() >= k {
            break;
        }
        res.push(len);
        let (val, dest, left, right) = nodes[idx];
        if left != 0 {
            epq.push(MinScore(len - val + nodes[left].0, left));
        }
        if right != 0 {
            epq.push(MinScore(len - val + nodes[right].0, right));
        }
        let h = heap_root[dest];
        if h != 0 {
            epq.push(MinScore(len + nodes[h].0, h));
        }
    }
    res
}
