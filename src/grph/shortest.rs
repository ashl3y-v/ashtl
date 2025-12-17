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

// TODO: eppstein's algorithm

// https://codeforces.com/blog/entry/102085
/// O(m log m + k log k)
pub fn eppstein<T>(adj: &[Vec<(usize, T)>], s: usize, t: usize, k: usize) {}
