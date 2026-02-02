// TODO: rerooting
// https://codeforces.com/blog/entry/124286
// https://maspypy.github.io/library/graph/tree_dp/rerooting_dp.hpp
// https://maspypy.github.io/library/graph/tree_dp/rerooting_dp_2.hpp
// https://blog.niuez.net/cp-cpp-library/tech/rerooting.html

use std::collections::VecDeque;

use crate::ds::bit_vec::BitVec;

pub fn reroot<T, Merge, UpRoot, TakeVertex>(
    n: usize,
    edges: &[(usize, usize)],
    id: T,
    mut merge: Merge,
    mut up_root: UpRoot,
    mut take_vertex: TakeVertex,
) -> Vec<T>
where
    T: Clone,
    Merge: FnMut(&T, &T) -> T,
    UpRoot: FnMut(&T, usize) -> T,
    TakeVertex: FnMut(&T, usize) -> T,
{
    if n == 0 {
        return vec![];
    } else if n == 1 {
        return vec![take_vertex(&id, 0)];
    }
    let mut adj = vec![vec![]; n];
    for (i, &(u, v)) in edges.iter().enumerate() {
        adj[u].push((2 * i, v));
        adj[v].push((2 * i + 1, u));
    }
    let mut order = Vec::with_capacity(n);
    let mut par_e = vec![usize::MAX; n];
    let mut q = VecDeque::new();
    let mut visited = BitVec::new(n, false);
    q.push_back(0);
    visited.set(0, true);
    while let Some(u) = q.pop_front() {
        order.push(u);
        let mut par_i = usize::MAX;
        for (i, &(e, v)) in adj[u].iter().enumerate() {
            if !visited[v] {
                visited.set(v, true);
                par_e[v] = e;
                q.push_back(v);
            } else {
                par_i = i;
            }
        }
        if par_i != usize::MAX {
            adj[u].swap_remove(par_i);
        }
    }
    let mut dp = vec![id.clone(); n];
    for &u in order.iter().rev() {
        let mut acc = id.clone();
        for &(e, v) in &adj[u] {
            acc = merge(&acc, &up_root(&dp[v], e));
        }
        dp[u] = take_vertex(&acc, u);
    }
    let mut rev_dp = vec![id.clone(); n];
    for &u in &order {
        let nbrs = &adj[u];
        let deg = nbrs.len();
        let mut suff = Vec::with_capacity(deg + 1);
        let mut pref = Vec::with_capacity(deg + 1);
        pref.push(if par_e[u] != usize::MAX {
            up_root(&rev_dp[u], par_e[u])
        } else {
            id.clone()
        });
        for &(e, v) in nbrs {
            let val = up_root(&dp[v], e);
            pref.push(val.clone());
            suff.push(val);
        }
        suff.push(id.clone());
        for i in 0..deg {
            pref[i + 1] = merge(&pref[i], &pref[i + 1]);
        }
        for i in (0..deg).rev() {
            suff[i] = merge(&suff[i], &suff[i + 1]);
        }
        for (i, &(_, v)) in nbrs.iter().enumerate() {
            rev_dp[v] = take_vertex(&merge(&pref[i], &suff[i + 1]), u);
        }
    }
    let mut sln = Vec::with_capacity(n);
    for u in 0..n {
        let mut acc = if par_e[u] == usize::MAX {
            id.clone()
        } else {
            up_root(&rev_dp[u], par_e[u])
        };
        for &(e, v) in &adj[u] {
            acc = merge(&acc, &up_root(&dp[v], e));
        }
        sln.push(take_vertex(&acc, u));
    }
    sln
}
