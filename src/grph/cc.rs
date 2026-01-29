use crate::{
    ds::{bit_vec::BitVec, dsu::DSU},
    grph::format::edges_to_csr_undir,
};
use std::collections::VecDeque;

pub struct SccResult {
    pub comp_cnt: usize,
    pub comp_id: Vec<usize>,
    pub comp_size: Vec<usize>,
    pub comp_start: Vec<usize>,
    pub comp_list: Vec<usize>,
}

pub fn scc(n: usize, g: &[usize], d: &[usize]) -> SccResult {
    let mut dfn = vec![0; n];
    let mut low = vec![0; n];
    let mut timer = 0;
    let mut stk = Vec::with_capacity(n);
    let mut in_stk = BitVec::new(n, false);
    let mut comp_id = vec![0; n];
    let mut comp_list = vec![0; n];
    let mut comp_size = vec![0; n];
    let mut comp_start = vec![0; n];
    let mut comp_cnt = 0;
    let mut write_ptr = n;
    struct Context<'a> {
        g: &'a [usize],
        d: &'a [usize],
        dfn: &'a mut [usize],
        low: &'a mut [usize],
        timer: &'a mut usize,
        stk: &'a mut Vec<usize>,
        in_stk: &'a mut BitVec,
        comp_id: &'a mut [usize],
        comp_list: &'a mut [usize],
        comp_size: &'a mut [usize],
        comp_start: &'a mut [usize],
        comp_cnt: &'a mut usize,
        write_ptr: &'a mut usize,
    }
    fn calc(u: usize, ctx: &mut Context) {
        *ctx.timer += 1;
        ctx.dfn[u] = *ctx.timer;
        ctx.low[u] = *ctx.timer;
        ctx.stk.push(u);
        ctx.in_stk.set(u, true);
        for &v in &ctx.g[ctx.d[u]..ctx.d[u + 1]] {
            if ctx.dfn[v] == 0 {
                calc(v, ctx);
                if ctx.low[v] < ctx.low[u] {
                    ctx.low[u] = ctx.low[v];
                }
            } else if ctx.in_stk[v] && ctx.dfn[v] < ctx.low[u] {
                ctx.low[u] = ctx.dfn[v];
            }
        }
        if ctx.low[u] == ctx.dfn[u] {
            let mut sz = 0;
            loop {
                let v = ctx.stk.pop().unwrap();
                ctx.in_stk.set(v, false);
                ctx.comp_id[v] = *ctx.comp_cnt;
                *ctx.write_ptr -= 1;
                ctx.comp_list[*ctx.write_ptr] = v;
                sz += 1;
                if v == u {
                    break;
                }
            }
            ctx.comp_size[*ctx.comp_cnt] = sz;
            ctx.comp_start[*ctx.comp_cnt] = *ctx.write_ptr;
            *ctx.comp_cnt += 1;
        }
    }
    let mut ctx = Context {
        g,
        d,
        dfn: &mut dfn,
        low: &mut low,
        timer: &mut timer,
        stk: &mut stk,
        in_stk: &mut in_stk,
        comp_id: &mut comp_id,
        comp_list: &mut comp_list,
        comp_size: &mut comp_size,
        comp_start: &mut comp_start,
        comp_cnt: &mut comp_cnt,
        write_ptr: &mut write_ptr,
    };
    for i in 0..n {
        if ctx.dfn[i] == 0 {
            calc(i, &mut ctx);
        }
    }
    SccResult {
        comp_cnt,
        comp_id,
        comp_size,
        comp_start,
        comp_list,
    }
}

/// O(m log m + n)
pub fn scc_incremental(n: usize, mut es: Vec<(usize, usize)>) -> (Vec<usize>, Vec<usize>) {
    fn rec(
        n: usize,
        x: usize,
        idx: Vec<usize>,
        es: &mut [(usize, usize)],
        sep: &mut Vec<usize>,
        merge: &mut Vec<usize>,
    ) {
        let m = idx.len();
        if x == m {
            return;
        } else if x + 1 == m {
            let mut dsu = DSU::new(n);
            for &e in &idx {
                let (u, v) = es[e];
                if !dsu.union(u, v).1 {
                    continue;
                }
                sep[idx[x] + 1] += 1;
                merge.push(e);
            }
            return;
        }
        let mut mp = vec![usize::MAX; n];
        let mut nn = 0;
        for &e_idx in &idx {
            let (u, v) = es[e_idx];
            if mp[u] == usize::MAX {
                mp[u] = nn;
                nn += 1;
            }
            if mp[v] == usize::MAX {
                mp[v] = nn;
                nn += 1;
            }
        }
        for &e in &idx {
            let (u, v) = es[e];
            es[e] = (mp[u], mp[v]);
        }
        let mid = x.midpoint(m);
        let mut l_es = Vec::with_capacity(mid);
        for i in 0..mid {
            l_es.push(es[idx[i]]);
        }
        let (g, d) = edges_to_csr_undir(nn, &l_es);
        let scc_res = scc(nn, &g, &d);
        let mut idxl = Vec::new();
        let mut idxr = Vec::new();
        for i in 0..x {
            let (u, v) = es[idx[i]];
            if scc_res.comp_id[u] == scc_res.comp_id[v] {
                idxl.push(idx[i]);
            } else {
                idxr.push(idx[i]);
            }
        }
        let xl = idxl.len();
        for i in x..mid {
            let (u, v) = es[idx[i]];
            if scc_res.comp_id[u] == scc_res.comp_id[v] {
                idxl.push(idx[i]);
            } else {
                idxr.push(idx[i]);
            }
        }
        let xr = idxr.len();
        for i in mid..m {
            let (u, v) = es[idx[i]];
            if scc_res.comp_id[u] != scc_res.comp_id[v] {
                idxr.push(idx[i]);
            }
        }
        rec(nn, xl, idxl, es, sep, merge);
        for &e in &idxr {
            let (u, v) = es[e];
            es[e] = (scc_res.comp_id[u], scc_res.comp_id[v]);
        }
        rec(scc_res.comp_cnt, xr, idxr, es, sep, merge);
    }
    let m = es.len();
    let mut sep = vec![0; m + 1];
    let mut merge = Vec::new();
    let mut idx = Vec::new();
    let (g, d) = edges_to_csr_undir(n, &es);
    let scc_res = scc(n, &g, &d);
    for i in 0..m {
        let (u, v) = es[i];
        if scc_res.comp_id[u] == scc_res.comp_id[v] {
            idx.push(i);
        }
    }
    rec(n, 0, idx, &mut es, &mut sep, &mut merge);
    for i in 0..m {
        sep[i + 1] += sep[i];
    }
    (merge, sep)
}

// TODO: improve two cc
// https://judge.yosupo.jp/problem/biconnected_components
// https://judge.yosupo.jp/submission/287412

pub fn cc2<F>(n: usize, adj: &[Vec<usize>], mut f: F)
where
    F: FnMut(&[(usize, usize)]),
{
    let mut tin = vec![0; n];
    let mut low = vec![0; n];
    let mut visited = vec![false; n];
    let mut timer = 0;
    let mut edge_stack = Vec::new();
    fn dfs<F>(
        v: usize,
        parent: Option<usize>,
        adj: &[Vec<usize>],
        visited: &mut [bool],
        tin: &mut [usize],
        low: &mut [usize],
        timer: &mut usize,
        edge_stack: &mut Vec<(usize, usize)>,
        f: &mut F,
    ) where
        F: FnMut(&[(usize, usize)]),
    {
        visited[v] = true;
        tin[v] = *timer;
        low[v] = *timer;
        *timer += 1;
        for &to in &adj[v] {
            if Some(to) == parent {
                continue;
            }
            if visited[to] {
                low[v] = low[v].min(tin[to]);
                if tin[to] < tin[v] {
                    edge_stack.push((v, to));
                }
            } else {
                edge_stack.push((v, to));
                dfs(to, Some(v), adj, visited, tin, low, timer, edge_stack, f);
                low[v] = low[v].min(low[to]);
                if !parent.is_none() && low[to] >= tin[v] {
                    let mut component = Vec::new();
                    while let Some(e) = edge_stack.pop() {
                        component.push(e);
                        if e == (v, to) {
                            break;
                        }
                    }
                    f(&component);
                }
            }
        }
    }
    for v in 0..n {
        if !visited[v] {
            dfs(
                v,
                None,
                adj,
                &mut visited,
                &mut tin,
                &mut low,
                &mut timer,
                &mut edge_stack,
                &mut f,
            );
            // any leftover edges form one last block
            if !edge_stack.is_empty() {
                f(&edge_stack);
                edge_stack.clear();
            }
        }
    }
}

pub fn cut_vertices<F>(n: usize, adj: &[Vec<usize>], mut is_cut: F)
where
    F: FnMut(usize),
{
    let mut visited = vec![false; n];
    let mut tin = vec![0; n];
    let mut low = vec![0; n];
    let mut timer = 0;

    fn dfs<F>(
        v: usize,
        parent: Option<usize>,
        adj: &[Vec<usize>],
        visited: &mut [bool],
        tin: &mut [usize],
        low: &mut [usize],
        timer: &mut usize,
        is_cut: &mut F,
    ) where
        F: FnMut(usize),
    {
        visited[v] = true;
        tin[v] = *timer;
        low[v] = *timer;
        *timer += 1;
        let mut children = 0;
        for &to in &adj[v] {
            if Some(to) == parent {
                continue;
            }
            if visited[to] {
                low[v] = low[v].min(tin[to]);
            } else {
                children += 1;
                dfs(to, Some(v), adj, visited, tin, low, timer, is_cut);
                low[v] = low[v].min(low[to]);
                if parent.is_some() && low[to] >= tin[v] {
                    is_cut(v);
                }
            }
        }
        if parent.is_none() && children > 1 {
            is_cut(v);
        }
    }
    for v in 0..n {
        if !visited[v] {
            dfs(
                v,
                None,
                adj,
                &mut visited,
                &mut tin,
                &mut low,
                &mut timer,
                &mut is_cut,
            );
        }
    }
}

/// O(n^2)
pub fn comp_cc(adj: &[Vec<usize>], mut f: impl FnMut(Vec<usize>)) {
    let n = adj.len();
    let mut visited = BitVec::new(n, false);
    let mut temp = BitVec::new(n, false);
    let mut next_unvisited = 0;
    let mut remaining: Vec<usize> = Vec::with_capacity(n);
    remaining.extend(0..n);
    while next_unvisited < n {
        let mut component = Vec::with_capacity(remaining.len());
        component.push(next_unvisited);
        visited.set(next_unvisited, true);
        let mut queue = VecDeque::with_capacity(remaining.len());
        queue.push_back(next_unvisited);
        while let Some(curr) = queue.pop_front() {
            for &edge in &adj[curr] {
                temp.set(edge, true);
            }
            let mut i = 0;
            while i < remaining.len() {
                let node = remaining[i];
                if visited[node] {
                    remaining.swap_remove(i);
                } else if !temp[node] {
                    visited.set(node, true);
                    component.push(node);
                    queue.push_back(node);
                    remaining.swap_remove(i);
                } else {
                    i += 1;
                }
            }
            for &edge in &adj[curr] {
                temp.set(edge, false);
            }
        }
        f(component);
        while next_unvisited < n && visited[next_unvisited] {
            next_unvisited += 1;
        }
    }
}

// TODO: two ecc
// https://judge.yosupo.jp/submission/106412
// https://maspypy.github.io/library/graph/two_edge_component.hpp
pub fn ecc2() {}

// TODO: three ecc
// https://judge.yosupo.jp/submission/248134
// https://judge.yosupo.jp/problem/three_edge_connected_components
pub fn ecc3() {}

// TODO: s-t numbering
// https://judge.yosupo.jp/problem/st_numbering
pub fn st_numbering() {}
