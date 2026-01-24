use crate::ds::bit_vec::BitVec;
use crate::{
    alg::{fps::FPS, lattice},
    ds::set::UbIntSet,
};
use std::collections::{BinaryHeap, HashMap};

pub fn chromatic_number(adj: &[Vec<usize>]) -> usize {
    let n = adj.len();
    let mut ans = n + 1;
    let mut colors = vec![0; n];
    fn dfs(graph: &[Vec<usize>], colors: &mut [usize], c: usize, cnt: usize, ans: &mut usize) {
        if c >= *ans {
            return;
        } else if cnt == 0 {
            *ans = c;
            return;
        }
        let mut u = 0;
        let mut max_neighbors = -1i32;
        let mut neighbor_mask = 0u64;
        for i in 0..graph.len() {
            if colors[i] == 0 {
                let mut mask = 0u64;
                for &j in &graph[i] {
                    if colors[j] > 0 {
                        mask |= 1u64 << colors[j];
                    }
                }
                let count = mask.count_ones() as i32;
                if count > max_neighbors {
                    (max_neighbors, u, neighbor_mask) = (count, i, mask);
                }
            }
        }
        for color in 1..=c + 1 {
            if (neighbor_mask >> color) & 1 == 0 {
                colors[u] = color;
                dfs(graph, colors, c.max(color), cnt - 1, ans);
            }
        }
        colors[u] = 0;
    }
    dfs(adj, &mut colors, 0, n, &mut ans);
    ans
}

/// DSatur greedy coloring
/// O((n + m) log n)
pub fn dsatur(adj: &[Vec<usize>]) -> (HashMap<usize, usize>, usize) {
    let n = adj.len();
    let mut deg = vec![0; n];
    let mut q = BinaryHeap::with_capacity(n);
    let mut cols = HashMap::with_capacity(n);
    let mut adj_cols = vec![UbIntSet::new(n); n];
    let mut seen = BitVec::new(n, false);
    let mut max_col = 0;
    for u in 0..n {
        let d = adj[u].len();
        q.push(((d, 0), u));
        deg[u] = d;
    }
    while let Some((_, u)) = q.pop() {
        if seen[u] {
            continue;
        }
        seen.set(u, true);
        let adj_col = &adj_cols[u];
        let col = adj_col.exsucc(0);
        cols.insert(u, col);
        max_col = max_col.max(col);
        for &v in &adj[u] {
            if let Some(adj_col) = adj_cols.get_mut(v) {
                adj_col.insert(col);
                q.push(((adj_col.len(), deg[v]), v));
            }
        }
    }
    (cols, max_col + 1)
}

/// O(2^n n)
pub fn k_col(k: usize, adj: &[usize]) -> bool {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    for i in 0..n {
        for j in 0..i {
            if adj[i] & (1 << j) != 0 {
                f[1 << i | 1 << j] = 1;
            }
        }
    }
    lattice::subset(&mut f);
    for i in 0..f.len() {
        if f[i] != 0 {
            f[i] = 0;
        } else {
            f[i] = 1;
        }
    }
    lattice::xor(&mut f);
    f.iter_mut().for_each(|i| *i = i.wrapping_pow(k as u32));
    let mut t = 0;
    for i in 0..1_usize << n {
        if i.count_ones() & 1 == 0 {
            t += f[i]
        } else {
            t -= f[i]
        };
    }
    t != 0
}

/// O(2^n n)
pub fn chi(adj: &[usize]) -> usize {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    for i in 0..n {
        for j in 0..i {
            if adj[i] & (1 << j) != 0 {
                f[1 << i | 1 << j] = 1;
            }
        }
    }
    lattice::subset(&mut f);
    for i in 0..f.len() {
        if f[i] != 0 {
            f[i] = 0;
        } else {
            f[i] = 1;
        }
    }
    let mut g = f.clone();
    lattice::xor(&mut g);
    let mut f = g.clone();
    for i in 1..=n {
        let mut t = 0;
        for i in 0..1_usize << n {
            if i.count_ones() & 1 == 0 {
                t += f[i]
            } else {
                t -= f[i]
            };
        }
        if t != 0 {
            return i;
        }
        f.iter_mut()
            .zip(&g)
            .for_each(|(i, &j)| *i = i.wrapping_mul(j));
    }
    usize::MAX
}

/// O(2^n n)
pub fn clique_cover_number(adj: &[usize]) -> usize {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    for i in 0..n {
        for j in 0..i {
            if adj[i] & (1 << j) == 0 {
                f[1 << i | 1 << j] = 1;
            }
        }
    }
    lattice::subset(&mut f);
    for i in 0..f.len() {
        if f[i] != 0 {
            f[i] = 0;
        } else {
            f[i] = 1;
        }
    }
    let mut g = f.clone();
    lattice::xor(&mut g);
    let mut f = g.clone();
    for i in 1..=n {
        let mut t = 0;
        for i in 0..1_usize << n {
            if i.count_ones() & 1 == 0 {
                t += f[i]
            } else {
                t -= f[i]
            };
        }
        if t != 0 {
            return i;
        }
        f.iter_mut()
            .zip(&g)
            .for_each(|(i, &j)| *i = i.wrapping_mul(j));
    }
    usize::MAX
}

/// O(2^n n^2 + m log m)
pub fn chromatic_poly<const M: u64>(adj: &[usize], m: usize) -> FPS<M> {
    let n = adj.len();
    let mut f = vec![0_i64; 1 << n];
    for i in 0..n {
        for j in 0..i {
            if adj[i] & (1 << j) != 0 {
                f[1 << i | 1 << j] = 1;
            }
        }
    }
    lattice::subset(&mut f);
    for i in 0..f.len() {
        if f[i] != 0 {
            f[i] = 0;
        } else {
            f[i] = 1;
        }
    }
    let mut w = vec![0; 1 << n];
    w[(1 << n) - 1] = 1;
    FPS::new(f).sps_pow_proj(FPS::<M>::new(w), m)
}

// TODO: edge coloring
// https://judge.yosupo.jp/submission/97319
// https://judge.yosupo.jp/submission/228343
// https://codeforces.com/blog/entry/75431
// https://github.com/kth-competitive-programming/kactl/blob/eab6492ce9c8549832484f47276739ff120477b3/content/graph/EdgeColoring.h#L16
// https://maspypy.github.io/library/graph/bipartite_edge_coloring.hpp

fn split_euler(n: usize, edges: &[(usize, usize)]) -> Vec<usize> {
    if edges.is_empty() {
        return Vec::new();
    }
    let mut gph: Vec<usize> = vec![usize::MAX; n];
    let m = edges.len();
    let mut nxt = vec![0; m * 2];
    let mut vis = BitVec::new(m * 2, false);
    for (i, &(u, v)) in edges.iter().enumerate() {
        let u_idx = u;
        let v_idx = v + n / 2;
        let edge_ref_u = 2 * i;
        if gph[u_idx] != usize::MAX {
            let prev = gph[u_idx];
            nxt[prev] = edge_ref_u ^ 1;
            nxt[edge_ref_u] = prev ^ 1;
            gph[u_idx] = usize::MAX;
        } else {
            gph[u_idx] = edge_ref_u;
        }
        let edge_ref_v = 2 * i + 1;
        if gph[v_idx] != usize::MAX {
            let prev = gph[v_idx];
            nxt[prev] = edge_ref_v ^ 1;
            nxt[edge_ref_v] = prev ^ 1;
            gph[v_idx] = usize::MAX;
        } else {
            gph[v_idx] = edge_ref_v;
        }
    }
    let mut ans = Vec::new();
    for i in 0..(m * 2) {
        if !vis[i] {
            let mut j = i;
            while !vis[j] {
                ans.push(j >> 1);
                vis.set(j, true);
                vis.set(j ^ 1, true);
                j = nxt[j];
            }
        }
    }
    ans
}

fn edge_coloring_power_of_two(n: usize, k: usize, edges: Vec<(usize, usize)>) -> Vec<usize> {
    let m = edges.len();
    let mut matchings: Vec<Vec<(usize, usize)>> = vec![Vec::new(); 2 * k - 1];
    let mut indices: Vec<Vec<usize>> = vec![Vec::new(); 2 * k - 1];
    matchings[0] = edges;
    indices[0] = (0..m).collect();
    for i in 0..(k - 1) {
        let decomp = split_euler(2 * n, &matchings[i]);
        for (j, &edge_idx) in decomp.iter().enumerate() {
            let target_idx = 2 * i + 1 + (j % 2);
            let a = matchings[i][edge_idx];
            matchings[target_idx].push(a);
            let b = indices[i][edge_idx];
            indices[target_idx].push(b);
        }
    }
    let mut ans = vec![0; m];
    for i in 0..k {
        for &original_idx in &indices[i + k - 1] {
            ans[original_idx] = i;
        }
    }
    ans
}

fn edge_coloring_regular(n: usize, k: usize, edges: Vec<(usize, usize)>) -> Vec<usize> {
    #[derive(Clone, Copy)]
    struct DncItem {
        u: usize,
        v: usize,
        k: usize,
        idx: isize,
    }
    assert!(k > 0);
    if k.is_power_of_two() {
        return edge_coloring_power_of_two(n, k, edges);
    }
    if k % 2 == 0 {
        let decomp = split_euler(2 * n, &edges);
        let mut sub: [Vec<(usize, usize)>; 2] = [Vec::new(), Vec::new()];
        for (i, &edge_idx) in decomp.iter().enumerate() {
            sub[i % 2].push(edges[edge_idx]);
        }
        let rec0 = edge_coloring_regular(n, k / 2, sub[0].clone());
        let mut phi = 1;
        while phi < k / 2 {
            phi *= 2;
        }
        let mut ans = vec![0; edges.len()];
        let mut ptr = sub[1].len();
        for i in 0..(decomp.len() / 2) {
            let original_idx = decomp[2 * i];
            let color = rec0[i];
            ans[original_idx] = color;
            if color >= k - phi {
                sub[1].push(edges[original_idx]);
            }
        }
        let rec1 = edge_coloring_power_of_two(n, phi, sub[1].clone());
        for i in 0..decomp.len() {
            let original_idx = decomp[i];
            if i % 2 == 0 {
                if ans[original_idx] >= k - phi {
                    ans[original_idx] = rec1[ptr] + k - phi;
                    ptr += 1;
                }
            } else {
                ans[original_idx] = rec1[i / 2] + k - phi;
            }
        }
        return ans;
    }
    let mut t = 0;
    while (1 << t) < k * n {
        t += 1;
    }
    let mut todnc: Vec<DncItem> = Vec::new();
    let alph = (1 << t) / k;
    let beta = (1 << t) - k * alph;
    for (i, &(u, v)) in edges.iter().enumerate() {
        todnc.push(DncItem {
            u,
            v: v + n,
            k: alph,
            idx: i as isize,
        });
    }
    if beta > 0 {
        for i in 0..n {
            todnc.push(DncItem {
                u: i,
                v: i + n,
                k: beta,
                idx: -1,
            });
        }
    }
    for _ in 0..t {
        let mut toeuler: Vec<(usize, usize)> = Vec::new();
        for item in &todnc {
            if item.k % 2 != 0 {
                toeuler.push((item.u, item.v - n));
            }
        }
        let pth = split_euler(2 * n, &toeuler);
        let mut parity = vec![0; toeuler.len()];
        for i in (1..pth.len()).step_by(2) {
            parity[pth[i]] = 1;
        }
        let mut sub0: Vec<DncItem> = Vec::new();
        let mut sub1: Vec<DncItem> = Vec::new();
        let mut ptr = 0;
        let mut bal = 0;
        for item in &todnc {
            let mut l = item.k / 2;
            let mut r = item.k / 2;
            if item.k % 2 != 0 {
                if parity[ptr] == 1 {
                    r += 1;
                } else {
                    l += 1;
                }
                ptr += 1;
            }
            if item.idx == -1 {
                bal += l as isize - r as isize;
            }
            if l > 0 {
                sub0.push(DncItem {
                    u: item.u,
                    v: item.v,
                    k: l,
                    idx: item.idx,
                });
            }
            if r > 0 {
                sub1.push(DncItem {
                    u: item.u,
                    v: item.v,
                    k: r,
                    idx: item.idx,
                });
            }
        }
        if bal >= 0 {
            todnc = sub1;
        } else {
            todnc = sub0;
        }
    }
    let mut ans = vec![-1_i32; edges.len()];
    for item in &todnc {
        assert!(item.k == 1 && item.idx != -1);
        ans[item.idx as usize] = (k - 1) as i32;
    }
    let mut sub_edges = Vec::new();
    for i in 0..edges.len() {
        if ans[i] == -1 {
            sub_edges.push(edges[i]);
        }
    }
    let mut piv = 0;
    let sol = edge_coloring_regular(n, k - 1, sub_edges);
    let mut final_ans = vec![0; edges.len()];
    for i in 0..edges.len() {
        if ans[i] == -1 {
            final_ans[i] = sol[piv];
            piv += 1;
        } else {
            final_ans[i] = ans[i] as usize;
        }
    }
    final_ans
}

pub fn edge_coloring(mut l: usize, mut r: usize, mut edges: Vec<(usize, usize)>) -> Vec<usize> {
    if edges.is_empty() {
        return Vec::new();
    }
    let mut d = [vec![0; l], vec![0; r]];
    for &(u, v) in &edges {
        d[0][u] += 1;
        d[1][v] += 1;
    }
    let k_max = (*d[0].iter().max().unwrap_or(&0)).max(*d[1].iter().max().unwrap_or(&0));
    for i in 0..2 {
        let current_len = if i == 0 { l } else { r };
        let mut ord: Vec<usize> = (0..current_len).collect();
        ord.sort_by(|&a, &b| d[i][a].cmp(&d[i][b]));
        let mut maps = vec![0; current_len];
        let mut nl = 0;
        let mut j = 0;
        while j < ord.len() {
            let mut nxt = j;
            let mut sum = 0;
            while nxt < ord.len() && sum + d[i][ord[nxt]] <= k_max {
                sum += d[i][ord[nxt]];
                maps[ord[nxt]] = nl;
                nxt += 1;
            }
            nl += 1;
            j = nxt;
        }
        for e in &mut edges {
            if i == 0 {
                e.0 = maps[e.0];
            } else {
                e.1 = maps[e.1];
            }
        }
        if i == 0 {
            l = nl;
        } else {
            r = nl;
        }
    }
    let n = l.max(r);
    let mut d0 = vec![0; n];
    let mut d1 = vec![0; n];
    for &(u, v) in &edges {
        d0[u] += 1;
        d1[v] += 1;
    }
    let orig_len = edges.len();
    let mut j_ptr = 0;
    for i in 0..n {
        while d0[i] < k_max {
            while j_ptr < n && d1[j_ptr] == k_max {
                j_ptr += 1;
            }
            if j_ptr < n {
                edges.push((i, j_ptr));
                d0[i] += 1;
                d1[j_ptr] += 1;
            } else {
                break;
            }
        }
    }
    let mut sol = edge_coloring_regular(n, k_max, edges);
    sol.truncate(orig_len);
    sol
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn verify_coloring(l: usize, r: usize, edges: &[(usize, usize)], colors: &[usize]) {
        assert_eq!(edges.len(), colors.len());

        let mut left_colors = vec![HashSet::new(); l];
        let mut right_colors = vec![HashSet::new(); r];
        let mut max_c = 0;

        for (i, &(u, v)) in edges.iter().enumerate() {
            let c = colors[i];
            if c > max_c {
                max_c = c;
            }

            // Check left conflict
            if left_colors[u].contains(&c) {
                panic!("Conflict at left node {} with color {}", u, c);
            }
            left_colors[u].insert(c);

            // Check right conflict
            if right_colors[v].contains(&c) {
                panic!("Conflict at right node {} with color {}", v, c);
            }
            right_colors[v].insert(c);
        }

        // Calculate max degree
        let mut d_l = vec![0; l];
        let mut d_r = vec![0; r];
        for &(u, v) in edges {
            d_l[u] += 1;
            d_r[v] += 1;
        }
        let k = *d_l
            .iter()
            .max()
            .unwrap_or(&0)
            .max(d_r.iter().max().unwrap_or(&0));

        // Ensure we didn't use unnecessary colors (optional strict check, but good for optimal coloring)
        // The algorithm guarantees max_color < k
        assert!(max_c < k, "Used color {} >= K ({})", max_c, k);
    }

    #[test]
    fn test_simple_bipartite() {
        // Square: 0-0, 0-1, 1-0, 1-1
        let l = 2;
        let r = 2;
        let edges = vec![(0, 0), (0, 1), (1, 0), (1, 1)];
        let colors = edge_coloring(l, r, edges.clone());
        verify_coloring(l, r, &edges, &colors);
    }

    #[test]
    fn test_k33() {
        let l = 3;
        let r = 3;
        let mut edges = Vec::new();
        for i in 0..l {
            for j in 0..r {
                edges.push((i, j));
            }
        }
        let colors = edge_coloring(l, r, edges.clone());
        verify_coloring(l, r, &edges, &colors);
    }

    #[test]
    fn test_irregular_graph() {
        let l = 4;
        let r = 5;
        let edges = vec![
            (0, 0),
            (0, 1),
            (1, 1),
            (1, 2),
            (1, 3),
            (2, 0),
            (2, 4),
            (3, 3),
        ];
        let colors = edge_coloring(l, r, edges.clone());
        verify_coloring(l, r, &edges, &colors);
    }

    #[test]
    fn test_empty() {
        let colors = edge_coloring(5, 5, vec![]);
        assert!(colors.is_empty());
    }
}
