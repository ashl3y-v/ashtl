use std::collections::{BinaryHeap, LinkedList, VecDeque};
use std::ops::{Add, AddAssign, Sub, SubAssign};

use rand::prelude::SliceRandom;

use crate::alg::fps::FPS;
use crate::alg::ops::inv;
use crate::ds::score::MinScore;
use crate::ds::{bit_vec::BitVec, dsu::DSU};
use crate::tree::top::StaticTopTree;

const INF: i64 = i64::MAX / 2;

// O(√n m)
pub fn hopcroft_karp(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
) -> (usize, Vec<usize>, Vec<usize>) {
    let mut l = vec![usize::MAX; n];
    let mut r = vec![usize::MAX; k];
    let mut size = 0;
    let mut rt = vec![usize::MAX; n];
    let mut fa = vec![usize::MAX; n];
    let mut q = vec![0; n];
    for u in 0..n {
        if l[u] != usize::MAX {
            continue;
        }
        for &v in &g[d[u]..d[u + 1]] {
            if r[v] == usize::MAX {
                l[u] = v;
                r[v] = u;
                size += 1;
                break;
            }
        }
    }
    loop {
        rt.fill(usize::MAX);
        fa.fill(usize::MAX);
        let mut q_n = 0;
        for i in 0..n {
            if l[i] == usize::MAX {
                q[q_n] = i;
                rt[i] = i;
                fa[i] = i;
                q_n += 1;
            }
        }
        let mut matched = false;
        let mut i = 0;
        while i < q_n {
            let u = q[i];
            if l[rt[u]] != usize::MAX {
                i += 1;
                continue;
            }
            for j in d[u]..d[u + 1] {
                let v = g[j] as usize;
                if r[v] == usize::MAX {
                    let mut vv = v;
                    let mut uu = u;
                    while vv != usize::MAX {
                        r[vv] = uu;
                        let nvv = l[uu];
                        l[uu] = vv;
                        vv = nvv;
                        uu = fa[uu];
                    }
                    matched = true;
                    size += 1;
                    break;
                }
                let rv = r[v] as usize;
                if fa[rv] == usize::MAX {
                    q[q_n] = rv;
                    fa[rv] = u;
                    rt[rv] = rt[u];
                    q_n += 1;
                }
            }
            i += 1;
        }
        if !matched {
            break;
        }
    }
    (size, l, r)
}

pub fn min_vertex_cover_bipartite(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
    l: &[usize],
    r: &[usize],
) -> (BitVec, BitVec) {
    let (mut lfound, mut seen, mut q) = (
        BitVec::from_fn(n, |i| l[i] == usize::MAX),
        BitVec::new(k, false),
        Vec::with_capacity(n),
    );
    q.extend((0..n).filter(|&i| l[i] == usize::MAX));
    while let Some(v) = q.pop() {
        lfound.set(v, true);
        for &w in &g[d[v]..d[v + 1]] {
            if !seen[w] && r[w] != usize::MAX {
                seen.set(w, true);
                q.push(r[w]);
            }
        }
    }
    lfound.negate();
    (lfound, seen)
}

pub fn min_edge_cover_bipartite(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
    l: &[usize],
    r: &[usize],
    matching_size: usize,
) -> Vec<(usize, usize)> {
    let cover_size = n + k - matching_size;
    let mut res = Vec::with_capacity(cover_size);
    for u in 0..n {
        if l[u] != usize::MAX {
            res.push((u, l[u]));
        }
    }
    for u in 0..n {
        if l[u] == usize::MAX && d[u] < d[u + 1] {
            let v = g[d[u]];
            res.push((u, v));
        }
    }
    let mut right_cover = BitVec::new(k, false);
    let mut need = (0..k).filter(|&v| r[v] == usize::MAX).count();
    'a: for u in 0..n {
        for &v in &g[d[u]..d[u + 1]] {
            if r[v] == usize::MAX && !right_cover[v] {
                right_cover.set(v, true);
                res.push((u, v));
                need -= 1;
                if need == 0 {
                    break 'a;
                }
            }
        }
    }
    res
}

pub fn max_coclique_bipartite(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
    l: &[usize],
    r: &[usize],
) -> (BitVec, BitVec) {
    let (mut in_cover_l, mut in_cover_r) = min_vertex_cover_bipartite(n, k, g, d, l, r);
    in_cover_l.negate();
    in_cover_r.negate();
    (in_cover_l, in_cover_r)
}

/// O(√V E)
pub fn dulmage_mendelsohn(n: usize, k: usize, g: &[usize], d: &[usize]) -> Vec<u8> {
    let t = n + k;
    let mut adj: Vec<Vec<usize>> = vec![vec![]; t];
    for u in 0..n {
        for &v in &g[d[u]..d[u + 1]] {
            adj[u].push(n + v);
            adj[n + v].push(u);
        }
    }
    let (_, l, _) = hopcroft_karp(n, k, g, d);
    let mut matched = vec![usize::MAX; t];
    for u in 0..n {
        if l[u] != usize::MAX {
            matched[u] = n + l[u];
            matched[n + l[u]] = u;
        }
    }
    let mut comp = vec![0; t];
    for v in 0..t {
        if matched[v] != usize::MAX {
            comp[v] = 2;
        }
    }
    let mut stack: Vec<(usize, bool)> = Vec::new();
    for v in 0..t {
        if comp[v] == 0 {
            stack.push((v, true));
        }
    }
    while let Some((u, b)) = stack.pop() {
        for &v in &adj[u] {
            if comp[v] == 2 && (b != (matched[u] == v)) {
                comp[v] = comp[u] ^ 1;
                stack.push((v, !b));
            }
        }
    }
    comp
}

/// O(√n m)
pub fn dag_path_cover(n: usize, edges: &[(usize, usize)]) -> Vec<usize> {
    let mut degree = vec![0; n];
    for &(u, _) in edges {
        degree[u] += 1;
    }
    let mut d = vec![0; n + 1];
    for i in 0..n {
        d[i + 1] = d[i] + degree[i];
    }
    let mut g = vec![0; d[n]];
    let mut counter = d.clone();
    for &(u, v) in edges {
        g[counter[u]] = v;
        counter[u] += 1;
    }
    let (_, l, _) = hopcroft_karp(n, n, &g, &d);
    let mut dsu = DSU::new(n);
    for u in 0..n {
        let v = l[u];
        if v < n {
            dsu.union(u, v);
        }
    }
    let mut ans = vec![0; n];
    let mut root_to_id = vec![usize::MAX; n];
    let mut current_id = 0;
    for v in 0..n {
        let root = dsu.find(v);
        if root_to_id[root] == usize::MAX {
            root_to_id[root] = current_id;
            current_id += 1;
        }
        ans[v] = root_to_id[root];
    }
    ans
}

pub struct Hungarian<T> {
    n: usize,
    m: usize,
    val: Vec<T>,
    init: T,
    inf: T,
}

impl<T: Copy + PartialOrd + Default + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign>
    Hungarian<T>
{
    pub fn new(n: usize, m: usize, init: T, inf: T) -> Self {
        debug_assert!(m >= n);
        Self {
            n,
            m,
            val: vec![init; n * m],
            init,
            inf,
        }
    }

    pub fn add_edge(&mut self, left: usize, right: usize, w: T) {
        let idx = left * self.m + right;
        if w > self.val[idx] {
            self.val[idx] = w;
        }
    }

    /// O(n m^2)
    pub fn calc(&self) -> (T, Vec<usize>) {
        let (n, m) = (self.n, self.m);
        if n == 0 {
            return (T::default(), vec![]);
        }
        let mut l_mt = vec![usize::MAX; n];
        let mut r_mt = vec![usize::MAX; m];
        let mut l_pt = self
            .val
            .chunks_exact(m)
            .map(|a| a.iter().fold(self.init, |a, &b| if b > a { b } else { a }))
            .collect::<Vec<_>>();
        let mut r_pt = vec![T::default(); m];
        let mut slack = vec![self.inf; m];
        let mut from_v = vec![0; m];
        let mut l_vis = BitVec::new(n, false);
        let mut r_vis = BitVec::new(m, false);
        let mut q = vec![0; n];
        let aug = |r: usize,
                   l_mt: &mut [usize],
                   r_mt: &mut [usize],
                   from_v: &[usize],
                   l_vis: &mut BitVec,
                   r_vis: &mut BitVec,
                   q: &mut [usize],
                   tail: &mut usize|
         -> bool {
            let l = r_mt[r];
            if l != usize::MAX {
                r_vis.set(r, true);
                l_vis.set(l, true);
                q[*tail] = l;
                *tail += 1;
                return false;
            }
            let mut cur = r;
            while cur != usize::MAX {
                let from_l = from_v[cur];
                let prev = l_mt[from_l];
                r_mt[cur] = from_l;
                l_mt[from_l] = cur;
                cur = prev;
            }
            true
        };
        for st in 0..n {
            l_vis.clear();
            r_vis.clear();
            slack.fill(self.inf);
            let mut head = 0;
            let mut tail = 0;
            l_vis.set(st, true);
            q[tail] = st;
            tail += 1;
            'a: loop {
                while head < tail {
                    let l = q[head];
                    head += 1;
                    for to in 0..m {
                        if r_vis[to] {
                            continue;
                        }
                        let gap = l_pt[l] + r_pt[to] - self.val[l * m + to];
                        if slack[to] >= gap {
                            from_v[to] = l;
                            if gap == T::default() {
                                if aug(
                                    to, &mut l_mt, &mut r_mt, &from_v, &mut l_vis, &mut r_vis,
                                    &mut q, &mut tail,
                                ) {
                                    break 'a;
                                }
                            } else {
                                slack[to] = gap;
                            }
                        }
                    }
                }
                let mut delta = self.inf;
                for r in 0..m {
                    if !r_vis[r] && slack[r] < delta {
                        delta = slack[r];
                    }
                }
                for l in 0..n {
                    if l_vis[l] {
                        l_pt[l] -= delta;
                    }
                }
                for r in 0..m {
                    if r_vis[r] {
                        r_pt[r] += delta;
                    } else {
                        slack[r] -= delta;
                    }
                }
                for r in 0..m {
                    if !r_vis[r] && slack[r] == T::default() {
                        if aug(
                            r, &mut l_mt, &mut r_mt, &from_v, &mut l_vis, &mut r_vis, &mut q,
                            &mut tail,
                        ) {
                            break 'a;
                        }
                    }
                }
            }
        }
        let mut res = T::default();
        for l in 0..n {
            res += self.val[l * m + l_mt[l]];
        }
        (res, l_mt)
    }
}

pub struct Assignment<T> {
    n: usize,
    m: usize,
    adj: Vec<Vec<(usize, T)>>,
    init: T,
    inf: T,
}

impl<T: Copy + PartialOrd + Default + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign>
    Assignment<T>
{
    pub fn new(n: usize, m: usize, init: T, inf: T) -> Self {
        Self {
            n,
            m,
            adj: vec![vec![]; n],
            init,
            inf,
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize, w: T) {
        self.adj[u].push((v, w));
    }

    pub fn calc(&self) -> (T, Vec<usize>) {
        let n = self.n;
        let m = self.m;
        if n == 0 {
            return (T::default(), vec![]);
        }
        let mut l_mt = vec![usize::MAX; n];
        let mut r_mt = vec![usize::MAX; m];
        let mut l_pt = vec![self.init; n];
        let mut r_pt = vec![T::default(); m];
        for u in 0..n {
            for &(_, w) in &self.adj[u] {
                if w > l_pt[u] {
                    l_pt[u] = w;
                }
            }
        }
        let mut dist = vec![self.inf; m];
        let mut from = vec![usize::MAX; m];
        let mut visited = vec![false; m];
        let mut touched = Vec::with_capacity(m);
        let mut pq = BinaryHeap::new();
        for i in 0..n {
            for &(j, w) in &self.adj[i] {
                let slack = l_pt[i] + r_pt[j] - w;
                if slack < dist[j] {
                    if dist[j] == self.inf {
                        touched.push(j);
                    }
                    dist[j] = slack;
                    from[j] = i;
                    pq.push(MinScore(slack, j));
                }
            }
            let mut end_node = usize::MAX;
            let mut path_len = T::default();
            while let Some(MinScore(d, u)) = pq.pop() {
                if d > dist[u] {
                    continue;
                }
                if visited[u] {
                    continue;
                }
                visited[u] = true;
                if r_mt[u] == usize::MAX {
                    end_node = u;
                    path_len = d;
                    break;
                }
                let ml = r_mt[u];
                for &(v, w) in &self.adj[ml] {
                    let weight = l_pt[ml] + r_pt[v] - w;
                    let new_dist = d + weight;
                    if new_dist < dist[v] {
                        if dist[v] == self.inf {
                            touched.push(v);
                        }
                        dist[v] = new_dist;
                        from[v] = ml;
                        pq.push(MinScore(new_dist, v));
                    }
                }
            }
            if end_node != usize::MAX {
                l_pt[i] -= path_len;
                for &j in &touched {
                    if dist[j] <= path_len {
                        r_pt[j] += path_len - dist[j];
                        if r_mt[j] != usize::MAX {
                            l_pt[r_mt[j]] -= path_len - dist[j];
                        }
                    }
                }
                let mut curr = end_node;
                while curr != usize::MAX {
                    let prev_l = from[curr];
                    let prev_r = l_mt[prev_l];
                    r_mt[curr] = prev_l;
                    l_mt[prev_l] = curr;
                    curr = prev_r;
                }
            }
            for &node in &touched {
                dist[node] = self.inf;
                visited[node] = false;
            }
            touched.clear();
            pq.clear();
        }
        let mut res = T::default();
        for l in 0..n {
            if l_mt[l] != usize::MAX {
                let mut best_val = None;
                for &(r, w) in &self.adj[l] {
                    if r == l_mt[l] {
                        match best_val {
                            None => best_val = Some(w),
                            Some(cur) => {
                                if w > cur {
                                    best_val = Some(w);
                                }
                            }
                        }
                    }
                }
                if let Some(val) = best_val {
                    res += val;
                }
            }
        }
        (res, l_mt)
    }
}

// https://math.mit.edu/~goemans/18438F09/lec3.pdf
/// O(n^3)
pub fn blossom(n: usize, g: &[usize], d: &[usize]) -> (usize, Vec<usize>, Vec<u8>) {
    let mut n_matches = 0;
    let mut mate = vec![0; n + 1];
    let mut q = vec![0; n + 1];
    let mut book = BitVec::new(n + 1, false);
    let mut typ = vec![u8::MAX; n + 1];
    let mut fa = vec![0; n + 1];
    let mut bl = vec![0; n + 1];
    for u in 1..=n {
        if mate[u] != 0 {
            continue;
        }
        for &v in &g[d[u]..d[u + 1]] {
            if mate[v] == 0 {
                mate[u] = v;
                mate[v] = u;
                n_matches += 1;
                break;
            }
        }
    }
    'a: for sv in 1..=n {
        if mate[sv] != 0 {
            continue;
        }
        for u in 1..=n {
            bl[u] = u;
            typ[u] = u8::MAX;
        }
        q[0] = sv;
        let mut q_n = 1;
        typ[sv] = 0;
        let mut i = 0;
        while i < q_n {
            let u = q[i];
            for &v in &g[d[u]..d[u + 1]] {
                if typ[v] == u8::MAX {
                    fa[v] = u;
                    typ[v] = 1;
                    let nu = mate[v];
                    if nu == 0 {
                        let mut vv = v;
                        while vv != 0 {
                            let nvv = mate[fa[vv]];
                            mate[vv] = fa[vv];
                            mate[fa[vv]] = vv;
                            vv = nvv;
                        }
                        n_matches += 1;
                        continue 'a;
                    }
                    q[q_n] = nu;
                    q_n += 1;
                    typ[nu] = 0;
                } else if typ[v] == 0 && bl[u] != bl[v] {
                    book.clear();
                    let mut uu = u;
                    let mut vv = v;
                    let lca = loop {
                        if uu != 0 {
                            if book[uu] {
                                break uu;
                            }
                            book.set(uu, true);
                            uu = bl[fa[mate[uu]]];
                        }
                        (uu, vv) = (vv, uu);
                    };
                    let mut go_up = |mut u, mut v, lca| {
                        while bl[u] != lca {
                            fa[u] = v;
                            v = mate[u];
                            if typ[v] == 1 {
                                q[q_n] = v;
                                q_n += 1;
                                typ[v] = 0;
                            }
                            bl[u] = lca;
                            bl[v] = lca;
                            u = fa[v];
                        }
                    };
                    go_up(u, v, lca);
                    go_up(v, u, lca);
                    for u in 1..=n {
                        bl[u] = bl[bl[u]];
                    }
                }
            }
            i += 1;
        }
    }
    for v in typ.iter_mut() {
        if *v == u8::MAX {
            *v = 2;
        }
    }
    (n_matches, mate, typ)
}

#[derive(Clone, Copy, Default, Debug)]
pub struct WeightedBlossomEdge {
    u: usize,
    v: usize,
    w: i64,
}

pub struct WeightedBlossom {
    n: usize,
    n_x: usize,
    g: Vec<Vec<WeightedBlossomEdge>>,
    pt: Vec<i64>,
    mate: Vec<usize>,
    slack: Vec<usize>,
    bl: Vec<usize>,
    fa: Vec<usize>,
    flo_from: Vec<Vec<usize>>,
    typ: Vec<i64>,
    vis: Vec<usize>,
    flo: Vec<Vec<usize>>,
    q: VecDeque<usize>,
    vis_timer: usize,
}

impl WeightedBlossom {
    pub fn new(n: usize) -> Self {
        let max_size = 2 * n + 2;
        let mut g = vec![vec![WeightedBlossomEdge::default(); max_size]; max_size];
        for u in 1..max_size {
            for v in 1..max_size {
                g[u][v] = WeightedBlossomEdge { u, v, w: 0 };
            }
        }
        Self {
            n,
            n_x: n,
            g,
            pt: vec![0; max_size],
            mate: vec![0; max_size],
            slack: vec![0; max_size],
            bl: vec![0; max_size],
            fa: vec![0; max_size],
            flo_from: vec![vec![0; max_size]; max_size],
            typ: vec![0; max_size],
            vis: vec![0; max_size],
            flo: vec![Vec::new(); max_size],
            q: VecDeque::new(),
            vis_timer: 0,
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize, w: i64) {
        if w > self.g[u][v].w {
            self.g[u][v].w = w;
            self.g[v][u].w = w;
        }
    }

    fn e_delta(&self, e: &WeightedBlossomEdge) -> i64 {
        self.pt[e.u] + self.pt[e.v] - e.w * 2
    }

    fn update_slack(&mut self, u: usize, x: usize) {
        if self.slack[x] == 0
            || self.e_delta(&self.g[u][x]) < self.e_delta(&self.g[self.slack[x]][x])
        {
            self.slack[x] = u;
        }
    }

    fn set_slack(&mut self, x: usize) {
        self.slack[x] = 0;
        for u in 1..=self.n {
            if self.g[u][x].w > 0 && self.bl[u] != x && self.typ[self.bl[u]] == 0 {
                self.update_slack(u, x);
            }
        }
    }

    fn q_push(&mut self, x: usize) {
        if x <= self.n {
            self.q.push_back(x);
        } else {
            let indices = self.flo[x].clone();
            for &idx in &indices {
                self.q_push(idx);
            }
        }
    }

    fn set_bl(&mut self, x: usize, b: usize) {
        self.bl[x] = b;
        if x > self.n {
            let indices = self.flo[x].clone();
            for &idx in &indices {
                self.set_bl(idx, b);
            }
        }
    }

    fn get_pth(&mut self, b: usize, xr: usize) -> usize {
        let pos = self.flo[b].iter().position(|&val| val == xr).unwrap();
        if pos % 2 == 1 {
            let len = self.flo[b].len();
            self.flo[b][1..len].reverse();
            self.flo[b].len() - pos
        } else {
            pos
        }
    }

    fn set_match(&mut self, u: usize, v: usize) {
        self.mate[u] = self.g[u][v].v;
        if u <= self.n {
            return;
        }
        let xr = self.flo_from[u][self.g[u][v].u];
        let pr = self.get_pth(u, xr);
        for i in 0..pr {
            let f1 = self.flo[u][i];
            let f2 = self.flo[u][i ^ 1];
            self.set_match(f1, f2);
        }
        self.set_match(xr, v);
        self.flo[u].rotate_left(pr);
    }

    fn augment(&mut self, mut u: usize, mut v: usize) {
        loop {
            let xnv = self.bl[self.mate[u]];
            self.set_match(u, v);
            if xnv == 0 {
                return;
            }
            self.set_match(xnv, self.bl[self.fa[xnv]]);
            u = self.bl[self.fa[xnv]];
            v = xnv;
        }
    }

    fn lca(&mut self, mut u: usize, mut v: usize) -> usize {
        self.vis_timer += 1;
        let t = self.vis_timer;
        while u != 0 || v != 0 {
            if u != 0 {
                if self.vis[u] == t {
                    return u;
                }
                self.vis[u] = t;
                u = self.bl[self.mate[u]];
                if u != 0 {
                    u = self.bl[self.fa[u]];
                }
            }
            std::mem::swap(&mut u, &mut v);
        }
        0
    }

    fn add_blossom(&mut self, u: usize, lca: usize, v: usize) {
        let mut b = self.n + 1;
        while b <= self.n_x && self.bl[b] != 0 {
            b += 1;
        }
        if b > self.n_x {
            self.n_x += 1;
        }
        self.pt[b] = 0;
        self.typ[b] = 0;
        self.mate[b] = self.mate[lca];
        self.flo[b] = vec![lca];
        let mut x = u;
        while x != lca {
            let y = self.bl[self.mate[x]];
            self.flo[b].push(x);
            self.flo[b].push(y);
            self.q_push(y);
            x = self.bl[self.fa[y]];
        }
        let len = self.flo[b].len();
        self.flo[b][1..len].reverse();
        x = v;
        while x != lca {
            let y = self.bl[self.mate[x]];
            self.flo[b].push(x);
            self.flo[b].push(y);
            self.q_push(y);
            x = self.bl[self.fa[y]];
        }
        self.set_bl(b, b);
        for x_i in 1..=self.n_x {
            self.g[b][x_i].w = 0;
            self.g[x_i][b].w = 0;
        }
        for x_i in 1..=self.n {
            self.flo_from[b][x_i] = 0;
        }
        for i in 0..self.flo[b].len() {
            let xs = self.flo[b][i];
            for x_i in 1..=self.n_x {
                let e_new = self.g[xs][x_i];
                if self.g[b][x_i].w == 0 || self.e_delta(&e_new) < self.e_delta(&self.g[b][x_i]) {
                    self.g[b][x_i] = e_new;
                    self.g[x_i][b] = self.g[x_i][xs];
                }
            }
            for x_i in 1..=self.n {
                if self.flo_from[xs][x_i] != 0 {
                    self.flo_from[b][x_i] = xs;
                }
            }
        }
        self.set_slack(b);
    }

    fn expand_blossom(&mut self, b: usize) {
        let indices = self.flo[b].clone();
        for &idx in &indices {
            self.set_bl(idx, idx);
        }
        let xr = self.flo_from[b][self.g[b][self.fa[b]].u];
        let pr = self.get_pth(b, xr);
        let mut i = 0;
        while i < pr {
            let xs = self.flo[b][i];
            let xns = self.flo[b][i + 1];
            self.fa[xs] = self.g[xns][xs].u;
            self.typ[xs] = 1;
            self.typ[xns] = 0;
            self.slack[xs] = 0;
            self.set_slack(xns);
            self.q_push(xns);
            i += 2;
        }
        self.typ[xr] = 1;
        self.fa[xr] = self.fa[b];
        for i in (pr + 1)..self.flo[b].len() {
            let idx = self.flo[b][i];
            self.typ[idx] = -1;
            self.set_slack(idx);
        }
        self.bl[b] = 0;
    }

    fn on_found_edge(&mut self, u_in: usize, v_in: usize) -> bool {
        let u = self.bl[u_in];
        let v = self.bl[v_in];
        if self.typ[v] == -1 {
            self.fa[v] = u_in;
            self.typ[v] = 1;
            let nu = self.bl[self.mate[v]];
            self.slack[v] = 0;
            self.slack[nu] = 0;
            self.typ[nu] = 0;
            self.q_push(nu);
        } else if self.typ[v] == 0 {
            let lca = self.lca(u, v);
            if lca == 0 {
                self.augment(u, v);
                self.augment(v, u);
                return true;
            } else {
                self.add_blossom(u, lca, v);
            }
        }
        false
    }

    fn matching(&mut self) -> bool {
        for i in 1..=self.n_x {
            self.typ[i] = -1;
            self.slack[i] = 0;
        }
        self.q.clear();
        for x in 1..=self.n_x {
            if self.bl[x] == x && self.mate[x] == 0 {
                self.fa[x] = 0;
                self.typ[x] = 0;
                self.q_push(x);
            }
        }
        if self.q.is_empty() {
            return false;
        }
        loop {
            while let Some(u) = self.q.pop_front() {
                if self.typ[self.bl[u]] == 1 {
                    continue;
                }
                for v in 1..=self.n {
                    if self.g[u][v].w > 0 && self.bl[u] != self.bl[v] {
                        let delta = self.e_delta(&self.g[u][v]);
                        if delta == 0 {
                            if self.on_found_edge(u, v) {
                                return true;
                            }
                        } else {
                            self.update_slack(u, self.bl[v]);
                        }
                    }
                }
            }
            let mut d = INF;
            for b in (self.n + 1)..=self.n_x {
                if self.bl[b] == b && self.typ[b] == 1 {
                    d = d.min(self.pt[b] / 2);
                }
            }
            for x in 1..=self.n_x {
                if self.bl[x] == x && self.slack[x] != 0 {
                    let slack_edge = self.g[self.slack[x]][x];
                    let delta = self.e_delta(&slack_edge);
                    if self.typ[x] == -1 {
                        d = d.min(delta);
                    } else if self.typ[x] == 0 {
                        d = d.min(delta / 2);
                    }
                }
            }
            for u in 1..=self.n {
                if self.typ[self.bl[u]] == 0 {
                    if self.pt[u] <= d {
                        return false;
                    }
                    self.pt[u] -= d;
                } else if self.typ[self.bl[u]] == 1 {
                    self.pt[u] += d;
                }
            }
            for b in (self.n + 1)..=self.n_x {
                if self.bl[b] == b {
                    if self.typ[b] == 0 {
                        self.pt[b] += d * 2;
                    } else if self.typ[b] == 1 {
                        self.pt[b] -= d * 2;
                    }
                }
            }
            self.q.clear();
            for x in 1..=self.n_x {
                if self.bl[x] == x && self.slack[x] != 0 && self.bl[self.slack[x]] != x {
                    let delta = self.e_delta(&self.g[self.slack[x]][x]);
                    if delta == 0 {
                        if self.on_found_edge(self.slack[x], x) {
                            return true;
                        }
                    }
                }
            }
            for b in (self.n + 1)..=self.n_x {
                if self.bl[b] == b && self.typ[b] == 1 && self.pt[b] == 0 {
                    self.expand_blossom(b);
                }
            }
        }
    }

    /// O(n^3)
    pub fn calc(&mut self) -> (i64, usize) {
        for i in 1..=self.n {
            self.mate[i] = 0;
        }
        self.n_x = self.n;
        let mut n_matches = 0;
        let mut tot_weight: i64 = 0;
        let mut w_max = 0;
        for u in 0..=self.n {
            self.bl[u] = u;
            self.flo[u].clear();
        }
        for u in 1..=self.n {
            for v in 1..=self.n {
                self.flo_from[u][v] = if u == v { u } else { 0 };
                w_max = w_max.max(self.g[u][v].w);
            }
        }
        for u in 1..=self.n {
            self.pt[u] = w_max;
        }
        while self.matching() {
            n_matches += 1;
        }
        for u in 1..=self.n {
            if self.mate[u] != 0 && self.mate[u] < u {
                tot_weight += self.g[u][self.mate[u]].w;
            }
        }
        (tot_weight, n_matches)
    }
}

pub struct GabowBlossom {
    n: usize,
    nh: usize,
    g: Vec<(usize, usize)>,
    d: Vec<usize>,
    mate: Vec<usize>,
    p: Vec<i64>,
    pt: Vec<i64>,
    link: Vec<(usize, usize)>,
    q: VecDeque<usize>,
    dsu: DSU,
    list: Vec<LinkedList<usize>>,
    bl: Vec<LinkedList<usize>>,
    dsu_changelog: Vec<(usize, usize)>,
    dsu_changelog_last: usize,
    dsu_changelog_size: usize,
    stk: Vec<usize>,
    time_current: i64,
    time_augment: i64,
    contract_count: i64,
    outer_id: i64,
}

impl GabowBlossom {
    const K_INNER: i64 = -1;
    const K_FREE: i64 = 0;

    pub fn new(n: usize, input_edges: &[(usize, usize)]) -> Self {
        let nh = n >> 1;
        let mut d = vec![0; n + 2];
        let m = input_edges.len();
        let mut g = vec![(0, 0); m * 2];
        for &(u, v) in input_edges {
            d[u + 2] += 1;
            d[v + 2] += 1;
        }
        for i in 1..=n + 1 {
            d[i] += d[i - 1];
        }
        for &(u, v) in input_edges {
            let u1 = u + 1;
            let v1 = v + 1;
            g[d[u1]] = (u1, v1);
            d[u1] += 1;
            g[d[v1]] = (v1, u1);
            d[v1] += 1;
        }
        for i in (1..=n + 1).rev() {
            d[i] = d[i - 1];
        }
        d[0] = 0;
        let mut list = Vec::with_capacity(nh + 1);
        for _ in 0..=nh {
            list.push(LinkedList::new());
        }
        let mut bl = Vec::with_capacity(n + 1);
        for _ in 0..=n {
            bl.push(LinkedList::new());
        }
        Self {
            n,
            nh,
            g,
            d,
            mate: vec![0; n + 1],
            p: vec![1; n + 1],
            pt: vec![Self::K_FREE; n + 1],
            link: vec![(0, 0); n + 1],
            q: VecDeque::with_capacity(n),
            dsu: DSU::new(n + 1),
            list,
            bl,
            dsu_changelog: vec![(0, 0); n],
            dsu_changelog_last: 0,
            dsu_changelog_size: 0,
            stk: Vec::with_capacity(n),
            time_current: 0,
            time_augment: INF,
            contract_count: 0,
            outer_id: 1,
        }
    }

    /// O(√n m)
    pub fn calc(&mut self) -> usize {
        self.initialize();
        let mut match_count = 0;
        while match_count * 2 + 1 < self.n {
            self.reset_count();
            let has_augmenting_path = self.do_edmonds_search();
            if !has_augmenting_path {
                break;
            }
            match_count += self.find_maximal();
            self.clear();
        }
        match_count
    }

    pub fn edges(&self) -> Vec<(usize, usize)> {
        let mut ans = Vec::new();
        for i in 1..=self.n {
            if self.mate[i] > i {
                ans.push((i - 1, self.mate[i] - 1));
            }
        }
        ans
    }

    fn initialize(&mut self) {
        self.mate.fill(0);
        self.p.fill(1);
        self.pt.fill(Self::K_FREE);
        self.link.fill((0, 0));
        self.dsu.p.fill(-1);
        for l in &mut self.list {
            l.clear();
        }
        for b in &mut self.bl {
            b.clear();
        }
        self.q.clear();
        self.stk.clear();
    }

    fn reset_count(&mut self) {
        self.time_current = 0;
        self.time_augment = INF;
        self.contract_count = 0;
        self.outer_id = 1;
        self.dsu_changelog_size = 0;
        self.dsu_changelog_last = 0;
    }

    fn clear(&mut self) {
        self.q.clear();
        for u in 1..=self.n {
            self.p[u] = 1;
            self.dsu.p[u] = -1;
            self.bl[u].clear();
        }
        let limit = self.n / 2;
        let start = self.time_current as usize;
        for t in start..=limit {
            if t < self.list.len() {
                self.list[t].clear();
            }
        }
    }

    fn grow(&mut self, x: usize, y: usize, z: usize) {
        self.pt[y] = Self::K_INNER;
        self.p[y] = self.time_current;
        self.link[z] = (x, y);
        self.pt[z] = self.pt[x];
        self.p[z] = self.time_current + 1;
        self.q.push_back(z);
    }

    fn contract(&mut self, x: usize, y: usize) {
        let mut bx = self.dsu.find(x);
        let mut by = self.dsu.find(y);
        self.contract_count += 1;
        let h = -(self.contract_count) + Self::K_INNER;
        self.pt[self.mate[bx]] = h;
        self.pt[self.mate[by]] = h;
        let mut lca;
        loop {
            if self.mate[by] != 0 {
                std::mem::swap(&mut bx, &mut by);
            }
            bx = self.dsu.find(self.link[bx].0);
            lca = bx;
            if self.pt[self.mate[bx]] == h {
                break;
            }
            self.pt[self.mate[bx]] = h;
        }
        for &v_start in &[self.dsu.find(x), self.dsu.find(y)] {
            let mut bv = v_start;
            while bv != lca {
                let mv = self.mate[bv];
                self.link[mv] = (x, y);
                self.pt[mv] = self.pt[x];
                self.p[mv] = 1 + (self.time_current - self.p[mv]) + self.time_current;
                self.q.push_back(mv);
                self.dsu.p[bv] = lca as isize;
                self.dsu_changelog[self.dsu_changelog_last] = (bv, lca);
                self.dsu_changelog_last += 1;
                self.dsu.p[mv] = lca as isize;
                self.dsu_changelog[self.dsu_changelog_last] = (mv, lca);
                self.dsu_changelog_last += 1;
                bv = self.dsu.find(self.link[bv].0);
            }
        }
    }

    fn find_augmenting_path(&mut self) -> bool {
        while let Some(x) = self.q.pop_front() {
            let lx = self.pt[x];
            let px = self.p[x];
            let mut bx = self.dsu.find(x);
            for eid in self.d[x]..self.d[x + 1] {
                let y = self.g[eid].1;
                let ly = self.pt[y];
                if ly > 0 {
                    let time_next = (px + self.p[y]) >> 1;
                    if lx != ly {
                        if time_next == self.time_current {
                            return true;
                        }
                        self.time_augment = std::cmp::min(time_next, self.time_augment);
                    } else {
                        if bx == self.dsu.find(y) {
                            continue;
                        }
                        if time_next == self.time_current {
                            self.contract(x, y);
                            bx = self.dsu.find(x);
                        } else if (time_next as usize) <= self.nh {
                            self.list[time_next as usize].push_front(eid);
                        }
                    }
                    if ly > 0
                        && lx == ly
                        && bx != self.dsu.find(y)
                        && ((px + self.p[y]) >> 1) == self.time_current
                    {
                        bx = self.dsu.find(x);
                    }
                } else if ly == Self::K_FREE {
                    let time_next = px + 1;
                    if time_next == self.time_current {
                        self.grow(x, y, self.mate[y]);
                    } else if (time_next as usize) <= self.nh {
                        self.list[time_next as usize].push_front(eid);
                    }
                }
            }
        }
        false
    }

    fn adjust_dual_variables(&mut self) -> bool {
        let time_lim = (self.nh as i64 + 1).min(self.time_augment);
        self.time_current += 1;
        while self.time_current <= time_lim {
            self.dsu_changelog_size = self.dsu_changelog_last;
            if self.time_current == time_lim {
                break;
            }
            let current_list = std::mem::take(&mut self.list[self.time_current as usize]);
            let mut updated = false;
            for eid in current_list {
                let e = self.g[eid];
                let (x, y) = e;
                let ly = self.pt[y];
                if ly > 0 {
                    if self.p[x] + self.p[y] != (self.time_current << 1) {
                        continue;
                    }
                    if self.dsu.find(x) == self.dsu.find(y) {
                        continue;
                    }
                    if self.pt[x] != ly {
                        self.time_augment = self.time_current;
                        return false;
                    }
                    self.contract(x, y);
                    updated = true;
                } else if ly == Self::K_FREE {
                    self.grow(x, y, self.mate[y]);
                    updated = true;
                }
            }
            if updated {
                return false;
            }
            self.time_current += 1;
        }
        self.time_current > (self.nh as i64)
    }

    fn do_edmonds_search(&mut self) -> bool {
        self.pt[0] = Self::K_FREE;
        for u in 1..=self.n {
            if self.mate[u] == 0 {
                self.q.push_back(u);
                self.pt[u] = u as i64;
            } else {
                self.pt[u] = Self::K_FREE;
            }
        }
        loop {
            if self.find_augmenting_path() {
                break;
            }
            let maximum = self.adjust_dual_variables();
            if maximum {
                return false;
            }
            if self.time_current == self.time_augment {
                break;
            }
        }
        for u in 1..=self.n {
            if self.pt[u] > 0 {
                self.p[u] -= self.time_current;
            } else if self.pt[u] < 0 {
                self.p[u] = 1 + (self.time_current - self.p[u]);
            }
        }
        true
    }

    fn rematch(&mut self, v: usize, w: usize) {
        let t = self.mate[v];
        self.mate[v] = w;
        if self.mate[t] != v {
            return;
        }
        if self.link[v].1 == self.dsu.find(self.link[v].1) {
            self.mate[t] = self.link[v].0;
            self.rematch(self.mate[t], t);
        } else {
            let (x, y) = self.link[v];
            self.rematch(x, y);
            self.rematch(y, x);
        }
    }

    fn dfs_augment(&mut self, x: usize, bx: usize) -> bool {
        let px = self.p[x];
        let lx = self.pt[bx];
        for eid in self.d[x]..self.d[x + 1] {
            let y = self.g[eid].1;
            if px + self.p[y] != 0 {
                continue;
            }
            let by = self.dsu.find(y);
            let ly = self.pt[by];
            if ly > 0 {
                if lx >= ly {
                    continue;
                }
                let stack_beg = self.stk.len();
                let mut bv = by;
                while bv != bx {
                    let mv = self.mate[bv];
                    let bw = self.dsu.find(mv);
                    self.stk.push(bw);
                    self.link[bw] = (x, y);
                    self.dsu.p[bv] = bx as isize;
                    self.dsu.p[bw] = bx as isize;
                    bv = self.dsu.find(self.link[bv].0);
                }
                let mut success = false;
                while self.stk.len() > stack_beg {
                    let bw = self.stk.pop().unwrap();
                    let children: Vec<usize> = self.bl[bw].iter().cloned().collect();
                    for v in children {
                        if !success {
                            if self.dfs_augment(v, bx) {
                                success = true;
                            }
                        }
                    }
                    if success {
                        break;
                    }
                }
                if success {
                    self.stk.truncate(stack_beg);
                    return true;
                }
                self.stk.truncate(stack_beg);
            } else if ly == Self::K_FREE {
                self.pt[by] = Self::K_INNER;
                let z = self.mate[by];
                if z == 0 {
                    self.rematch(x, y);
                    self.rematch(y, x);
                    return true;
                }
                let bz = self.dsu.find(z);
                self.link[bz] = (x, y);
                self.pt[bz] = self.outer_id;
                self.outer_id += 1;
                let children: Vec<usize> = self.bl[bz].iter().cloned().collect();
                for v in children {
                    if self.dfs_augment(v, bz) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn find_maximal(&mut self) -> usize {
        self.dsu.p.fill(-1);
        for i in 0..self.dsu_changelog_size {
            let (v, par) = self.dsu_changelog[i];
            self.dsu.p[v] = par as isize;
        }
        for u in 1..=self.n {
            self.pt[u] = Self::K_FREE;
            self.bl[u].clear();
        }
        for u in 1..=self.n {
            self.bl[self.dsu.find(u)].push_front(u);
        }
        let mut ret = 0;
        for u in 1..=self.n {
            if self.mate[u] == 0 {
                let bu = self.dsu.find(u);
                if self.pt[bu] != Self::K_FREE {
                    continue;
                }
                self.pt[bu] = self.outer_id;
                self.outer_id += 1;
                let children: Vec<usize> = self.bl[bu].iter().cloned().collect();
                for v in children {
                    if self.dfs_augment(v, bu) {
                        ret += 1;
                        break;
                    }
                }
            }
        }
        ret
    }
}

// TODO: O(√n m) maximum matching
// https://arxiv.org/pdf/1703.03998
// https://judge.yosupo.jp/submission/51928

/// O(2^n Δ) = O(2^n n) time, O(n + m) space
pub fn count_perfect_matchings<const M: u64>(n: usize, g: &[usize], d: &[usize]) -> u64 {
    if n == 0 {
        return 1;
    } else if n % 2 == 1 {
        return 0;
    }
    let half = n / 2;
    let m = d[n] / 2;
    let mut binom = vec![0u64; m + 1];
    if half <= m {
        binom[half] = 1;
        for i in half + 1..=m {
            binom[i] = binom[i - 1] * (i as u64) % M;
            binom[i] = (binom[i] as i64 * inv::<M>((i - half) as i64)).rem_euclid(M as i64) as u64;
        }
    }
    let mut deg = vec![0; n];
    let mut in_set = BitVec::new(n, false);
    let mut e = 0;
    let mut size = 0;
    let mut res = 0;
    let sign = |sz| -> u64 { if (n - sz) % 2 == 0 { 1 } else { M - 1 } };
    let n_words = (n + 63) / 64;
    let mut counter = vec![0u64; n_words];
    loop {
        let flip_bit = {
            let mut bit = n_words * 64;
            for (i, word) in counter.iter_mut().enumerate() {
                let old = *word;
                *word = word.wrapping_add(1);
                if old != u64::MAX {
                    bit = i * 64 + word.trailing_zeros() as usize;
                    break;
                }
            }
            bit
        };
        if flip_bit >= n {
            break;
        }
        let v = flip_bit;
        if in_set[v] {
            e -= deg[v];
            size -= 1;
            in_set.set(v, false);
            for &u in &g[d[v]..d[v + 1]] {
                deg[u] -= 1;
            }
        } else {
            e += deg[v];
            size += 1;
            in_set.set(v, true);
            for &u in &g[d[v]..d[v + 1]] {
                deg[u] += 1;
            }
        }
        if e >= half {
            res = (res + sign(size) * binom[e]) % M;
        }
    }
    res
}

/// O(n log^2 n)
pub fn count_matching_on_tree<const M: u64>(p: &[usize]) -> Vec<i64> {
    type State<const M: u64> = [[FPS<M>; 2]; 2];
    #[derive(Clone)]
    struct Path<const M: u64> {
        single: bool,
        s: State<M>,
    }
    impl<const M: u64> Default for Path<M> {
        fn default() -> Self {
            Path {
                single: true,
                s: Default::default(),
            }
        }
    }
    type Point<const M: u64> = State<M>;
    let n = p.len();
    if n == 0 {
        return vec![1];
    } else if n == 1 {
        return vec![1];
    }
    let stt = StaticTopTree::new(p);
    let id: Point<M> = {
        let mut s: State<M> = Default::default();
        s[0][0] = FPS::new(vec![1]);
        s
    };
    let result: Path<M> = stt.calc::<Path<M>, Point<M>>(
        |_| -> Path<M> {
            let mut p = Path::default();
            p.single = true;
            p.s[0][0] = FPS::new(vec![1]);
            p
        },
        |l: Path<M>, r: Path<M>| -> Path<M> {
            let mut z = Path {
                single: false,
                s: Default::default(),
            };
            for a in 0..2 {
                for d in 0..2 {
                    let l_sum = l.s[a][0].clone() + &l.s[a][1];
                    let r_sum = r.s[0][d].clone() + &r.s[1][d];
                    z.s[a][d] += l_sum * &r_sum;
                    let new_a = if l.single { 1 } else { a };
                    let new_d = if r.single { 1 } else { d };
                    z.s[new_a][new_d] += l.s[a][0].clone() * &r.s[0][d] << 1;
                }
            }
            z
        },
        |l: Point<M>, r: Point<M>| -> Point<M> {
            let mut z: Point<M> = Default::default();
            z[0][0] = l[0][0].clone() * &r[0][0];
            z[1][1] = l[0][0].clone() * &r[1][1] + l[1][1].clone() * &r[0][0];
            z
        },
        |p: Path<M>| -> Point<M> {
            let mut z: Point<M> = Default::default();
            let sum_all: FPS<M> = (0..2)
                .flat_map(|a| (0..2).map(move |b| (a, b)))
                .fold(FPS::default(), |acc, (a, b)| acc + &p.s[a][b]);
            let sum_top_unmatched = p.s[0][0].clone() + &p.s[0][1];
            z[0][0] = sum_all;
            z[1][1] = sum_top_unmatched << 1;
            z
        },
        |pt: Point<M>, _v| -> Path<M> {
            let mut z = Path {
                single: true,
                s: Default::default(),
            };
            z.s[0][0] = pt[0][0].clone();
            z.s[1][1] = pt[1][1].clone();
            z
        },
        id,
    );
    let mut ans = FPS::<M>::default();
    for a in 0..2 {
        for b in 0..2 {
            ans += &result.s[a][b];
        }
    }
    let mut coeff = ans.pos_normalize().coeff;
    while coeff.len() > 1 && coeff.last() == Some(&0) {
        coeff.pop();
    }
    coeff
}

pub struct StableMatching {
    n1: usize,
    n2: usize,
    dat: Vec<Vec<(usize, i64, i64)>>,
}

impl StableMatching {
    pub fn new(n1: usize, n2: usize) -> Self {
        Self {
            n1,
            n2,
            dat: vec![Vec::new(); n1],
        }
    }

    pub fn add(&mut self, v1: usize, v2: usize, x1: i64, x2: i64) {
        self.dat[v1].push((v2, x1, x2));
    }

    /// O((n1 + m) log m)
    pub fn calc(&mut self) -> Vec<(usize, usize)> {
        for v1 in 0..self.n1 {
            self.dat[v1].sort_by_key(|&(_, x1, _)| x1);
        }
        let mut match_1 = vec![usize::MAX; self.n1];
        let mut match_2 = vec![usize::MAX; self.n2];
        let mut val_2 = vec![i64::MIN; self.n2];
        let mut queue: Vec<usize> = (0..self.n1).collect();
        while let Some(v1) = queue.pop() {
            match_1[v1] = usize::MAX;
            let Some((v2, _x1, x2)) = self.dat[v1].pop() else {
                continue;
            };
            if val_2[v2] >= x2 {
                queue.push(v1);
                continue;
            }
            if match_2[v2] != usize::MAX {
                queue.push(match_2[v2]);
            }
            match_1[v1] = v2;
            match_2[v2] = v1;
            val_2[v2] = x2;
        }
        (0..self.n1)
            .filter_map(|v1| {
                let v2 = match_1[v1];
                (v2 != usize::MAX).then_some((v1, v2))
            })
            .collect()
    }
}

pub struct BipartiteRegularMatching<F>
where
    F: Fn(usize) -> usize,
{
    pub n: usize,
    pub mtl: Vec<usize>,
    pub mtr: Vec<usize>,
    pub ord: Vec<usize>,
    pub path: Vec<(usize, usize)>,
    pub pos: Vec<usize>,
    pub sample_out: F,
}

// https://arxiv.org/pdf/0909.3346
impl<F> BipartiteRegularMatching<F>
where
    F: Fn(usize) -> usize,
{
    pub fn new(n: usize, sample_out: F) -> Self {
        let mut obj = Self {
            n,
            mtl: vec![usize::MAX; n],
            mtr: vec![usize::MAX; n],
            ord: (0..n).collect(),
            path: Vec::with_capacity(3 * n + 20),
            pos: vec![usize::MAX; n],
            sample_out,
        };
        obj.ord.shuffle(&mut rand::rng());
        obj
    }

    /// O(n log n) ex.
    pub fn solve(&mut self) {
        self.mtl.fill(usize::MAX);
        self.mtr.fill(usize::MAX);
        for i in 0..self.n {
            self.walk(self.ord[i]);
        }
        for v in 0..self.n {
            if self.mtr[v] != usize::MAX {
                self.mtl[self.mtr[v]] = v;
            }
        }
    }

    fn walk(&mut self, mut s: usize) {
        while s != usize::MAX {
            let v = (self.sample_out)(s);
            (self.mtr[v], s) = (s, self.mtr[v]);
        }
    }

    /// O(n log n)
    pub fn solve_whp(&mut self) {
        self.mtl.fill(usize::MAX);
        self.mtr.fill(usize::MAX);
        for j in 0..self.n {
            let n_f = self.n as f64;
            let j_f = j as f64;
            let budget = 2.0 * (2.0 + n_f / (n_f - j_f));
            let b_limit = budget.ceil() as usize;
            let mut start_node = None;
            for &candidate in &self.ord {
                if self.mtl[candidate] == usize::MAX {
                    start_node = Some(candidate);
                    break;
                }
            }
            if let Some(s) = start_node {
                loop {
                    if self.truncated_walk(s, b_limit) {
                        break;
                    }
                }
            }
        }
    }

    fn truncated_walk(&mut self, mut s: usize, mut b: usize) -> bool {
        self.path.clear();
        self.pos[s] = 0;
        let mut success = false;
        b += 1;
        while b > 0 {
            b -= 1;
            let v = (self.sample_out)(s);
            if self.mtr[v] == s {
                continue;
            }
            let u = self.mtr[v];
            if u != usize::MAX {
                let pos = self.pos[u];
                if pos != usize::MAX {
                    self.pos[s] = usize::MAX;
                    for (u_node, _) in &self.path[pos + 1..] {
                        self.pos[*u_node] = usize::MAX;
                    }
                    self.path.truncate(pos);
                    s = u;
                    continue;
                }
            }
            self.path.push((s, v));
            if u == usize::MAX {
                self.apply_path();
                success = true;
                break;
            }
            s = u;
            self.pos[s] = self.path.len();
        }
        self.pos[s] = usize::MAX;
        for (u, _) in &self.path {
            self.pos[*u] = usize::MAX;
        }
        success
    }

    fn apply_path(&mut self) {
        for &(u, v) in &self.path {
            let old_u = self.mtr[v];
            if old_u != usize::MAX {
                self.mtl[old_u] = usize::MAX;
            }
            self.mtl[u] = v;
            self.mtr[v] = u;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_graph(n: usize, edges: &[(usize, usize, i64)]) -> (i64, usize, Vec<usize>) {
        let mut matcher = WeightedBlossom::new(n);
        for &(u, v, w) in edges {
            matcher.add_edge(u, v, w);
        }
        let calc = matcher.calc();
        (calc.0, calc.1, matcher.mate.clone())
    }

    #[test]
    fn test_triangle_with_legs_force_expand() {
        // This test is designed to trigger expand_blossom.
        // Core: Triangle 1-2-3 with weight 10.
        // Legs: 1-4, 2-5, 3-6 with weight 20.
        //
        // Initial behavior: The algorithm will likely pick edges inside the triangle
        // (e.g., 1-2) because they form a tight blossom early on or due to greedy initialization.
        //
        // Optimal Solution: Match the legs! (1,4), (2,5), (3,6).
        // Total Weight: 20 + 20 + 20 = 60.
        // (Matching inside triangle gives at best 10 + 20 = 30).
        //
        // The algorithm must shrink 1-2-3 into a blossom, realize it's suboptimal
        // as the dual variables change, reduce the blossom dual to 0,
        // and then EXPAND it to allow the external connections.

        let n = 6;
        let edges = vec![
            // Triangle (The Blossom)
            (1, 2, 10),
            (2, 3, 10),
            (3, 1, 10),
            // Legs (The Optimal Match)
            (1, 4, 20),
            (2, 5, 20),
            (3, 6, 20),
        ];

        let (weight, count, mates) = solve_graph(n, &edges);

        assert_eq!(weight, 60);
        assert_eq!(count, 3);
        assert_eq!(mates[1], 4);
        assert_eq!(mates[2], 5);
        assert_eq!(mates[3], 6);
    }

    #[test]
    fn test_pentagon_blossom() {
        // A 5-cycle (pentagon) is the classic odd-cycle case.
        // 1-2-3-4-5-1.
        // Optimal is 2 edges (weight 20).
        let n = 5;
        let edges = vec![(1, 2, 10), (2, 3, 10), (3, 4, 10), (4, 5, 10), (5, 1, 10)];

        let (weight, count, _) = solve_graph(n, &edges);

        // Max weight is 20 (e.g., 1-2, 3-4, 5 is free)
        assert_eq!(weight, 20);
        assert_eq!(count, 2);
    }

    #[test]
    fn test_nested_blossom_structure() {
        // Constructing a scenario that might form nested blossoms.
        // A triangle 1-2-3.
        // Node 1 is also part of a larger odd cycle 1-4-5-6-7-1?
        // Let's rely on a known hard graph: The "Prism" or just weighted complexity.

        // 1-2 (100)
        // 2-3 (100)
        // 3-4 (100)
        // 4-5 (100)
        // 5-6 (100)
        // 6-1 (100) -> Hexagon (Even cycle, bipartite-ish)
        // Cross edges to make it non-bipartite and form odd cycles
        // 1-4 (50)
        // 2-5 (50)
        // 3-6 (50)

        // Optimal: 1-2, 3-4, 5-6 (300).
        // Or: 1-6, 2-3, 4-5 (300).
        // The cross edges create triangles (e.g. 1-2-5... no wait).
        // 1-2-3-4-1 is a 4-cycle.
        // 1-2-5-4-1... 1-2(100)-5(50)-4(100)-1(50).

        let n = 6;
        let edges = vec![
            (1, 2, 100),
            (2, 3, 100),
            (3, 4, 100),
            (4, 5, 100),
            (5, 6, 100),
            (6, 1, 100),
            (1, 4, 50),
            (2, 5, 50),
            (3, 6, 50),
        ];

        let (weight, count, _) = solve_graph(n, &edges);

        assert_eq!(weight, 300);
        assert_eq!(count, 3);
    }

    #[test]
    fn test_disconnected_weighted_components() {
        let n = 4;
        let edges = vec![
            (1, 2, 100), // Component 1
            (3, 4, 200), // Component 2
        ];

        let (weight, count, mates) = solve_graph(n, &edges);

        assert_eq!(weight, 300);
        assert_eq!(count, 2);
        assert_eq!(mates[1], 2);
        assert_eq!(mates[3], 4);
    }

    #[test]
    fn test_single_heavy_edge_vs_many_light() {
        // Path 1-2-3-4.
        // 1-2 (10), 2-3 (100), 3-4 (10).
        // Optimal: 2-3 (100).
        // Greedy might fail if not careful, but max weight matching should prioritize 2-3.
        let n = 4;
        let edges = vec![(1, 2, 10), (2, 3, 100), (3, 4, 10)];

        let (weight, count, mates) = solve_graph(n, &edges);

        assert_eq!(weight, 100);
        assert_eq!(count, 1);
        assert_eq!(mates[2], 3);
    }
}

#[cfg(test)]
mod tests_p {
    use super::*;
    use std::cmp::max;
    use std::collections::HashSet;

    /// Helper function to validate that the output is indeed a valid matching.
    /// It checks:
    /// 1. The size matches the expected size.
    /// 2. Every edge in the matching actually exists in the input.
    /// 3. No vertex appears more than once in the matching.
    fn validate_matching(
        n: usize,
        input_edges: &[(usize, usize)],
        result_edges: &[(usize, usize)],
        expected_size: usize,
    ) {
        assert_eq!(result_edges.len(), expected_size, "Matching size incorrect");

        // Create a set of input edges for O(1) lookup (undirected)
        let mut valid_edges = HashSet::new();
        for &(u, v) in input_edges {
            valid_edges.insert((u.min(v), max(u, v)));
        }

        let mut matched_vertices = HashSet::new();

        for &(u, v) in result_edges {
            // Check edge validity
            let sorted_edge = (u.min(v), max(u, v));
            assert!(
                valid_edges.contains(&sorted_edge),
                "Result edge {:?} does not exist in input graph",
                (u, v)
            );

            // Check vertex uniqueness
            assert!(
                matched_vertices.insert(u),
                "Vertex {} used twice in matching",
                u
            );
            assert!(
                matched_vertices.insert(v),
                "Vertex {} used twice in matching",
                v
            );
        }
    }

    #[test]
    fn test_empty_graph() {
        let n = 5;
        let edges = vec![];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();

        assert_eq!(size, 0);
        assert!(matcher.edges().is_empty());
    }

    #[test]
    fn test_single_edge() {
        let n = 2;
        let edges = vec![(0, 1)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 1);
    }

    #[test]
    fn test_disconnected_pairs() {
        // 0-1 and 2-3 are separate
        let n = 4;
        let edges = vec![(0, 1), (2, 3)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 2);
    }

    #[test]
    fn test_linear_chain() {
        // 0-1-2-3
        // Maximum matching is (0,1) and (2,3) -> Size 2
        let n = 4;
        let edges = vec![(0, 1), (1, 2), (2, 3)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 2);
    }

    #[test]
    fn test_triangle_odd_cycle() {
        // 0-1, 1-2, 2-0
        // Max matching is 1 (one node left out)
        let n = 3;
        let edges = vec![(0, 1), (1, 2), (2, 0)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 1);
    }

    #[test]
    fn test_simple_blossom() {
        // This is the critical case for General Matching vs Bipartite Matching.
        // Graph: 0 matched to 1, and 1 is part of a triangle (1-2-3-1).
        // 0 -- 1
        //      | \
        //      3--2
        // If we greedily match (1,2), we can't match 0 or 3.
        // Correct matching: (0,1) and (2,3). Size 2.
        let n = 4;
        let edges = vec![
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 1), // The blossom
        ];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 2);
    }

    #[test]
    fn test_complete_graph_k4() {
        // K4 is fully connected. Max matching is N/2 = 2.
        let n = 4;
        let edges = vec![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 2);
    }

    #[test]
    fn test_complete_graph_k5() {
        // K5, N=5. Max matching is floor(5/2) = 2. One node unmatched.
        let n = 5;
        let mut edges = Vec::new();
        for i in 0..n {
            for j in (i + 1)..n {
                edges.push((i, j));
            }
        }
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 2);
    }

    #[test]
    fn test_petersen_graph() {
        // The Petersen graph has 10 vertices and 15 edges.
        // It has a perfect matching (size 5).
        let n = 10;
        let edges = vec![
            // Outer star
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 4),
            (4, 0),
            // Inner star (0 connected to 5, etc)
            (0, 5),
            (1, 6),
            (2, 7),
            (3, 8),
            (4, 9),
            // Inner cycle (star shape) 5-7-9-6-8-5
            (5, 7),
            (7, 9),
            (9, 6),
            (6, 8),
            (8, 5),
        ];

        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 5);
    }

    #[test]
    fn test_star_graph() {
        // Center 0 connected to 1, 2, 3, 4.
        // Max matching is 1 (0 connected to any leaf).
        let n = 5;
        let edges = vec![(0, 1), (0, 2), (0, 3), (0, 4)];
        let mut matcher = GabowBlossom::new(n, &edges);
        let size = matcher.calc();
        let res = matcher.edges();

        validate_matching(n, &edges, &res, 1);
    }

    #[test]
    fn test_reuse_struct() {
        // Ensure the struct works if we run it, then get edges multiple times,
        // or if logic allows, re-run (though current API is designed for one-shot construction).
        // We will just test that calling get_edges multiple times is consistent.
        let n = 4;
        let edges = vec![(0, 1), (2, 3)];
        let mut matcher = GabowBlossom::new(n, &edges);
        matcher.calc();

        let res1 = matcher.edges();
        let res2 = matcher.edges();

        assert_eq!(res1.len(), 2);
        assert_eq!(res1, res2);
    }
}
