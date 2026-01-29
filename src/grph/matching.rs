use std::ops::{Add, AddAssign, Sub, SubAssign};

use rand::prelude::SliceRandom;

use crate::alg::fps::FPS;
use crate::alg::ops::inv;
use crate::ds::{bit_vec::BitVec, dsu::DSU};
use crate::tree::top::StaticTopTree;

/// O(√n m)
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

// Minimum vertex cover of bipartite graph O(sqrt(|V|) |E|) with hopcroft-karp
// returns (in_cover_l, in_cover_r)
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

// Minimum edge cover of bipartite graph O(sqrt(|V|) |E|) with hopcroft-karp
// returns edges as (left_vertex, right_vertex) pairs
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

// Maximum co-clique of bipartite graph O(sqrt(|V|) |E|) with hopcroft-karp
// returns (in_coclique_l, in_coclique_r)
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
}

impl<T: Copy + PartialOrd + Default + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign>
    Hungarian<T>
{
    pub fn new(n: usize, m: usize, init: T) -> Self {
        debug_assert!(m >= n);
        Self {
            n,
            m,
            val: vec![init; n * m],
            init,
        }
    }

    pub fn add_edge(&mut self, left: usize, right: usize, w: T) {
        self.val[left * self.m + right] = w;
    }

    /// O(n m^2)
    pub fn calc(&self, inf: T) -> (T, Vec<usize>) {
        let (n, m) = (self.n, self.m);
        if n == 0 {
            return (T::default(), vec![]);
        }
        let mut l_mt = vec![usize::MAX; n];
        let mut r_mt = vec![usize::MAX; m];
        let mut l_label = self
            .val
            .chunks_exact(m)
            .map(|a| a.iter().fold(self.init, |a, &b| if b > a { b } else { a }))
            .collect::<Vec<_>>();
        let mut r_label = vec![T::default(); m];
        let mut slack = vec![inf; m];
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
            slack.fill(inf);
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
                        let gap = l_label[l] + r_label[to] - self.val[l * m + to];
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
                let mut delta = inf;
                for r in 0..m {
                    if !r_vis[r] && slack[r] < delta {
                        delta = slack[r];
                    }
                }
                for l in 0..n {
                    if l_vis[l] {
                        l_label[l] -= delta;
                    }
                }
                for r in 0..m {
                    if r_vis[r] {
                        r_label[r] += delta;
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
            *v = 3;
        }
    }
    (n_matches, mate, typ)
}

// TODO: weighted blossom
// https://judge.yosupo.jp/submission/295392
// https://judge.yosupo.jp/problem/general_weighted_matching

// TODO: O(m √n log ?) maximum matching
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

// TODO: O(n log n) regular bipartite perfect matching
// https://judge.yosupo.jp/submission/342111

// https://www.tau.ac.il/~nogaa/PDFS/lex2.pdf
// O(m log m)
// pub fn perfect_matching_regular_bipartite(
//     n: usize,
//     k: usize,
//     edges: Vec<(usize, usize)>,
// ) -> Vec<(usize, usize)> {
//     #[derive(Clone, Copy)]
//     struct DncItem {
//         u: usize,
//         v: usize,
//         k: usize,
//         idx: isize,
//     }
//     assert!(k > 0);
//     let mut t = 0;
//     while (1 << t) < k * n {
//         t += 1;
//     }
//     let mut todnc: Vec<DncItem> = Vec::new();
//     let alph = (1 << t) / k;
//     let beta = (1 << t) - k * alph;
//     for (i, &(u, v)) in edges.iter().enumerate() {
//         todnc.push(DncItem {
//             u,
//             v: v + n,
//             k: alph,
//             idx: i as isize,
//         });
//     }
//     if beta > 0 {
//         for i in 0..n {
//             todnc.push(DncItem {
//                 u: i,
//                 v: i + n,
//                 k: beta,
//                 idx: -1,
//             });
//         }
//     }
//     for _ in 0..t {
//         let mut toeuler: Vec<(usize, usize)> = Vec::new();
//         for item in &todnc {
//             if item.k % 2 != 0 {
//                 toeuler.push((item.u, item.v - n));
//             }
//         }
//         let pth = split_euler_bipartite(2 * n, &toeuler);
//         let mut parity = vec![0; toeuler.len()];
//         for i in (1..pth.len()).step_by(2) {
//             parity[pth[i]] = 1;
//         }
//         let mut sub0: Vec<DncItem> = Vec::new();
//         let mut sub1: Vec<DncItem> = Vec::new();
//         let mut ptr = 0;
//         let mut bal = 0;
//         for item in &todnc {
//             let mut l = item.k / 2;
//             let mut r = item.k / 2;
//             if item.k % 2 != 0 {
//                 if parity[ptr] == 1 {
//                     r += 1;
//                 } else {
//                     l += 1;
//                 }
//                 ptr += 1;
//             }
//             if item.idx == -1 {
//                 bal += l as isize - r as isize;
//             }
//             if l > 0 {
//                 sub0.push(DncItem {
//                     u: item.u,
//                     v: item.v,
//                     k: l,
//                     idx: item.idx,
//                 });
//             }
//             if r > 0 {
//                 sub1.push(DncItem {
//                     u: item.u,
//                     v: item.v,
//                     k: r,
//                     idx: item.idx,
//                 });
//             }
//         }
//         if bal >= 0 {
//             todnc = sub1;
//         } else {
//             todnc = sub0;
//         }
//     }
//     let mut matching_edges = Vec::new();
//     for item in &todnc {
//         if item.idx != -1 {
//             matching_edges.push(edges[item.idx as usize]);
//         }
//     }
//     matching_edges
// }

pub struct BipartiteRegularMatching<F>
where
    F: Fn(usize) -> usize,
{
    n: usize,
    mtl: Vec<usize>,
    mtr: Vec<usize>,
    ord: Vec<usize>,
    path: Vec<(usize, usize)>,
    pos: Vec<usize>,
    sample_out: F,
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
    use rand::Rng;

    fn generate_regular_bipartite(n: usize, d: usize) -> Vec<Vec<usize>> {
        let mut adj = vec![vec![]; n];
        let mut rng = rand::thread_rng();
        for _ in 0..d {
            let mut p: Vec<usize> = (0..n).collect();
            p.shuffle(&mut rng);
            for (u, &v) in p.iter().enumerate() {
                adj[u].push(v);
            }
        }
        adj
    }

    fn verify_perfect_matching<F>(solver: &BipartiteRegularMatching<F>, adj: &[Vec<usize>])
    where
        F: Fn(usize) -> usize,
    {
        for u in 0..solver.n {
            let v_idx = solver.mtl[u];
            assert_ne!(v_idx, usize::MAX, "Node P[{}] is unmatched", u);
            let v = v_idx as usize;

            let u_back = solver.mtr[v];
            assert_eq!(
                u_back, u,
                "Inconsistent: P[{}]->Q[{}] but Q[{}]->P[{}]",
                u, v, v, u_back
            );
            assert!(adj[u].contains(&v), "Edge P[{}]-Q[{}] invalid", u, v);
        }
    }

    #[test]
    fn test_whp_correctness_stress() {
        for _ in 0..20 {
            let n = 50;
            let d = 4;
            let adj = generate_regular_bipartite(n, d);
            let sample_out = |u: usize| -> usize {
                let neighbors = &adj[u];
                neighbors[rand::thread_rng().gen_range(0..neighbors.len())]
            };

            let mut solver = BipartiteRegularMatching::new(n, &sample_out);
            solver.solve_whp();
            verify_perfect_matching(&solver, &adj);
        }
    }

    #[test]
    fn test_small_3_regular() {
        let n = 10;
        let d = 3;
        let adj = generate_regular_bipartite(n, d);

        let sample_out = |u: usize| -> usize {
            let neighbors = &adj[u];
            let idx = rand::thread_rng().gen_range(0..neighbors.len());
            neighbors[idx]
        };

        // Test Expected Time Algo
        let mut solver = BipartiteRegularMatching::new(n, &sample_out);
        solver.solve();
        verify_perfect_matching(&solver, &adj);

        // Test WHP Algo
        let mut solver2 = BipartiteRegularMatching::new(n, &sample_out);
        solver2.solve_whp();
        verify_perfect_matching(&solver2, &adj);
    }

    #[test]
    fn test_large_graph() {
        let n = 1000; // 1000 nodes on each side
        let d = 5;
        let adj = generate_regular_bipartite(n, d);

        let sample_out = |u: usize| -> usize {
            let neighbors = &adj[u];
            // Using fast randomness for loop
            neighbors[rand::thread_rng().gen_range(0..neighbors.len())]
        };

        let mut solver = BipartiteRegularMatching::new(n, &sample_out);
        solver.solve();
        verify_perfect_matching(&solver, &adj);
    }

    #[test]
    fn test_degree_1_trivial() {
        let n = 50;
        let d = 1;
        let adj = generate_regular_bipartite(n, d);

        let sample_out = |u: usize| -> usize { adj[u][0] };

        let mut solver = BipartiteRegularMatching::new(n, &sample_out);
        solver.solve_whp();
        verify_perfect_matching(&solver, &adj);
    }

    #[test]
    fn test_whp_correctness_stress_2() {
        // Run multiple times to ensure the probabilistic bounds hold (no infinite loops)
        for _ in 0..10 {
            let n = 50;
            let d = 4;
            let adj = generate_regular_bipartite(n, d);

            let sample_out = |u: usize| -> usize {
                let neighbors = &adj[u];
                neighbors[rand::thread_rng().gen_range(0..neighbors.len())]
            };

            let mut solver = BipartiteRegularMatching::new(n, &sample_out);
            solver.solve_whp();
            verify_perfect_matching(&solver, &adj);
        }
    }
}
