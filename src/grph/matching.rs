use crate::alg::fps::Poly;
use crate::alg::ops::inv;
use crate::ds::bit_vec::BitVec;
use crate::tree::top::StaticTopTree;

/// O(√V E)
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
pub fn dulmage_mendelsohn(n: usize, k: usize, g: &[usize], d: &[usize]) -> Vec<i32> {
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
    let mut comp: Vec<i32> = vec![0; t];
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

// TODO: hungarian algorithm
// https://judge.yosupo.jp/submission/219195
// https://codeforces.com/blog/entry/128703
// https://maspypy.github.io/library/flow/hungarian.hpp
pub fn hungarian() {}

/// O(n^3)
pub fn blossom(n: usize, g: &[usize], d: &[usize]) -> (usize, Vec<usize>) {
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
    (n_matches, mate)
}

// TODO: weighted blossom
// https://judge.yosupo.jp/submission/295392

// TODO: O(m √n log ?) maximum matching
// https://arxiv.org/pdf/1703.03998
// https://judge.yosupo.jp/submission/51928

// TODO: stable matching
// https://maspypy.github.io/library/graph/stable_matching.hpp

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
    type State<const M: u64> = [[Poly<M>; 2]; 2];
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
        s[0][0] = Poly::new(vec![1]);
        s
    };
    let result: Path<M> = stt.calc::<Path<M>, Point<M>>(
        |_| -> Path<M> {
            let mut p = Path::default();
            p.single = true;
            p.s[0][0] = Poly::new(vec![1]);
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
            let sum_all: Poly<M> = (0..2)
                .flat_map(|a| (0..2).map(move |b| (a, b)))
                .fold(Poly::default(), |acc, (a, b)| acc + &p.s[a][b]);
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
    let mut ans = Poly::<M>::default();
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
