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

// https://www.tau.ac.il/~nogaa/PDFS/lex2.pdf
/// O(m log m)
pub fn edge_color_bipartite(n1: usize, n2: usize, edges: Vec<(usize, usize)>) -> Vec<usize> {
    #[derive(Clone)]
    struct RegularGraph {
        n: usize,
        k: usize,
        edges: Vec<(usize, usize)>,
    }
    fn regularize(n1: usize, n2: usize, edges: Vec<(usize, usize)>) -> RegularGraph {
        let (mut deg1, mut deg2) = (vec![0; n1], vec![0; n2]);
        for &(u, v) in &edges {
            deg1[u] += 1;
            deg2[v] += 1;
        }
        let k = deg1
            .iter()
            .max()
            .copied()
            .unwrap_or(0)
            .max(deg2.iter().max().copied().unwrap_or(0));
        let (mut map1, mut map2) = (vec![0; n1], vec![0; n2]);
        let (mut idx1, mut idx2) = (vec![0; n1.max(n2)], vec![0; n1.max(n2)]);
        let build_map = |n: usize, deg: &Vec<usize>, map: &mut Vec<usize>, idx: &mut Vec<usize>| {
            if n == 0 {
                return;
            }
            idx[0] += deg[0];
            for i in 1..n {
                map[i] = map[i - 1];
                if idx[map[i]] + deg[i] > k {
                    map[i] += 1;
                }
                idx[map[i]] += deg[i];
            }
        };
        build_map(n1, &deg1, &mut map1, &mut idx1);
        build_map(n2, &deg2, &mut map2, &mut idx2);
        let n = if n1 == 0 && n2 == 0 {
            0
        } else {
            (map1.last().unwrap_or(&0) + 1).max(map2.last().unwrap_or(&0) + 1)
        };
        let mut res = RegularGraph {
            n,
            k,
            edges: vec![(0, 0); n * k],
        };
        for (i, &(u, v)) in edges.iter().enumerate() {
            res.edges[i] = (map1[u], map2[v]);
        }
        let (mut s1, mut s2) = (0, 0);
        for i in edges.len()..n * k {
            while s1 < n && idx1[s1] == k {
                s1 += 1;
            }
            while s2 < n && idx2[s2] == k {
                s2 += 1;
            }
            res.edges[i] = (s1, s2);
            idx1[s1] += 1;
            idx2[s2] += 1;
        }
        res
    }
    struct Solver {
        n: usize,
        k: usize,
        inci: Vec<usize>,
        xedge: Vec<usize>,
        flag: Vec<usize>,
        nx: usize,
    }
    impl Solver {
        fn new(g: &RegularGraph) -> Self {
            let (n, k, m) = (g.n * 2, g.k, g.n * g.k);
            let (mut inci, mut xedge, mut head) = (vec![0; n * k], vec![0; m], vec![0; n]);
            for (e, &(u, v)) in g.edges.iter().enumerate() {
                let (u, v) = (u * 2, v * 2 + 1);
                inci[k * u + head[u]] = e;
                head[u] += 1;
                inci[k * v + head[v]] = e;
                head[v] += 1;
                xedge[e] = u ^ v;
            }
            Self {
                n,
                k,
                inci,
                xedge,
                flag: vec![0; m],
                nx: 0,
            }
        }

        fn split(&mut self, mut pl: Vec<usize>, mut pr: Vec<usize>) -> Vec<usize> {
            self.nx += 1;
            for sp in 0..self.n {
                let mut v = sp;
                loop {
                    if pl[v] == pr[v] {
                        if sp == v {
                            break;
                        }
                        v ^= 1;
                        continue;
                    }
                    let e = self.inci[pl[v]];
                    pl[v] += 1;
                    let mut w = v;
                    if self.flag[e] != self.nx {
                        self.flag[e] = self.nx;
                        w = v ^ self.xedge[e];
                    }
                    if w % 2 == 0 {
                        pl[v] -= 1;
                        pr[v] -= 1;
                        self.inci.swap(pl[v], pr[v]);
                    }
                    v = w;
                }
            }
            pl
        }

        fn swap_grp(&mut self, el: &[usize], em: &mut [usize], er: &[usize]) {
            for i in 0..self.n {
                let len = (em[i] - el[i]).min(er[i] - em[i]);
                for k in 0..len {
                    self.inci.swap(el[i] + k, er[i] - len + k);
                }
                em[i] = er[i] + el[i] - em[i];
            }
        }

        fn take(&mut self, s: usize, d: usize) {
            let (mut pl, mut pr) = (vec![0; self.n], vec![0; self.n]);
            for i in 0..self.n {
                pl[i] = i * self.k + s;
                pr[i] = i * self.k + s + d;
            }
            let mut pm = pr.clone();
            let limit = (self.n / 2) * d;
            let mut md = 1;
            while md < limit {
                md *= 2;
            }
            let mut alpha = md / d;
            while alpha > 0 && alpha % 2 == 0 {
                alpha /= 2;
                md /= 2;
            }
            let mut w = 1;
            while w < md {
                if (alpha & w) != 0 {
                    let mut plm = self.split(pl.clone(), pm.clone());
                    let cnt: isize = (0..self.n)
                        .step_by(2)
                        .map(|i| (pm[i] + pl[i]) as isize - plm[i] as isize * 2)
                        .sum();
                    if cnt < 0 {
                        self.swap_grp(&pl, &mut plm, &pm);
                    }
                    pm = plm;
                } else {
                    let mut pmr = self.split(pm.clone(), pr.clone());
                    let cnt: isize = (0..self.n)
                        .step_by(2)
                        .map(|i| (pr[i] + pm[i]) as isize - pmr[i] as isize * 2)
                        .sum();
                    if cnt < 0 {
                        self.swap_grp(&pm, &mut pmr, &pr);
                    }
                    pm = pmr;
                }
                w *= 2;
            }
        }

        fn recurse(&mut self, s: usize, mut d: usize) {
            if d <= 1 {
                return;
            } else if d % 2 == 1 {
                if s + d < self.k {
                    d += 1;
                } else {
                    self.take(s, d);
                    d -= 1;
                }
            }
            self.split(
                (0..self.n).map(|i| i * self.k + s).collect(),
                (0..self.n).map(|i| i * self.k + s + d).collect(),
            );
            self.recurse(s + d / 2, d / 2);
            self.recurse(s, d / 2);
        }
    }
    if edges.is_empty() {
        return vec![];
    }
    let m_orig = edges.len();
    let g = regularize(n1, n2, edges);
    let mut s = Solver::new(&g);
    s.recurse(0, g.k);
    let mut ans = vec![0; m_orig];
    for i in (0..s.n).step_by(2) {
        for j in 0..g.k {
            let e = s.inci[i * g.k + j];
            if e < m_orig {
                ans[e] = j;
            }
        }
    }
    ans
}
