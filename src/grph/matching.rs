use crate::ds::bit_vec::BitVec;

// Hopcroft-Karp maximum bipartite matching O(sqrt(|V|) |E|)
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

// TODO: hungarian algorithm
// https://judge.yosupo.jp/submission/219195
// https://codeforces.com/blog/entry/128703
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

#[cfg(test)]
mod tests {
    use super::blossom;
    use crate::grph::format::edges_to_csr_undir_one_based;
    use crate::grph::matching::BitVec;

    /// No edges ⇒ no matches
    #[test]
    fn test_no_edges() {
        let n = 3;
        let edges: Vec<[usize; 2]> = Vec::new();
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 0);
        // all vertices 1..n should remain unmatched (mate[u] == 0)
        for u in 1..=n {
            assert_eq!(mate[u], 0);
        }
    }

    /// Single edge 1–2 ⇒ one match
    #[test]
    fn test_single_edge() {
        let n = 2;
        let edges = vec![[1, 2], [2, 1]];
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 1);
        assert_eq!(mate[1], 2);
        assert_eq!(mate[2], 1);
    }

    /// Path 1–2–3 ⇒ at most one match
    #[test]
    fn test_path_three_nodes() {
        let n = 3;
        let edges = vec![[1, 2], [2, 1], [2, 3], [3, 2]];
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 1);
        let matched: Vec<_> = (1..=n).filter(|&u| mate[u] != 0).collect();
        assert_eq!(matched.len(), 2);
        for &u in &matched {
            let v = mate[u];
            assert_eq!(mate[v], u);
        }
    }

    /// Triangle 1–2–3–1 ⇒ matching size 1
    #[test]
    fn test_triangle() {
        let n = 3;
        let edges = vec![[1, 2], [2, 1], [2, 3], [3, 2], [3, 1], [1, 3]];
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 1);
        let matched: Vec<_> = (1..=n).filter(|&u| mate[u] != 0).collect();
        assert_eq!(matched.len(), 2);
    }

    /// 4-cycle 1–2–3–4–1 ⇒ perfect matching of size 2
    #[test]
    fn test_cycle4() {
        let n = 4;
        let edges = vec![
            [1, 2],
            [2, 1],
            [2, 3],
            [3, 2],
            [3, 4],
            [4, 3],
            [4, 1],
            [1, 4],
        ];
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 2);
        for u in 1..=n {
            if mate[u] != 0 {
                assert_eq!(mate[mate[u]], u);
            }
        }
    }

    /// 5-cycle (odd) ⇒ max matching size 2
    #[test]
    fn test_cycle5() {
        let n = 5;
        let mut edges = Vec::new();
        for i in 1..=5 {
            let j = if i < 5 { i + 1 } else { 1 };
            edges.push([i, j]);
            edges.push([j, i]);
        }
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 2);
        let matched: Vec<_> = (1..=n).filter(|&u| mate[u] != 0).collect();
        assert_eq!(matched.len(), 4);
    }

    /// Complete bipartite K₃,₃ ⇒ perfect matching of size 3
    #[test]
    fn test_k3_3() {
        let n = 6;
        let left = [1, 2, 3];
        let right = [4, 5, 6];
        let mut edges = Vec::new();
        for &u in &left {
            for &v in &right {
                edges.push([u, v]);
                edges.push([v, u]);
            }
        }
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 3);
        for u in 1..=n {
            if mate[u] != 0 {
                let v = mate[u];
                assert!(
                    (u <= 3 && v >= 4) || (u >= 4 && v <= 3),
                    "edge {:?}-{:?} is not across the bipartition",
                    u,
                    v
                );
                assert_eq!(mate[v], u);
            }
        }
    }

    /// Two nested odd cycles sharing node 1
    #[test]
    fn test_two_nested_odd_cycles() {
        let n = 15;
        let mut edges = Vec::new();
        // Cycle A: 1..7
        for i in 1..=7 {
            let j = if i < 7 { i + 1 } else { 1 };
            edges.push([i, j]);
            edges.push([j, i]);
        }
        // Cycle B: [1,8..15]
        let mut cycle_b = vec![1];
        cycle_b.extend(8..=15);
        for w in cycle_b.windows(2) {
            edges.push([w[0], w[1]]);
            edges.push([w[1], w[0]]);
        }
        // close B
        let last = *cycle_b.last().unwrap();
        edges.push([last, 1]);
        edges.push([1, last]);

        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, 3 + 4);
        for u in 1..=n {
            if mate[u] != 0 {
                assert_eq!(mate[mate[u]], u);
            }
        }
    }

    /// Chain of three odd cycles
    #[test]
    fn test_chain_three_odd_cycles() {
        let size_a = 5;
        let size_b = 7;
        let size_c = 9;
        let n = size_a + (size_b - 1) + (size_c - 1);
        let mut edges = Vec::new();
        // A: 1..5
        for i in 1..=size_a {
            let j = if i < size_a { i + 1 } else { 1 };
            edges.push([i, j]);
            edges.push([j, i]);
        }
        // B attach at 2
        let attach_b = 2;
        let start_b = size_a + 1;
        let mut cycle_b = vec![attach_b];
        cycle_b.extend(start_b..start_b + (size_b - 1));
        for w in cycle_b.windows(2) {
            edges.push([w[0], w[1]]);
            edges.push([w[1], w[0]]);
        }
        // close B
        let last_b = *cycle_b.last().unwrap();
        edges.push([last_b, attach_b]);
        edges.push([attach_b, last_b]);
        // C attach at cycle_b[1]
        let attach_c = cycle_b[1];
        let start_c = start_b + (size_b - 1);
        let mut cycle_c = vec![attach_c];
        cycle_c.extend(start_c..start_c + (size_c - 1));
        for w in cycle_c.windows(2) {
            edges.push([w[0], w[1]]);
            edges.push([w[1], w[0]]);
        }
        // close C
        let last_c = *cycle_c.last().unwrap();
        edges.push([last_c, attach_c]);
        edges.push([attach_c, last_c]);

        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, size_a / 2 + size_b / 2 + size_c / 2);
        for u in 1..=n {
            if mate[u] != 0 {
                assert_eq!(mate[mate[u]], u);
            }
        }
    }

    /// Many disconnected odd cycles
    #[test]
    fn test_many_disconnected_odd_cycles() {
        let lengths = [3, 5, 7, 9, 11];
        let n: usize = lengths.iter().sum();
        let mut edges = Vec::new();
        let mut offset = 1;
        let mut expected = 0;
        for &len in &lengths {
            for i in 0..len {
                let u = offset + i;
                let v = offset + (i + 1) % len;
                edges.push([u, v]);
                edges.push([v, u]);
            }
            expected += len / 2;
            offset += len;
        }
        let (g, d) = edges_to_csr_undir_one_based(n, &edges);
        let (n_matches, mate) = blossom(n, &g, &d);
        assert_eq!(n_matches, expected);
        for u in 1..=n {
            if mate[u] != 0 {
                assert_eq!(mate[mate[u]], u);
            }
        }
    }

    /// Reuse with edge addition (fresh calls)
    #[test]
    fn test_reuse_with_edge_addition() {
        let n = 5;
        // initial triangle on {1,2,3}
        let mut triangle = vec![[1, 2], [2, 1], [2, 3], [3, 2], [3, 1], [1, 3]];
        let (g1, d1) = edges_to_csr_undir_one_based(n, &triangle);
        let (m1, mate1) = blossom(n, &g1, &d1);
        assert_eq!(m1, 1);
        let (u0, v0) = (1..=3)
            .find_map(|u| (mate1[u] != 0).then(|| (u, mate1[u])))
            .expect("one match in triangle");
        assert_eq!(mate1[u0], v0);
        assert_eq!(mate1[v0], u0);

        // now add edge 4–5
        triangle.push([4, 5]);
        triangle.push([5, 4]);
        let (g2, d2) = edges_to_csr_undir_one_based(n, &triangle);
        let (m2, mate2) = blossom(n, &g2, &d2);
        assert_eq!(m2, 2);
        assert_eq!(mate2[4], 5);
        assert_eq!(mate2[5], 4);
        assert_eq!(mate2[u0], v0);
        assert_eq!(mate2[v0], u0);
    }

    use crate::grph::format::edges_to_csr_undir;
    use crate::grph::matching::hopcroft_karp;
    use crate::grph::matching::max_coclique_bipartite;
    use crate::grph::matching::min_edge_cover_bipartite;
    use crate::grph::matching::min_vertex_cover_bipartite;

    /// Brute-force maximum matching size on bipartite graph
    fn brute_force(n: usize, k: usize, edges: &[[usize; 2]]) -> usize {
        let e = edges.len();
        let mut best = 0;
        for mask in 0..(1_usize << e) {
            let cnt = mask.count_ones() as usize;
            if cnt <= best {
                continue;
            }
            let mut ul = vec![false; n];
            let mut ur = vec![false; k];
            let mut ok = true;
            for i in 0..e {
                if (mask >> i) & 1 == 1 {
                    let [u, v] = edges[i];
                    if ul[u] || ur[v] {
                        ok = false;
                        break;
                    }
                    ul[u] = true;
                    ur[v] = true;
                }
            }
            if ok {
                best = cnt;
            }
        }
        best
    }

    #[test]
    fn test_complete_small() {
        let n = 6;
        let k = 6;
        let mut edges = Vec::new();
        for u in 0..n {
            for v in 0..k {
                edges.push([u, v]);
            }
        }
        let (g, d) = edges_to_csr_undir(n, &edges);
        let (ans, _, _) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(ans, 6);
    }

    #[test]
    fn test_cycle_graph() {
        let n = 7;
        let k = 7;
        let mut edges = Vec::new();
        for i in 0..n {
            edges.push([i, i]);
            edges.push([i, (i + 1) % k]);
        }
        let expected = brute_force(n, k, &edges);
        let (g, d) = edges_to_csr_undir(n, &edges);
        let (ans, _, _) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(ans, expected);
    }

    #[test]
    fn test_random_small() {
        let n = 6;
        let k = 6;
        let edges: Vec<_> = (0..n)
            .flat_map(|u| (0..k).map(move |v| [u, v]))
            .filter(|_| rand::random::<f64>() < 0.5)
            .collect();
        let expected = brute_force(n, k, &edges);
        let (g, d) = edges_to_csr_undir(n, &edges);
        let (ans, _, _) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(ans, expected);
    }

    #[test]
    fn test_star_graph() {
        let n = 5;
        let k = 10;
        let edges: Vec<_> = (0..k).map(|v| [0, v]).collect();
        let expected = brute_force(n, k, &edges);
        let (g, d) = edges_to_csr_undir(n, &edges);
        let (ans, l, r) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(ans, expected);
        // verify matching vectors
        assert_eq!(l[0], r.iter().position(|&u| u == 0).unwrap());
    }

    #[test]
    fn test_disjoint_unions() {
        let n = 6;
        let k = 6;
        let mut edges = Vec::new();
        for &base in &[0, 3] {
            for u in base..base + 3 {
                for v in 0..3 {
                    edges.push([u, v + base]);
                }
            }
        }
        let expected = brute_force(n, k, &edges);
        let (g, d) = edges_to_csr_undir(n, &edges);
        let (ans, _, _) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(ans, expected);
    }

    /// Build CSR representation of a bipartite graph with `n` left vertices.
    fn build_csr(n: usize, edges: &[(usize, usize)]) -> (Vec<usize>, Vec<usize>) {
        let mut d = vec![0; n + 1];
        for &(u, _) in edges {
            d[u + 1] += 1;
        }
        for i in 1..=n {
            d[i] += d[i - 1];
        }
        let mut g = vec![0; edges.len()];
        let mut next = d.clone();
        for &(u, v) in edges {
            g[next[u]] = v;
            next[u] += 1;
        }
        (g, d)
    }

    /// Check if edge cover is valid (covers all vertices)
    fn check_edge_cover(
        n: usize,
        k: usize,
        edges: &[(usize, usize)],
        cover: &[(usize, usize)],
    ) -> bool {
        let mut left_covered = vec![false; n];
        let mut right_covered = vec![false; k];

        // Check all cover edges are valid
        for &(u, v) in cover {
            if !edges.contains(&(u, v)) {
                return false;
            }
            left_covered[u] = true;
            right_covered[v] = true;
        }

        // Check all vertices are covered
        left_covered.iter().all(|&x| x) && right_covered.iter().all(|&x| x)
    }

    /// Brute force minimum edge cover size
    fn brute_force_min_edge_cover(n: usize, k: usize, edges: &[(usize, usize)]) -> usize {
        let e = edges.len();
        let mut best = usize::MAX;

        for mask in 0..(1_usize << e) {
            let cnt = mask.count_ones() as usize;
            if cnt >= best {
                continue;
            }

            let selected_edges: Vec<_> = edges
                .iter()
                .enumerate()
                .filter(|(i, _)| (mask >> i) & 1 == 1)
                .map(|(_, &edge)| edge)
                .collect();

            if check_edge_cover(n, k, edges, &selected_edges) {
                best = cnt;
            }
        }

        best
    }

    #[test]
    fn test_empty_graph_min_edge_cover() {
        let n = 2;
        let k = 2;
        let edges = &[];
        let (g, d) = build_csr(n, edges);
        // Empty graph has no edges, so no edge cover possible
        // This test mainly checks the function doesn't panic
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);
        // Should return empty cover for empty graph
        assert!(cover.is_empty());
    }

    #[test]
    fn test_single_edge_min_edge_cover() {
        let n = 1;
        let k = 1;
        let edges = &[(0, 0)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert_eq!(cover.len(), 1);
        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
    }

    #[test]
    fn test_star_graph_min_edge_cover() {
        let n = 3;
        let k = 1;
        let edges = &[(0, 0), (1, 0), (2, 0)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // Star with 3 left, 1 right should need 3 edges (one matching + 2 for unmatched)
        assert_eq!(cover.len(), 3);
    }

    #[test]
    fn test_complete_bipartite_2x2_min_edge_cover() {
        let n = 2;
        let k = 2;
        let edges = &[(0, 0), (0, 1), (1, 0), (1, 1)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // K_{2,2} with perfect matching should need exactly 2 edges
        assert_eq!(cover.len(), 2);
    }

    #[test]
    fn test_path_graph() {
        let n = 3;
        let k = 3;
        let edges = &[(0, 0), (1, 1), (2, 2)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // Perfect matching case should need exactly 3 edges
        assert_eq!(cover.len(), 3);
    }

    #[test]
    fn test_unbalanced_graph() {
        let n = 1;
        let k = 3;
        let edges = &[(0, 0), (0, 1), (0, 2)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // 1 left, 3 right: need 1 matching edge + 2 for unmatched right = 3 total
        assert_eq!(cover.len(), 3);
    }

    #[test]
    fn test_disconnected_components() {
        let n = 4;
        let k = 4;
        let edges = &[(0, 0), (1, 1), (2, 2), (3, 3)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        let cover = min_edge_cover_bipartite(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // Perfect matching with 4 isolated edges
        assert_eq!(cover.len(), 4);
    }
}
