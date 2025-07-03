use bit_vec::BitVec;

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

// Minimum vertex cover O(sqrt(|V|) |E|) with hopcroft-karp
// returns (in_cover_l, in_cover_r)
pub fn min_vertex_cover(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
    l: &[usize],
    r: &[usize],
) -> (BitVec, BitVec) {
    let (mut lfound, mut seen, mut q) = (
        BitVec::from_fn(n, |i| l[i] == usize::MAX),
        BitVec::from_elem(k, false),
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

// Minimum edge cover O(sqrt(|V|) |E|) with hopcroft-karp
// returns edges as (left_vertex, right_vertex) pairs
pub fn min_edge_cover(
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
    let mut right_cover = BitVec::from_elem(k, false);
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

// Maximum co-clique O(sqrt(|V|) |E|) with hopcroft-karp
// returns (in_coclique_l, in_coclique_r)
pub fn max_coclique(
    n: usize,
    k: usize,
    g: &[usize],
    d: &[usize],
    l: &[usize],
    r: &[usize],
) -> (BitVec, BitVec) {
    let (mut in_cover_l, mut in_cover_r) = min_vertex_cover(n, k, g, d, l, r);
    in_cover_l.negate();
    in_cover_r.negate();
    (in_cover_l, in_cover_r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grph::representations::edges_to_csr_undir;

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

    /// Collect the set bits of a BitVec into a sorted Vec<usize>.
    fn bv_to_vec(b: &BitVec) -> Vec<usize> {
        b.iter()
            .enumerate()
            .filter_map(|(i, bit)| if bit { Some(i) } else { None })
            .collect()
    }

    /// Verify that every edge (u,v) is covered by the union of cover_l ∪ cover_r.
    fn check_cover(edges: &[(usize, usize)], cover_l: &BitVec, cover_r: &BitVec) {
        for &(u, v) in edges {
            assert!(
                cover_l.get(u).unwrap_or(false) || cover_r.get(v).unwrap_or(false),
                "Edge ({},{}) not covered by L={:?} or R={:?}",
                u,
                v,
                bv_to_vec(cover_l),
                bv_to_vec(cover_r)
            );
        }
    }

    #[test]
    fn test_empty_graph() {
        let n = 3;
        let k = 4;
        let edges = &[];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(m, 0);
        let (cover_l, cover_r) = min_vertex_cover(n, k, &g, &d, &l, &r);
        assert!(bv_to_vec(&cover_l).is_empty(), "expected no left cover");
        assert!(bv_to_vec(&cover_r).is_empty(), "expected no right cover");
        let (anticl_l, anticl_r) = max_coclique(n, k, &g, &d, &l, &r);
        // On empty graph, anticlique == all vertices
        assert_eq!(bv_to_vec(&anticl_l), (0..n).collect::<Vec<_>>());
        assert_eq!(bv_to_vec(&anticl_r), (0..k).collect::<Vec<_>>());
    }

    #[test]
    fn test_single_edge() {
        let n = 1;
        let k = 1;
        let edges = &[(0, 0)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(m, 1);

        let (cover_l, cover_r) = min_vertex_cover(n, k, &g, &d, &l, &r);
        assert_eq!(bv_to_vec(&cover_l), vec![0]);
        assert!(bv_to_vec(&cover_r).is_empty());
        check_cover(edges, &cover_l, &cover_r);

        let (anticl_l, anticl_r) = max_coclique(n, k, &g, &d, &l, &r);
        // anticlique picks the opposite endpoint
        assert!(bv_to_vec(&anticl_l).is_empty());
        assert_eq!(bv_to_vec(&anticl_r), vec![0]);
    }

    #[test]
    fn test_star_graph_min_vertex_cover() {
        // Left 0→Right 0 and Left 1→Right 0
        let n = 2;
        let k = 1;
        let edges = &[(0, 0), (1, 0)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(m, 1);

        let (cover_l, cover_r) = min_vertex_cover(n, k, &g, &d, &l, &r);
        assert!(bv_to_vec(&cover_l).is_empty());
        assert_eq!(bv_to_vec(&cover_r), vec![0]);
        check_cover(edges, &cover_l, &cover_r);

        let (anticl_l, anticl_r) = max_coclique(n, k, &g, &d, &l, &r);
        // anticlique is everything except the cover
        assert_eq!(bv_to_vec(&anticl_l), vec![0, 1]);
        assert!(bv_to_vec(&anticl_r).is_empty());
    }

    #[test]
    fn test_complete_bipartite_2x2() {
        // K_{2,2}
        let n = 2;
        let k = 2;
        let edges = &[(0, 0), (0, 1), (1, 0), (1, 1)];
        let (g, d) = build_csr(n, edges);
        let (m, l, r) = hopcroft_karp(n, k, &g, &d);
        assert_eq!(m, 2);

        let (cover_l, cover_r) = min_vertex_cover(n, k, &g, &d, &l, &r);
        // in K_{2,2} with perfect matching, no free left => cover is all left
        assert_eq!(bv_to_vec(&cover_l), vec![0, 1]);
        assert!(bv_to_vec(&cover_r).is_empty());
        check_cover(edges, &cover_l, &cover_r);

        let (anticl_l, anticl_r) = max_coclique(n, k, &g, &d, &l, &r);
        // anticlique is the complement of the cover
        assert!(bv_to_vec(&anticl_l).is_empty());
        assert_eq!(bv_to_vec(&anticl_r), vec![0, 1]);
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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);
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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

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
        let cover = min_edge_cover(n, k, &g, &d, &l, &r, m);

        assert!(check_edge_cover(n, k, edges, &cover));
        assert_eq!(cover.len(), brute_force_min_edge_cover(n, k, edges));
        // Perfect matching with 4 isolated edges
        assert_eq!(cover.len(), 4);
    }
}
