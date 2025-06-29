use bit_vec::BitVec;

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
    use super::super::hopcroft_karp::hopcroft_karp;
    use super::*;
    use bit_vec::BitVec;

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
    fn test_star_graph() {
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
}
