use bit_vec::BitVec;

pub fn blossom(n: usize, g: &[usize], d: &[usize]) -> (usize, Vec<usize>) {
    let mut n_matches = 0;
    let mut mate = vec![0; n + 1];
    let mut q = vec![0; n + 1];
    let mut book = BitVec::from_elem(n + 1, false);
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
    use crate::grph::representations::edges_to_csr_undir_one_based;

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
}
