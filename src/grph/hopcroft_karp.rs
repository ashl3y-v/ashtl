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
                        let nyy = l[uu];
                        l[uu] = vv;
                        vv = nyy;
                        uu = fa[uu];
                    }
                    matched = true;
                    size += 1;
                    break;
                }
                let ry = r[v] as usize;
                if fa[ry] == usize::MAX {
                    q[q_n] = ry;
                    fa[ry] = u;
                    rt[ry] = rt[u];
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
}
