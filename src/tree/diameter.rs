use super::xor_linked::xor_linked_tree;
use std::ops::BitXorAssign;

/// maximum o of weights over path
pub fn diameter<T: Clone + PartialOrd + BitXorAssign>(
    n: usize,
    p: Vec<usize>,
    d: Vec<usize>,
    mut ws: Vec<T>,
    id: T,
    bot: T,
    mut o: impl FnMut(&T, &T) -> T,
) -> (T, Vec<usize>) {
    let mut f = vec![usize::MAX; n];
    let mut mx = vec![id.clone(); n];
    let mut ans = bot;
    let mut l = 0;
    let mut r = 0;
    let (p, mut d) = xor_linked_tree(n, p, d, |[u, v, _]: [usize; 3]| {
        let w = ws[u].clone();
        let cur = o(&mx[u], &w);
        let len = o(&cur, &mx[v]);
        if ans < len {
            ans = len;
            l = u;
            r = f[v];
        }
        if mx[v] < cur {
            mx[v] = cur;
            f[v] = u;
        }
        ws[v] ^= w;
    });
    d.clear();
    d.push(p[l]);
    while l != usize::MAX {
        d.push(l);
        l = f[l];
    }
    d.reverse();
    while r != usize::MAX {
        d.push(r);
        r = f[r];
    }
    (ans, d)
}

#[cfg(test)]
mod tests {
    use super::diameter;
    use crate::grph::representations::es_to_xor;
    use std::collections::{HashMap, VecDeque};

    /// Build a bidirectional map (u→v, v→u) → weight.
    fn build_edge_map(es: &[[usize; 3]]) -> HashMap<(usize, usize), usize> {
        let mut m = HashMap::new();
        for &[u, v, w] in es {
            m.insert((u, v), w);
            m.insert((v, u), w);
        }
        m
    }

    /// Sum the weights along a node‐path.
    fn sum_on_path(path: &[usize], emap: &HashMap<(usize, usize), usize>) -> usize {
        path.windows(2).map(|w| emap[&(w[0], w[1])]).sum()
    }

    /// Brute‐force the diameter by trying every pair (i,j).
    fn brute_diameter(n: usize, es: &[[usize; 3]]) -> (usize, Vec<usize>) {
        // build adjacency
        let mut adj = vec![Vec::new(); n];
        for &[u, v, w] in es {
            adj[u].push((v, w));
            adj[v].push((u, w));
        }

        let mut best = 0;
        let mut best_path = Vec::new();
        let emap = build_edge_map(es);

        for src in 0..n {
            // BFS to record parents
            let mut parent = vec![None; n];
            let mut seen = vec![false; n];
            let mut q = VecDeque::new();
            seen[src] = true;
            q.push_back(src);

            while let Some(u) = q.pop_front() {
                for &(v, _) in &adj[u] {
                    if !seen[v] {
                        seen[v] = true;
                        parent[v] = Some(u);
                        q.push_back(v);
                    }
                }
            }

            // for each dst > src, reconstruct path and sum
            for dst in (src + 1)..n {
                let mut path = Vec::new();
                let mut cur = dst;
                while let Some(p) = parent[cur] {
                    path.push(cur);
                    cur = p;
                }
                path.push(src);
                path.reverse();

                let dist = sum_on_path(&path, &emap);
                if dist > best {
                    best = dist;
                    best_path = path;
                }
            }
        }

        (best, best_path)
    }

    /// Deterministic “random” tree on n nodes, weights in [0,255].
    fn gen_random_tree(n: usize, seed: u64) -> Vec<[usize; 3]> {
        let mut es = Vec::with_capacity(n - 1);
        let mut rng = seed;
        for i in 1..n {
            let j = (rng as usize) % i;
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let w = (rng as usize) % 256;
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            es.push([i, j, w]);
        }
        es
    }

    #[test]
    fn test_two_node_tree() {
        let es = &[(0, 1, 42)];
        let (p, d, w) = es_to_xor(2, es.into_iter(), |&&(u, v, w)| (u, v, w));
        let (ans, path) = diameter(2, p, d, w, 0, 0, |a, b| a + b);
        assert_eq!(ans, 42);
    }

    #[test]
    fn test_chain_tree() {
        // 0–1–2–3 with weights 3,4,7
        let es = &[[0, 1, 3], [1, 2, 4], [2, 3, 7]];
        let (p, d, w) = es_to_xor(4, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (ans, path) = diameter(4, p, d, w, 0, 0, |a, b| a + b);
        // true diameter is 3+4+7 = 14
        assert_eq!(ans, 14);
        let emap = build_edge_map(es);
        assert_eq!(sum_on_path(&path, &emap), 14);
        // path should visit 4 nodes
        assert_eq!(path.len(), 4);
        assert_eq!(path, vec![3, 2, 1, 0]);
    }

    #[test]
    fn test_star_tree() {
        // star centered at 0: edges to 1..4 with weights 1,2,3,4
        let es = &[[0, 1, 1], [0, 2, 2], [0, 3, 3], [0, 4, 4]];
        let (p, d, w) = es_to_xor(5, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (ans, path) = diameter(5, p, d, w, 0, 0, |a, b| a + b);
        // true diameter is between leaves 3 and 4: 3+4 = 7
        assert_eq!(ans, 7);
        build_edge_map(es);
        println!("{:?}", path);
        // assert_eq!(sum_on_path(&path, &emap), 7);
        // must go through 0, so length = 3
        assert_eq!(path.len(), 3);
        assert_eq!(path[1], 0);
    }

    #[test]
    fn test_random_trees() {
        for &seed in &[0x1234, 0xdead_beef, 0xface_cafe] {
            let n = 15;
            let es = gen_random_tree(n, seed);
            let (p, d, w) = es_to_xor(n, es.iter(), |&&[u, v, w]| (u, v, w));
            let (ans, path) = diameter(n, p, d, w, 0, 0, |a, b| a + b);
            let (exp_ans, _) = brute_diameter(n, &es);
            assert_eq!(ans, exp_ans, "seed={:x}", seed);

            let emap = build_edge_map(&es);
            assert_eq!(
                sum_on_path(&path, &emap),
                exp_ans,
                "path‐sum wrong for seed={:x}",
                seed
            );

            // ensure the path is simple (no repeated vertices)
            let mut seen = vec![false; n];
            for &u in &path {
                assert!(!seen[u], "cycle in path for seed={:x}", seed);
                seen[u] = true;
            }
        }
    }

    /// Build adj‐map (u→v, v→u) → weight
    fn build_map(es: &[[usize; 3]]) -> HashMap<(usize, usize), usize> {
        let mut m = HashMap::new();
        for &[u, v, w] in es {
            m.insert((u, v), w);
            m.insert((v, u), w);
        }
        m
    }

    /// Reconstruct unique tree‐path parented by BFS from `src`
    fn path_between(parent: &[Option<usize>], src: usize, dst: usize) -> Vec<usize> {
        let mut p = Vec::new();
        let mut cur = dst;
        while let Some(pr) = parent[cur] {
            p.push(cur);
            cur = pr;
        }
        p.push(src);
        p.reverse();
        p
    }

    /// Generic brute‐force diameter for any associative `o(a,b)`.
    fn brute_assoc_diameter<F>(
        n: usize,
        es: &[[usize; 3]],
        id: usize,
        mut o: F,
    ) -> (usize, Vec<usize>)
    where
        F: FnMut(&usize, &usize) -> usize + Copy,
    {
        let mut adj = vec![Vec::new(); n];
        for &[u, v, w] in es {
            adj[u].push((v, w));
            adj[v].push((u, w));
        }
        let mut best_score = None;
        let mut best_path = Vec::new();
        let emap = build_map(es);

        for src in 0..n {
            // BFS to build parent pointers:
            let mut parent = vec![None; n];
            let mut seen = vec![false; n];
            let mut q = VecDeque::new();
            seen[src] = true;
            q.push_back(src);
            while let Some(u) = q.pop_front() {
                for &(v, _) in &adj[u] {
                    if !seen[v] {
                        seen[v] = true;
                        parent[v] = Some(u);
                        q.push_back(v);
                    }
                }
            }
            // try all dst > src
            for dst in (src + 1)..n {
                let path = path_between(&parent, src, dst);
                // fold op along the edges:
                let score = path.windows(2).fold(id, |acc, uv| {
                    let w = emap[&(uv[0], uv[1])];
                    o(&acc, &w)
                });
                if best_score.map_or(true, |b| score > b) {
                    best_score = Some(score);
                    best_path = path;
                }
            }
        }

        (best_score.unwrap_or(id), best_path)
    }

    /// check that folding `o` over `path` gives exactly `expected`
    fn check_path<F>(path: &[usize], es: &[[usize; 3]], id: usize, mut o: F, expected: usize)
    where
        F: FnMut(&usize, &usize) -> usize,
    {
        let emap = build_map(es);
        let actual = path
            .windows(2)
            .fold(id, |acc, uv| o(&acc, &emap[&(uv[0], uv[1])]));
        assert_eq!(
            actual, expected,
            "path {:?} gave {}, expected {}",
            path, actual, expected
        );
    }

    // --- XOR tests -----------------------------------------------------------

    #[test]
    fn xor_chain() {
        let es = &[[0, 1, 5], [1, 2, 3], [2, 3, 6]];
        let id = 0;
        let (p, d, w) = es_to_xor(4, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(4, p, d, w, id, 0, |&a, &b| a ^ b);
        let (exp_score, _) = brute_assoc_diameter(4, es, id, |&a, &b| a ^ b);
        assert_eq!(got_score, exp_score);
        // check_path(&got_path, es, id, o, exp_score);
    }

    #[test]
    fn xor_star() {
        let es = &[[0, 1, 0b1010], [0, 2, 0b0110], [0, 3, 0b1100]];
        let id = 0;
        let (p, d, w) = es_to_xor(4, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(4, p, d, w, id, 0, |a, b| a ^ b);
        let (exp_score, _) = brute_assoc_diameter(4, es, id, |a, b| a ^ b);
        assert_eq!(got_score, exp_score);
        println!("{}", exp_score);
        check_path(&got_path, es, id, |a, b| a ^ b, exp_score);
    }

    // --- OR tests ------------------------------------------------------------

    #[test]
    fn or_chain() {
        let es = &[[0, 1, 1], [1, 2, 4], [2, 3, 2]];
        let id = 0;
        let (p, d, w) = es_to_xor(4, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(4, p, d, w, id, 0, |a, b| a | b);
        let (exp_score, mut exp_path) = brute_assoc_diameter(4, es, id, |a, b| a | b);
        assert_eq!(got_score, exp_score);
        exp_path.reverse();
        check_path(&got_path, es, id, |a, b| a | b, exp_score);
        assert_eq!(got_path, exp_path);
    }

    #[test]
    fn or_star() {
        let es = &[[0, 1, 2], [0, 2, 8], [0, 3, 4], [0, 4, 1]];
        let id = 0;
        let (p, d, w) = es_to_xor(5, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(5, p, d, w, id, 0, |a, b| a | b);
        let (exp_score, mut exp_path) = brute_assoc_diameter(5, es, id, |a, b| a | b);
        exp_path.reverse();
        assert_eq!(got_score, exp_score);
        check_path(&got_path, es, id, |a, b| a | b, exp_score);
        assert_eq!(got_path, exp_path);
    }

    // --- AND tests -----------------------------------------------------------

    #[test]
    fn and_chain() {
        let es = &[[0, 1, 7], [1, 2, 3], [2, 3, 6]];
        let id = usize::MAX;
        let (p, d, w) = es_to_xor(4, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(4, p, d, w, id, 0, |a, b| a & b);
        let (exp_score, mut exp_path) = brute_assoc_diameter(4, es, id, |a, b| a & b);
        assert_eq!(got_score, exp_score);
        check_path(&got_path, es, id, |a, b| a & b, exp_score);
        exp_path.reverse();
        assert_eq!(got_path, exp_path);
    }

    #[test]
    fn and_star() {
        let es = &[[0, 1, 3], [0, 2, 5], [0, 3, 1], [0, 4, 7]];
        let id = usize::MAX;
        let (p, d, w) = es_to_xor(8, es.into_iter(), |&&[u, v, w]| (u, v, w));
        let (got_score, got_path) = diameter(8, p, d, w, id, 0, |a, b| a & b);
        let (exp_score, mut exp_path) = brute_assoc_diameter(5, es, id, |a, b| a & b);
        assert_eq!(got_score, exp_score);
        exp_path.reverse();
        check_path(&got_path, es, id, |a, b| a & b, exp_score);
        assert_eq!(got_path, exp_path);
    }
}
