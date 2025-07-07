use crate::grph::flow::PushRelabel;
use std::ops::{AddAssign, SubAssign};

pub fn gomory_hu<F: Copy + Default + Ord + AddAssign + SubAssign>(
    n: usize,
    es: &[(usize, usize, F)],
) -> (Vec<(usize, usize, F)>, Vec<usize>) {
    let mut tree = Vec::with_capacity(n - 1);
    let mut p = vec![0; n];
    let mut d = PushRelabel::<F>::new(n);
    for &(u, v, c) in es {
        d.add_edge(u, v, c, c);
    }
    for i in 1..n {
        tree.push((i, p[i], d.reset().calc(i, p[i])));
        for j in i + 1..n {
            if p[j] == p[i] && d.left_of_min_cut(j) {
                p[j] = i;
            }
        }
    }
    (tree, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    type F = i32;

    /// brute‐force min‐cut between u and v by running Push–Relabel on the undirected graph
    fn brute_min_cut(n: usize, es: &[(usize, usize, F)]) -> impl Fn(usize, usize) -> F {
        move |u, v| {
            let mut pr = {
                // build an undirected flow network
                let mut d = PushRelabel::new(n);
                for &(x, y, c) in es {
                    d.add_edge(x, y, c, c);
                }
                d
            };
            pr.calc(u, v)
        }
    }

    /// query the GH‐tree: find the unique path u→…→v and return the smallest edge‐weight
    fn tree_min_cut(tree: &[(usize, usize, F)], u: usize, v: usize) -> F {
        // build adjacency list of (neighbor, weight)
        let n = tree.iter().map(|&(i, p, _)| i.max(p)).max().unwrap_or(0) + 1;
        let mut adj = vec![Vec::new(); n];
        for &(i, p, w) in tree {
            adj[i].push((p, w));
            adj[p].push((i, w));
        }
        // simple DFS
        let mut seen = vec![false; n];
        fn dfs(
            adj: &Vec<Vec<(usize, F)>>,
            seen: &mut Vec<bool>,
            cur: usize,
            target: usize,
        ) -> Option<F> {
            if cur == target {
                return Some(F::MAX);
            }
            seen[cur] = true;
            for &(nx, w) in &adj[cur] {
                if seen[nx] {
                    continue;
                }
                if let Some(min_below) = dfs(adj, seen, nx, target) {
                    return Some(min_below.min(w));
                }
            }
            None
        }
        dfs(&adj, &mut seen, u, v).unwrap_or(0)
    }

    #[test]
    fn trivial_two_nodes() {
        let es = &[(0, 1, 42)];
        let (tree, _) = gomory_hu(2, es);
        // only one edge in the tree: (1,parent=0,weight=42)
        assert_eq!(tree, vec![(1, 0, 42)]);
    }

    #[test]
    fn simple_chain_three_nodes() {
        // 0—5—1—3—2  => cuts(1,0)=5, cuts(2,1)=3
        let es = &[(0, 1, 5), (1, 2, 3)];
        let (tree, _) = gomory_hu(3, es);
        let mut sorted = tree.clone();
        sorted.sort();
        assert_eq!(sorted, vec![(1, 0, 5), (2, 1, 3)]);
    }

    #[test]
    fn disconnected_components() {
        // two components: {0–1 cap=7}, {2–3 cap=11}
        let es = &[(0, 1, 7), (2, 3, 11)];
        let (tree, _) = gomory_hu(4, es);
        // expected:
        //   (1,0,7),
        //   (2,0,0),  // min‐cut(2,0)=0
        //   (3,2,11)
        let mut sorted = tree.clone();
        sorted.sort();
        assert_eq!(sorted, vec![(1, 0, 7), (2, 0, 0), (3, 2, 11)]);
    }

    #[test]
    fn star_graph() {
        // node 0 is center with edges of distinct weights
        let es = &[(0, 1, 10), (0, 2, 20), (0, 3, 30), (0, 4, 40)];
        let (tree, _) = gomory_hu(5, es);
        let mut sorted = tree.clone();
        sorted.sort();
        assert_eq!(
            sorted,
            vec![(1, 0, 10), (2, 0, 20), (3, 0, 30), (4, 0, 40),]
        );
    }

    #[test]
    fn complete_graph_k4_random_caps() {
        let n = 4;
        // fixed “random” capacities for determinism
        let es = &[
            (0, 1, 13),
            (0, 2, 7),
            (0, 3, 21),
            (1, 2, 5),
            (1, 3, 17),
            (2, 3, 11),
        ];
        let (tree, _) = gomory_hu(n, es);

        let bf = brute_min_cut(n, es);
        // verify for every pair u<v, the min cut from brute == tree_min_cut
        for u in 0..n {
            for v in (u + 1)..n {
                let bc = bf(u, v);
                let tc = tree_min_cut(&tree, u, v);
                assert_eq!(
                    tc, bc,
                    "mincut({}, {}) = {} but tree gives {}",
                    u, v, bc, tc
                );
            }
        }
    }

    #[test]
    fn square_grid_2x2() {
        // 4‐node 2×2 grid:
        // 0—1
        // |  |
        // 2—3
        let es = &[(0, 1, 3), (1, 3, 4), (3, 2, 5), (2, 0, 6)];
        let (tree, _) = gomory_hu(4, es);
        let bf = brute_min_cut(4, es);
        for u in 0..4 {
            for v in (u + 1)..4 {
                assert_eq!(
                    tree_min_cut(&tree, u, v),
                    bf(u, v),
                    "grid2x2 mincut({}, {}) mismatch",
                    u,
                    v
                );
            }
        }
    }
}
