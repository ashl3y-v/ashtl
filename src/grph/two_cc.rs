pub fn two_cc<F>(n: usize, adj: &[Vec<usize>], mut f: F)
where
    F: FnMut(&[(usize, usize)]),
{
    let mut tin = vec![0; n];
    let mut low = vec![0; n];
    let mut visited = vec![false; n];
    let mut timer = 0;
    let mut edge_stack = Vec::new();
    fn dfs<F>(
        v: usize,
        parent: Option<usize>,
        adj: &[Vec<usize>],
        visited: &mut [bool],
        tin: &mut [usize],
        low: &mut [usize],
        timer: &mut usize,
        edge_stack: &mut Vec<(usize, usize)>,
        f: &mut F,
    ) where
        F: FnMut(&[(usize, usize)]),
    {
        visited[v] = true;
        tin[v] = *timer;
        low[v] = *timer;
        *timer += 1;
        for &to in &adj[v] {
            if Some(to) == parent {
                continue;
            }
            if visited[to] {
                low[v] = low[v].min(tin[to]);
                if tin[to] < tin[v] {
                    edge_stack.push((v, to));
                }
            } else {
                edge_stack.push((v, to));
                dfs(to, Some(v), adj, visited, tin, low, timer, edge_stack, f);
                low[v] = low[v].min(low[to]);
                if !parent.is_none() && low[to] >= tin[v] {
                    let mut component = Vec::new();
                    while let Some(e) = edge_stack.pop() {
                        component.push(e);
                        if e == (v, to) {
                            break;
                        }
                    }
                    f(&component);
                }
            }
        }
    }

    for v in 0..n {
        if !visited[v] {
            dfs(
                v,
                None,
                adj,
                &mut visited,
                &mut tin,
                &mut low,
                &mut timer,
                &mut edge_stack,
                &mut f,
            );
            // any leftover edges form one last block
            if !edge_stack.is_empty() {
                f(&edge_stack);
                edge_stack.clear();
            }
        }
    }
}

pub fn cut_vertices<F>(n: usize, adj: &[Vec<usize>], mut is_cut: F)
where
    F: FnMut(usize),
{
    let mut visited = vec![false; n];
    let mut tin = vec![0; n];
    let mut low = vec![0; n];
    let mut timer = 0;

    fn dfs<F>(
        v: usize,
        parent: Option<usize>,
        adj: &[Vec<usize>],
        visited: &mut [bool],
        tin: &mut [usize],
        low: &mut [usize],
        timer: &mut usize,
        is_cut: &mut F,
    ) where
        F: FnMut(usize),
    {
        visited[v] = true;
        tin[v] = *timer;
        low[v] = *timer;
        *timer += 1;
        let mut children = 0;
        for &to in &adj[v] {
            if Some(to) == parent {
                continue;
            }
            if visited[to] {
                low[v] = low[v].min(tin[to]);
            } else {
                children += 1;
                dfs(to, Some(v), adj, visited, tin, low, timer, is_cut);
                low[v] = low[v].min(low[to]);
                if parent.is_some() && low[to] >= tin[v] {
                    is_cut(v);
                }
            }
        }

        if parent.is_none() && children > 1 {
            is_cut(v);
        }
    }

    for v in 0..n {
        if !visited[v] {
            dfs(
                v,
                None,
                adj,
                &mut visited,
                &mut tin,
                &mut low,
                &mut timer,
                &mut is_cut,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::cut_vertices;
    use super::two_cc;
    use std::collections::HashSet;

    /// Normalize edge orientations to undirected form.
    fn normalize(block: &[(usize, usize)]) -> HashSet<(usize, usize)> {
        block
            .iter()
            .map(|&(u, v)| if u < v { (u, v) } else { (v, u) })
            .collect()
    }

    /// Run the algorithm and collect all biconnected components as sets of undirected edges.
    fn collect_components(n: usize, adj: &[Vec<usize>]) -> Vec<HashSet<(usize, usize)>> {
        let mut comps = Vec::new();
        two_cc(n, adj, |comp| {
            comps.push(normalize(comp));
        });
        comps
    }

    #[test]
    fn test_empty_graph() {
        let adj: Vec<Vec<usize>> = vec![];
        let comps = collect_components(0, &adj);
        assert!(comps.is_empty());
    }

    #[test]
    fn test_single_edge() {
        let adj = vec![vec![1], vec![0]];
        let comps = collect_components(2, &adj);
        let expected: Vec<HashSet<(usize, usize)>> = vec![[(0, 1)].iter().cloned().collect()];
        assert_eq!(comps.len(), expected.len());
        for exp in expected {
            assert!(comps.contains(&exp));
        }
    }

    #[test]
    fn test_triangle_cycle() {
        let adj = vec![vec![1, 2], vec![0, 2], vec![0, 1]];
        let comps = collect_components(3, &adj);
        let mut exp = HashSet::new();
        exp.insert((0, 1));
        exp.insert((1, 2));
        exp.insert((0, 2));
        assert_eq!(comps.len(), 1);
        assert_eq!(comps[0], exp);
    }

    #[test]
    fn test_line_of_three() {
        let adj = vec![vec![1], vec![0, 2], vec![1]];
        let comps = collect_components(3, &adj);
        let expected: Vec<HashSet<(usize, usize)>> = vec![
            [(1, 2)].iter().cloned().collect(),
            [(0, 1)].iter().cloned().collect(),
        ];
        assert_eq!(comps.len(), expected.len());
        for exp in expected {
            assert!(comps.contains(&exp));
        }
    }

    #[test]
    fn test_two_triangles_sharing_vertex() {
        // Triangles: (0-1-2-0) and (2-3-4-2)
        let adj = vec![
            vec![1, 2],
            vec![0, 2],
            vec![0, 1, 3, 4],
            vec![2, 4],
            vec![2, 3],
        ];
        let comps = collect_components(5, &adj);

        let mut t1 = HashSet::new();
        t1.insert((0, 1));
        t1.insert((1, 2));
        t1.insert((0, 2));

        let mut t2 = HashSet::new();
        t2.insert((2, 3));
        t2.insert((3, 4));
        t2.insert((2, 4));

        assert_eq!(comps.len(), 2);
        assert!(comps.contains(&t1));
        assert!(comps.contains(&t2));
    }

    fn collect_cuts(n: usize, adj: &[Vec<usize>]) -> HashSet<usize> {
        let mut cuts = HashSet::new();
        cut_vertices(n, adj, |v| {
            cuts.insert(v);
        });
        cuts
    }

    #[test]
    fn test_empty_graph_cutvertices() {
        let adj: Vec<Vec<usize>> = vec![];
        let cuts = collect_cuts(0, &adj);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_single_node() {
        let adj = vec![vec![]];
        let cuts = collect_cuts(1, &adj);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_two_nodes() {
        let adj = vec![vec![1], vec![0]];
        let cuts = collect_cuts(2, &adj);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_triangle_cycle_cutvertices() {
        let adj = vec![vec![1, 2], vec![0, 2], vec![0, 1]];
        let cuts = collect_cuts(3, &adj);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_line_of_three_cutvertices() {
        // 0-1-2, only 1 is cut vertex
        let adj = vec![vec![1], vec![0, 2], vec![1]];
        let cuts = collect_cuts(3, &adj);
        let expected: HashSet<_> = vec![1].into_iter().collect();
        assert_eq!(cuts, expected);
    }

    #[test]
    fn test_star_graph() {
        // 0 connected to 1,2,3; 0 is cut vertex
        let adj = vec![vec![1, 2, 3], vec![0], vec![0], vec![0]];
        let cuts = collect_cuts(4, &adj);
        let expected: HashSet<_> = vec![0].into_iter().collect();
        assert_eq!(cuts, expected);
    }

    #[test]
    fn test_disconnected_graph() {
        // two separate lines: (0-1-2) and (3-4)
        let adj = vec![vec![1], vec![0, 2], vec![1], vec![4], vec![3]];
        let cuts = collect_cuts(5, &adj);
        let expected: HashSet<_> = vec![1].into_iter().collect();
        assert_eq!(cuts, expected);
    }
}
