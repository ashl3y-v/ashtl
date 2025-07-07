use bit_vec::BitVec;
use std::collections::VecDeque;

/// Tarjan's SCC
/// calls f on the SCCs in reverse topological order
/// outputs the indices of the SCCs that the vertices are in (also in reverse topological order)
pub fn scc<F: FnMut(Vec<usize>)>(g: &[Vec<usize>], mut f: F) -> Vec<usize> {
    let n = g.len();
    if n == 0 {
        return Vec::new();
    }
    let mut idx = 1;
    let mut comp_count = usize::MAX;
    let mut root_idx = vec![0; n];
    let mut child = BitVec::from_elem(n, false);
    let mut start = 0;
    let mut stk = Vec::with_capacity(n);
    let mut cur = 0;
    stk.push((start, 0));
    root_idx[start] = idx;
    idx += 1;
    'a: loop {
        let (v, e_m) = &mut stk[cur];
        let v = *v;
        let e = *e_m;
        let ws = &g[v];
        if e < ws.len() {
            let w = ws[e];
            if root_idx[w] == 0 {
                root_idx[w] = idx;
                stk.push((w, 0));
                idx += 1;
                cur = stk.len() - 1;
                continue 'a;
            } else {
                if root_idx[w] < root_idx[v] {
                    root_idx[v] = root_idx[w];
                    child.set(v, true);
                }
                *e_m += 1;
            }
        } else {
            if !child[v] {
                let comp = stk.drain(cur..).map(|(v, _)| v).collect::<Vec<_>>();
                idx -= comp.len();
                for &v in &comp {
                    root_idx[v] = comp_count;
                }
                f(comp);
                comp_count -= 1;
            }
            if cur != 0 {
                cur -= 1;
            } else {
                while start < n && root_idx[start] != 0 {
                    start += 1;
                }
                if start < n {
                    root_idx[start] = idx;
                    stk.push((start, 0));
                    cur = stk.len() - 1;
                    idx += 1;
                    start += 1;
                } else {
                    break;
                }
            }
        }
    }
    for v in &mut root_idx {
        *v = !*v;
    }
    root_idx
}

// TODO: improve two cc
// https://judge.yosupo.jp/submission/287412
pub fn cc2<F>(n: usize, adj: &[Vec<usize>], mut f: F)
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

/// O(n^2)
pub fn comp_cc(adj: &[Vec<usize>], mut f: impl FnMut(Vec<usize>)) {
    let n = adj.len();
    let mut visited = BitVec::from_elem(n, false);
    let mut temp = BitVec::from_elem(n, false);
    let mut next_unvisited = 0;
    let mut remaining: Vec<usize> = Vec::with_capacity(n);
    remaining.extend(0..n);
    while next_unvisited < n {
        let mut component = Vec::with_capacity(remaining.len());
        component.push(next_unvisited);
        visited.set(next_unvisited, true);
        let mut queue = VecDeque::with_capacity(remaining.len());
        queue.push_back(next_unvisited);
        while let Some(curr) = queue.pop_front() {
            for &edge in &adj[curr] {
                temp.set(edge, true);
            }
            let mut i = 0;
            while i < remaining.len() {
                let node = remaining[i];
                if visited[node] {
                    remaining.swap_remove(i);
                } else if !temp[node] {
                    visited.set(node, true);
                    component.push(node);
                    queue.push_back(node);
                    remaining.swap_remove(i);
                } else {
                    i += 1;
                }
            }
            for &edge in &adj[curr] {
                temp.set(edge, false);
            }
        }
        f(component);
        while next_unvisited < n && visited[next_unvisited] {
            next_unvisited += 1;
        }
    }
}

// TODO: two ecc
// https://judge.yosupo.jp/submission/106412
pub fn ecc2() {}

// TODO: three ecc
// https://judge.yosupo.jp/submission/248134
pub fn ecc3() {}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    fn collect_scc(g: &[Vec<usize>]) -> Vec<Vec<usize>> {
        let mut comps = Vec::new();
        scc(g, |comp_slice| {
            let mut comp = comp_slice.to_vec();
            comp.sort_unstable();
            comps.push(comp);
        });
        comps.sort_unstable_by(|a, b| a.cmp(b));
        comps
    }

    #[test]
    fn test_empty_graph() {
        let g: Vec<Vec<usize>> = vec![];
        let comps = collect_scc(&g);
        assert!(comps.is_empty(), "expected no components, got {:?}", comps);
    }

    #[test]
    fn test_single_vertex() {
        let g = vec![vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0]]);
    }

    #[test]
    fn test_disconnected_vertices() {
        let g = vec![vec![], vec![], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0], vec![1], vec![2]]);
    }

    #[test]
    fn test_linear_chain() {
        let g = vec![vec![1], vec![2], vec![3], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0], vec![1], vec![2], vec![3]]);
    }

    #[test]
    fn test_simple_cycle() {
        let g = vec![vec![1], vec![2], vec![0]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0, 1, 2]]);
    }

    #[test]
    fn test_two_disjoint_cycles() {
        let g = vec![vec![1], vec![0], vec![3], vec![2]];
        let comps = collect_scc(&g);
        assert_eq!(comps.len(), 2);
        assert!(comps.contains(&vec![0, 1]));
        assert!(comps.contains(&vec![2, 3]));
    }

    #[test]
    fn test_mixed_graph() {
        let g = vec![
            vec![1],    // 0 -> 1
            vec![2],    // 1 -> 2
            vec![0, 3], // 2 -> 0, 2 -> 3
            vec![4],    // 3 -> 4
            vec![3],    // 4 -> 3
            vec![],     // 5 isolated
        ];
        let comps = collect_scc(&g);
        assert_eq!(comps.len(), 3);
        assert!(comps.contains(&vec![0, 1, 2]));
        assert!(comps.contains(&vec![3, 4]));
        assert!(comps.contains(&vec![5]));
    }

    #[test]
    fn test_complete_graph() {
        let n = 4;
        let g: Vec<_> = (0..n)
            .map(|u| (0..n).filter(|&v| v != u).collect())
            .collect();
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![(0..4).collect::<Vec<_>>()]);
    }

    #[test]
    fn test_star_graph() {
        let g = vec![vec![1, 2, 3], vec![], vec![], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0], vec![1], vec![2], vec![3]]);
    }

    #[test]
    fn test_bidirectional_edge() {
        let g = vec![vec![1], vec![0, 2], vec![1, 3], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps.len(), 2);
        assert!(comps.contains(&vec![0, 1, 2]));
        assert!(comps.contains(&vec![3]));
    }

    #[test]
    fn test_self_loops() {
        let g = vec![vec![0], vec![1], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps, vec![vec![0], vec![1], vec![2]]);
    }

    #[test]
    fn test_parallel_edges() {
        let g = vec![vec![1, 1, 2], vec![0], vec![]];
        let comps = collect_scc(&g);
        assert_eq!(comps.len(), 2);
        assert!(comps.contains(&vec![0, 1]));
        assert!(comps.contains(&vec![2]));
    }

    #[test]
    fn test_complex_nested() {
        // 0<->1<->2 cycle, 2->3->4->2 small cycle, 4->5 leaf
        let g = vec![
            vec![1],    // 0->1
            vec![2],    // 1->2
            vec![0, 3], // 2->0,2->3
            vec![4],    // 3->4
            vec![2, 5], // 4->2,4->5
            vec![],     // 5
        ];
        let comps = collect_scc(&g);
        assert_eq!(comps.len(), 2);
        assert!(comps.contains(&vec![0, 1, 2, 3, 4]));
        assert!(comps.contains(&vec![5]));
    }

    #[test]
    fn test_scc_reverse_topo_order() {
        let g = vec![
            vec![1], // 0 -> 1
            vec![2], // 1 -> 2
            vec![],  // 2
        ];
        let mut seen = Vec::new();
        scc(&g, |comp| {
            seen.push(comp.to_vec());
        });
        assert_eq!(seen, vec![vec![2], vec![1], vec![0]]);
    }

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
        cc2(n, adj, |comp| {
            comps.push(normalize(comp));
        });
        comps
    }

    #[test]
    fn test_empty_graph_two_cc() {
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
    fn test_star_graph_two_cc() {
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

    #[test]
    fn test_empty_graph_comp_cc() {
        let adj: Vec<Vec<usize>> = vec![];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));
        assert_eq!(components, Vec::<Vec<usize>>::new());
    }

    #[test]
    fn test_single_vertex_comp_cc() {
        let adj = vec![vec![]]; // One vertex, no edges
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));
        assert_eq!(components, vec![vec![0]]);
    }

    #[test]
    fn test_complete_graph_comp_cc() {
        // Complete graph K4 - complement has no edges
        let adj = vec![
            vec![1, 2, 3], // 0 connected to 1,2,3
            vec![0, 2, 3], // 1 connected to 0,2,3
            vec![0, 1, 3], // 2 connected to 0,1,3
            vec![0, 1, 2], // 3 connected to 0,1,2
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Each vertex is its own component in complement
        assert_eq!(components.len(), 4);
        for comp in &components {
            assert_eq!(comp.len(), 1);
        }
    }

    #[test]
    fn test_no_edges() {
        // Graph with no edges - complement is complete
        let adj = vec![vec![], vec![], vec![], vec![]];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 4);

        let mut sorted_comp = components[0].clone();
        sorted_comp.sort();
        assert_eq!(sorted_comp, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_path_graph() {
        // Path: 0-1-2-3
        let adj = vec![
            vec![1],    // 0 connected to 1
            vec![0, 2], // 1 connected to 0,2
            vec![1, 3], // 2 connected to 1,3
            vec![2],    // 3 connected to 2
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Complement should have edges: 0-2, 0-3, 1-3
        // This creates one component with all vertices
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 4);
    }

    #[test]
    fn test_disconnected_graph_comp_cc() {
        // Two separate edges: 0-1 and 2-3
        let adj = vec![
            vec![1], // 0 connected to 1
            vec![0], // 1 connected to 0
            vec![3], // 2 connected to 3
            vec![2], // 3 connected to 2
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Complement has edges: 0-2, 0-3, 1-2, 1-3
        // This creates one component
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 4);
    }

    #[test]
    fn test_star_graph_comp_cc() {
        // Star graph: center 0 connected to 1,2,3
        let adj = vec![
            vec![1, 2, 3], // 0 connected to 1,2,3
            vec![0],       // 1 connected to 0
            vec![0],       // 2 connected to 0
            vec![0],       // 3 connected to 0
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Complement has edges: 1-2, 1-3, 2-3 (triangle)
        // Plus isolated vertex 0
        assert_eq!(components.len(), 2);

        let mut comp_sizes: Vec<usize> = components.iter().map(|c| c.len()).collect();
        comp_sizes.sort();
        assert_eq!(comp_sizes, vec![1, 3]);
    }

    #[test]
    fn test_triangle_plus_isolated() {
        // Triangle 0-1-2-0 plus isolated vertex 3
        let adj = vec![
            vec![1, 2], // 0 connected to 1,2
            vec![0, 2], // 1 connected to 0,2
            vec![0, 1], // 2 connected to 0,1
            vec![],     // 3 isolated
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Complement connects 3 to everyone (0,1,2)
        // So we get one component with all vertices
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 4);
    }

    #[test]
    fn test_larger_disconnected() {
        // Two triangles: 0-1-2-0 and 3-4-5-3
        let adj = vec![
            vec![1, 2], // 0 connected to 1,2
            vec![0, 2], // 1 connected to 0,2
            vec![0, 1], // 2 connected to 0,1
            vec![4, 5], // 3 connected to 4,5
            vec![3, 5], // 4 connected to 3,5
            vec![3, 4], // 5 connected to 3,4
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Complement connects all vertices from first triangle to second triangle
        // This creates one large component
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 6);
    }

    #[test]
    fn test_callback_ordering() {
        // Test that components are found in order of first vertex
        let adj = vec![
            vec![1], // 0-1 pair
            vec![0],
            vec![3], // 2-3 pair
            vec![2],
        ];
        let mut components = Vec::new();
        comp_cc(&adj, |comp| components.push(comp));

        // Should find one component containing all vertices
        // since complement connects the pairs
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].len(), 4);

        // First vertex should be 0 (lowest unvisited)
        assert_eq!(components[0][0], 0);
    }
}
