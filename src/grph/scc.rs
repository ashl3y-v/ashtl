// TODO: implement incremental SCC

use bit_vec::BitVec;

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

#[cfg(test)]
mod tests {
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
        let mut comps = collect_scc(&g);
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
}
