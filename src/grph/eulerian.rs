use bit_vec::BitVec;

/// eulerian path starting from v
pub fn eulerian_path(v: usize, m: usize, adj: &[Vec<usize>]) -> Vec<usize> {
    let n = adj.len();
    let mut stk = Vec::with_capacity(m + 1);
    let mut done = BitVec::from_elem(n, false);
    let mut path = vec![0; m + 1];
    let mut idx = m + 1;
    stk.push(v);
    while let Some(&u) = stk.last() {
        if done[u] {
            idx -= 1;
            path[idx] = u;
            stk.pop();
        } else {
            for &w in &adj[u] {
                stk.push(w);
            }
            done.set(u, true);
        }
    }
    path
}

/// euler tour of a tree
pub fn tree_euler_tour(n: usize, dfs: &[usize], pos: &[usize], ss: &[usize]) -> Vec<usize> {
    let mut et = Vec::with_capacity(n * 2);
    let mut stack = Vec::with_capacity(n);
    for &v in dfs {
        while let Some(&u) = stack.last() {
            if pos[v] >= pos[u] + ss[u] {
                et.push(u);
                stack.pop();
            } else {
                break;
            }
        }
        et.push(v);
        stack.push(v);
    }
    while let Some(u) = stack.pop() {
        et.push(u);
    }
    et
}

// TODO: counting eulerian circuits
// https://judge.yosupo.jp/submission/287846
pub fn eulerian_circuit_count() {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify that `path` is a valid Eulerian path in `adj`.
    /// - `m` is the number of vertices in the returned path.
    /// - It must start at `start` and end at `end`.
    /// - Every directed edge in `adj` must appear exactly once as a consecutive pair.
    fn check_path(start: usize, end: usize, adj: &[Vec<usize>], m: usize, path: &[usize]) {
        // length check
        assert_eq!(
            path.len(),
            m,
            "wrong path length: got {}, expected {}",
            path.len(),
            m
        );
        assert_eq!(path[0], start, "path does not start at {}", start);
        assert_eq!(path[path.len() - 1], end, "path does not end at {}", end);

        // multiset copy of edges
        let mut edges: Vec<Vec<usize>> = adj.iter().cloned().collect();

        // consume each directed edge
        for window in path.windows(2) {
            let u = window[0];
            let v = window[1];
            // remove exactly one occurrence of v from edges[u]
            if let Some(pos) = edges[u].iter().position(|&x| x == v) {
                edges[u].remove(pos);
            } else {
                panic!("Edge {}→{} not found or already used", u, v);
            }
        }

        // no edges left unused
        for (u, outs) in edges.iter().enumerate() {
            assert!(
                outs.is_empty(),
                "Unused outgoing edges from {}: {:?}",
                u,
                outs
            );
        }
    }

    /// Wrapper for cycles: must return m+1 vertices, start==end.
    fn check_cycle(start: usize, adj: &[Vec<usize>], m: usize, cycle: &[usize]) {
        // cycle length = m+1
        assert_eq!(
            cycle.len(),
            m + 1,
            "cycle length should be m+1 = {}, got {}",
            m + 1,
            cycle.len()
        );
        // first == last == start
        assert_eq!(cycle[0], start, "cycle does not start at {}", start);
        assert_eq!(
            *cycle.last().unwrap(),
            start,
            "cycle does not end at {}",
            start
        );

        // consume each edge in the same way
        let mut edges: Vec<Vec<usize>> = adj.iter().cloned().collect();
        for window in cycle.windows(2) {
            let u = window[0];
            let v = window[1];
            if let Some(pos) = edges[u].iter().position(|&x| x == v) {
                edges[u].remove(pos);
            } else {
                panic!("Cycle edge {}→{} not found or already used", u, v);
            }
        }
        for (u, outs) in edges.iter().enumerate() {
            assert!(
                outs.is_empty(),
                "Unused outgoing edges from {} in cycle: {:?}",
                u,
                outs
            );
        }
    }

    #[test]
    fn simple_directed_path() {
        // 0 → 1 → 2
        let adj = vec![vec![1], vec![2], vec![]];
        // path has 3 vertices
        let m = 2;
        let path = eulerian_path(0, m, &adj);
        check_path(0, 2, &adj, m + 1, &path);
    }

    #[test]
    fn simple_directed_cycle_triangle() {
        // 0→1→2→0
        let adj = vec![vec![1], vec![2], vec![0]];
        let m = 3;
        let cycle = eulerian_path(0, m, &adj);
        check_cycle(0, &adj, m, &cycle);
    }

    #[test]
    fn disconnected_trivial_graph() {
        // no edges at all; from 0 the only "path" is [0]
        let adj = vec![vec![], vec![], vec![]];
        let m = 0;
        let path = eulerian_path(0, m, &adj);
        assert_eq!(path, vec![0]);
    }

    #[test]
    fn single_vertex_cycle() {
        // single node 0 with no self-edge
        // m = 1 ⇒ path = [0], then cycle = [0, 0]
        let adj = vec![vec![]];
        let m = 1;
        let cycle = eulerian_path(0, m, &adj);
        assert_eq!(cycle, vec![0, 0]);
    }

    #[test]
    fn two_node_cycle_multi_edge() {
        // 0→1 and 1→0 (one each) ⇒ 2 edges, m=2 ⇒ cycle length 3
        let adj = vec![vec![1], vec![0]];
        let m = 2;
        let cycle = eulerian_path(0, m, &adj);
        check_cycle(0, &adj, m, &cycle);
    }
}
