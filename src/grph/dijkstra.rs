use crate::ds::score::MinScore;
use bit_vec::BitVec;
use std::{collections::BinaryHeap, ops::Add};

/// Dijkstra's algorithm
/// Works for any type T such that:
/// For source T::default() is correct initialization
/// sum(p) + v >= sum(p) if v adjacent to end of p
/// if p, q have same end and sum(p) >= sum(q), then sum(p) + v >= sum(q) + v for all v adjacent to end
/// https://codeforces.com/blog/entry/107810
pub fn dijkstra<T: Copy + PartialOrd + Add<T, Output = T> + Default>(
    u: usize,
    v: Option<usize>,
    adj: &[Vec<(usize, T)>],
) -> Vec<Option<T>> {
    let n = adj.len();
    let mut seen = BitVec::from_elem(n, false);
    let mut scores = vec![None; n];
    let mut visit = BinaryHeap::new();
    scores[u] = Some(T::default());
    visit.push(MinScore(T::default(), u));
    while let Some(MinScore(s, i)) = visit.pop() {
        if seen[i] {
            continue;
        }
        if v == Some(i) {
            break;
        }
        for &(j, w) in &adj[i] {
            if seen[j] {
                continue;
            }
            let ns = s + w;
            if scores[j].is_none() || Some(ns) < scores[j] {
                scores[j] = Some(ns);
                visit.push(MinScore(ns, j));
            }
        }
        seen.set(i, true);
    }
    scores
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::i32;

    /// Simple 3-node line graph: 0→1 (5), 0→2 (10), 1→2 (3)
    fn linear_graph() -> Vec<Vec<(usize, i32)>> {
        vec![vec![(1, 5), (2, 10)], vec![(2, 3)], vec![]]
    }

    #[test]
    fn test_simple_line() {
        let adj = linear_graph();
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(5), Some(8)],
            "0→1 should be 5, 0→2 via 1 should be 8"
        );
    }

    #[test]
    fn test_unreachable() {
        // Two isolated nodes
        let adj: Vec<Vec<(usize, i32)>> = vec![vec![], vec![]];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), None],
            "Node 1 is unreachable and should remain at max"
        );
    }

    #[test]
    fn test_single_node() {
        let adj: Vec<Vec<(usize, i32)>> = vec![vec![]];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0)],
            "Single-node graph distance is zero to itself"
        );
    }

    #[test]
    fn test_target_early_exit() {
        let adj = linear_graph();
        // Asking for target=2 should break out early once distance to 2 is finalized
        let dist = dijkstra(0, Some(2), &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(5), Some(8)],
            "Early exit must still record correct distances"
        );
    }

    #[test]
    fn test_multiple_paths() {
        // Graph:
        // 0→1 (1), 0→2 (4)
        // 1→2 (1), 1→3 (5)
        // 2→3 (1)
        let adj = vec![
            vec![(1, 1), (2, 4)],
            vec![(2, 1), (3, 5)],
            vec![(3, 1)],
            vec![],
        ];
        let dist = dijkstra(0, None, &adj);
        assert_eq!(
            dist,
            vec![Some(0), Some(1), Some(2), Some(3)],
            "Should pick the shortest paths 0→1→2→3"
        );
    }
}
