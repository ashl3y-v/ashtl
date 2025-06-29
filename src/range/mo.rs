use crate::geo::hilbert::hilbert;
use bit_vec::BitVec;

// Mo's algorithm using Hilbert curve
// O(n sqrt(q))
pub fn mo<T, R>(
    qs: &mut [(usize, usize, usize, T)],
    init: impl FnOnce(&mut [(usize, usize, usize, T)]) -> R,
    mut add: impl FnMut(usize, &mut R),
    mut remove: impl FnMut(usize, &mut R),
    mut answer: impl FnMut(usize, usize, usize, &T, &mut R),
) -> R {
    let q = qs.len();
    let mut ans = init(qs);
    let k = q.ilog2() + if q.is_power_of_two() { 0 } else { 1 };
    qs.sort_by_key(|&(i, j, ..)| hilbert(i as u64, j as u64, k as u64));
    let (mut l, mut r) = (1, 0);
    for &(q_l, q_r, qi, ref data) in &*qs {
        while l > q_l {
            l -= 1;
            add(l, &mut ans);
        }
        while r < q_r {
            r += 1;
            add(r, &mut ans);
        }
        while l < q_l {
            remove(l, &mut ans);
            l += 1;
        }
        while r > q_r {
            remove(r, &mut ans);
            r -= 1;
        }
        answer(q_l, q_r, qi, data, &mut ans);
    }
    ans
}

// Mo's algorithm on trees using Hilbert curve
// O(n sqrt(q))
pub fn mo_tree_paths<T, R>(
    et: &[usize],
    lca: impl Fn(usize, usize) -> usize,
    qs: &mut [(usize, usize, usize, T)],
    init: impl FnOnce(&mut [(usize, usize, usize, T)]) -> R,
    add: impl Fn(usize, &mut R),
    remove: impl Fn(usize, &mut R),
    mut answer: impl FnMut(usize, usize, usize, &T, &mut R),
) -> R {
    let toggle = move |i, (st, vis): &mut (R, BitVec)| {
        let u = et[i];
        if !vis[u] {
            add(i, st);
        } else {
            remove(i, st);
        }
        vis.set(u, !vis[u]);
    };
    mo(
        qs,
        |qs| (init(qs), BitVec::from_elem(et.len() / 2, false)),
        &toggle,
        &toggle,
        |l, r, qi, data, s| {
            let lc = lca(et[l], et[r]);
            if lc != et[l] && lc != et[r] {
                toggle(lc, s);
            }
            answer(l, r, qi, data, &mut s.0);
            if lc != et[l] && lc != et[r] {
                toggle(lc, s);
            }
        },
    )
    .0
}

#[cfg(test)]
mod tests {
    use super::{mo, mo_tree_paths};
    use std::collections::HashMap;

    #[test]
    fn test_mo_range_distinct() {
        // array and queries
        let arr = vec![1, 2, 1, 3, 2];
        // (l, r, query_index, unused data)
        let mut qs = vec![
            (0, 2, 0, ()), // [1,2,1] -> 2 distinct
            (1, 4, 1, ()), // [2,1,3,2] -> 3 distinct
        ];

        // state that lives through the Mo sweep
        struct State {
            answers: Vec<usize>,
            freq: HashMap<i32, usize>,
            distinct: usize,
        }

        let state = mo(
            &mut qs,
            |qs| State {
                answers: vec![0; qs.len()],
                freq: HashMap::new(),
                distinct: 0,
            },
            // add element at index i
            |i, st: &mut State| {
                let v = arr[i];
                let cnt = st.freq.entry(v).or_insert(0);
                if *cnt == 0 {
                    st.distinct += 1;
                }
                *cnt += 1;
            },
            // remove element at index i
            |i, st: &mut State| {
                let v = arr[i];
                let cnt = st.freq.get_mut(&v).unwrap();
                *cnt -= 1;
                if *cnt == 0 {
                    st.distinct -= 1;
                }
            },
            // record answer for this query
            |_, _, qi, &(), st: &mut State| {
                st.answers[qi] = st.distinct;
            },
        );

        assert_eq!(state.answers, vec![2, 3]);
    }

    #[test]
    fn test_mo_range_sum() {
        let arr = vec![1, 2, 3, 4, 5];
        let mut qs = vec![
            (1, 3, 0, ()), // sum of [2,3,4] = 9
            (0, 4, 1, ()), // sum of [1,2,3,4,5] = 15
        ];

        struct State {
            answers: Vec<i64>,
            sum: i64,
        }

        let state = mo(
            &mut qs,
            |qs| State {
                answers: vec![0; qs.len()],
                sum: 0,
            },
            |i, st: &mut State| {
                st.sum += arr[i] as i64;
            },
            |i, st: &mut State| {
                st.sum -= arr[i] as i64;
            },
            |_, _, qi, &(), st: &mut State| {
                st.answers[qi] = st.sum;
            },
        );

        assert_eq!(state.answers, vec![9, 15]);
    }

    //----------------------------------------------------------------------//
    // 2) Mo on a tree (Euler tour + LCA)
    //----------------------------------------------------------------------//

    /// A simpler version that *does* return parent,depth separately.
    fn build_euler_with_pd(
        adj: &Vec<Vec<usize>>,
    ) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let n = adj.len();
        let mut et = Vec::with_capacity(2 * n);
        let mut first = vec![0; n];
        let mut last = vec![0; n];
        let mut parent = vec![0; n];
        let mut depth = vec![0; n];

        fn dfs(
            u: usize,
            p: usize,
            adj: &Vec<Vec<usize>>,
            et: &mut Vec<usize>,
            first: &mut [usize],
            last: &mut [usize],
            parent: &mut [usize],
            depth: &mut [usize],
        ) {
            parent[u] = p;
            first[u] = et.len();
            et.push(u);
            for &v in &adj[u] {
                if v == p {
                    continue;
                }
                depth[v] = depth[u] + 1;
                dfs(v, u, adj, et, first, last, parent, depth);
            }
            last[u] = et.len();
            et.push(u);
        }

        dfs(
            0,
            0,
            adj,
            &mut et,
            &mut first,
            &mut last,
            &mut parent,
            &mut depth,
        );
        (et, first, last, parent, depth)
    }

    #[test]
    fn test_mo_tree_paths_distinct() {
        // build a little path‐tree: 0—1—2—3
        let adj = vec![
            vec![1],    // 0
            vec![0, 2], // 1
            vec![1, 3], // 2
            vec![2],    // 3
        ];
        let values = vec![10, 20, 10, 30];
        let (et, first, last, parent, depth) = build_euler_with_pd(&adj);
        // LCA by lifting parent pointers (naïve)
        let lca = move |mut u: usize, mut v: usize| {
            if depth[u] > depth[v] {
                std::mem::swap(&mut u, &mut v);
            }
            while depth[v] > depth[u] {
                v = parent[v];
            }
            while u != v {
                u = parent[u];
                v = parent[v];
            }
            u
        };

        // our queries (u,v) pairs
        let raw = vec![
            (0, 2), // path = [0,1,2] -> values {10,20,10} -> 2 distinct
            (1, 3), // [1,2,3] -> {20,10,30} -> 3
            (0, 3), // [0,1,2,3] -> {10,20,10,30} -> 3
        ];

        // build the mo_tree_paths query‐tuple
        let mut qs = Vec::new();
        for (qi, &(u, v)) in raw.iter().enumerate() {
            let (mut a, mut b) = (u, v);
            if first[a] > first[b] {
                std::mem::swap(&mut a, &mut b);
            }
            let w = lca(a, b);
            let (l, r) = if w == a {
                (first[a], first[b])
            } else {
                (last[a], first[b])
            };
            qs.push((l, r, qi, ()));
        }

        struct State {
            answers: Vec<usize>,
            freq: HashMap<i32, usize>,
            distinct: usize,
        }

        let state = mo_tree_paths(
            &et,
            lca,
            &mut qs,
            |qs| State {
                answers: vec![0; qs.len()],
                freq: HashMap::new(),
                distinct: 0,
            },
            |i, st: &mut State| {
                let node = et[i];
                let v = values[node];
                let cnt = st.freq.entry(v).or_insert(0);
                if *cnt == 0 {
                    st.distinct += 1;
                }
                *cnt += 1;
            },
            |i, st: &mut State| {
                let node = et[i];
                let v = values[node];
                let cnt = st.freq.get_mut(&v).unwrap();
                *cnt -= 1;
                if *cnt == 0 {
                    st.distinct -= 1;
                }
            },
            |_, _, qi, &(), st: &mut State| {
                st.answers[qi] = st.distinct;
            },
        );

        // check in original query‐order
        assert_eq!(state.answers, vec![2, 3, 3]);
    }

    #[test]
    fn test_mo_tree_paths_sum() {
        // same tree but now values = weights
        let adj = vec![vec![1], vec![0, 2], vec![1, 3], vec![2]];
        let values = vec![5, 1, 2, 1];
        let (et, first, last, parent, depth) = build_euler_with_pd(&adj);
        let lca = move |mut u: usize, mut v: usize| {
            if depth[u] > depth[v] {
                std::mem::swap(&mut u, &mut v);
            }
            while depth[v] > depth[u] {
                v = parent[v];
            }
            while u != v {
                u = parent[u];
                v = parent[v];
            }
            u
        };

        // queries: (0 → 2), (1 → 3)
        let raw = vec![(0, 2), (1, 3)];
        let mut qs = Vec::new();
        for (qi, &(u, v)) in raw.iter().enumerate() {
            let (mut a, mut b) = (u, v);
            if first[a] > first[b] {
                std::mem::swap(&mut a, &mut b);
            }
            let w = lca(a, b);
            let (l, r) = if w == a {
                (first[a], first[b])
            } else {
                (last[a], first[b])
            };
            qs.push((l, r, qi, ()));
        }

        struct State {
            answers: Vec<i64>,
            sum: i64,
        }

        let state = mo_tree_paths(
            &et,
            lca,
            &mut qs,
            |qs| State {
                answers: vec![0; qs.len()],
                sum: 0,
            },
            |i, st: &mut State| {
                let node = et[i];
                st.sum += values[node] as i64;
            },
            |i, st: &mut State| {
                let node = et[i];
                st.sum -= values[node] as i64;
            },
            |_, _, qi, &(), st: &mut State| {
                st.answers[qi] = st.sum;
            },
        );

        // path sums: 0→2 is 5+1+2=8; 1→3 is 1+2+1=4
        assert_eq!(state.answers, vec![8, 4]);
    }

    #[test]
    fn test_mo_tree_paths_xor() {
        // build a small tree:      0
        //                         / \
        //                        1   2
        //                             \
        //                              3
        let adj = vec![
            vec![1, 2], // 0
            vec![0],    // 1
            vec![0, 3], // 2
            vec![2],    // 3
        ];
        // assign each node a value
        let values = vec![3u32, 5u32, 1u32, 7u32];

        // build Euler tour + parent, depth arrays
        let (et, first, last, parent, depth) = build_euler_with_pd(&adj);

        // LCA by naive parent‐lifting
        let lca = move |mut u: usize, mut v: usize| {
            if depth[u] > depth[v] {
                std::mem::swap(&mut u, &mut v);
            }
            while depth[v] > depth[u] {
                v = parent[v];
            }
            while u != v {
                u = parent[u];
                v = parent[v];
            }
            u
        };

        // queries: (0→2), (1→3), (0→3)
        let raw = vec![(0, 2), (1, 3), (0, 3)];
        let mut qs = Vec::new();
        for (qi, &(u, v)) in raw.iter().enumerate() {
            let (mut a, mut b) = (u, v);
            if first[a] > first[b] {
                std::mem::swap(&mut a, &mut b);
            }
            let w = lca(a, b);
            let (l, r) = if w == a {
                (first[a], first[b])
            } else {
                (last[a], first[b])
            };
            qs.push((l, r, qi, ()));
        }

        struct State {
            answers: Vec<u32>,
            acc: u32,
        }

        let state = mo_tree_paths(
            &et,
            lca,
            &mut qs,
            |qs| State {
                answers: vec![0; qs.len()],
                acc: 0,
            },
            // include node i in the xor
            |i, st: &mut State| {
                st.acc ^= values[et[i]];
            },
            // remove node i from the xor
            |i, st: &mut State| {
                st.acc ^= values[et[i]];
            },
            // record the xor for this query
            |_, _, qi, &(), st: &mut State| {
                st.answers[qi] = st.acc;
            },
        );

        // expected xors:
        // 0→2: 3 ^ 5 ^ 1 = 7
        // 1→3: 5 ^ 3 ^ 1 ^ 7 =  (path is 1–0–2–3) = 5^3=6, 6^1=7, 7^7=0? Wait:
        //   actually path 1–0–2–3: values [5,3,1,7] → 5^3=6, 6^1=7, 7^7=0
        // 0→3: 3 ^ 1 ^ 7 = (path 0–2–3) → 3^1=2, 2^7=5
        assert_eq!(state.answers, vec![2, 0, 5]);
    }
}
