/// returns (p, d)
/// add_edge takes \[u, v, i\], where (u, v) is the ith edge produced by es
/// update takes \[u, v, deg\[v\]\] where v = p\[u\]
pub fn xor_linked_tree<R: ?Sized, T: ?Sized, E>(
    n: usize,
    es: impl Iterator<Item = E>,
    mut to: impl FnMut(&E) -> (usize, usize),
    mut add_edge: impl FnMut(&E, &mut R),
    mut update: impl FnMut([usize; 3], &mut R),
    data: &mut R,
) -> (Vec<usize>, Vec<usize>) {
    let (mut d, mut p) = (vec![0; n], vec![0; n]);
    for e in es {
        let (u, v) = to(&e);
        d[u] += 1;
        d[v] += 1;
        p[u] ^= v;
        p[v] ^= u;
        add_edge(&e, data);
    }
    d[0] = usize::MAX;
    for i in 0..n {
        let mut u = i;
        while d[u] == 1 {
            d[u] = 0;
            let v = p[u];
            update([u, v, d[v]], data);
            p[v] ^= u;
            d[v] -= 1;
            u = v;
        }
    }
    (p, d)
}

/// returns (p, ss, pos, dfs, depth)
/// add_edge takes an edge (u, v, deg\[u\], deg\[v\])
/// update takes (u, v, deg\[v\], ss\[u\], ss\[v\], idx)
/// where v = p\[u\], ss is subtree size, ss\[v\] is correct if deg\[v\] == 1
/// and idx is the dfs order index of u
pub fn xor_linked_tree_dfs<R: ?Sized, T: ?Sized, E>(
    n: usize,
    es: impl Iterator<Item = E>,
    to: impl FnMut(&E) -> (usize, usize),
    add_edge: impl FnMut(&E, &mut R),
    mut update: impl FnMut([usize; 6], &mut R),
    data: &mut R,
) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let (mut ss, mut dfs, mut depth) = (vec![1; n], vec![0; n], vec![0_usize; n]);
    let mut idx = n - 1;
    let (p, d) = xor_linked_tree::<_, T, _>(
        n,
        es,
        to,
        add_edge,
        |[u, v, d_v], data| {
            ss[v] += ss[u];
            update([u, v, d_v, ss[u], ss[v], idx], data);
            dfs[idx] = u;
            idx -= 1;
        },
        data,
    );
    let mut pos = d;
    pos.copy_from_slice(&ss);
    for i in 1..n {
        let u = dfs[i];
        let v = p[u];
        depth[u] = depth[v] + 1;
        (pos[u], pos[v]) = (pos[v], pos[v] - pos[u]);
    }
    for i in 0..n {
        pos[i] -= 1;
        dfs[pos[i]] = i;
    }
    (p, ss, pos, dfs, depth)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Capture the calls to `add_edge` and `update` in xor_linked_tree.
    struct TestData1 {
        pub add_calls: Vec<[usize; 2]>,
        pub update_calls: Vec<[usize; 3]>,
    }

    #[test]
    fn test_xor_linked_tree_closure_calls() {
        // Build a small 5-node tree:
        //      0
        //     / \
        //    1   2
        //   / \
        //  3   4
        let n = 5;
        let edges = vec![[0, 1], [0, 2], [1, 3], [1, 4]];

        let mut data = TestData1 {
            add_calls: Vec::new(),
            update_calls: Vec::new(),
        };

        // Run xor_linked_tree, recording closures into `data`.
        let (_p, _d) = xor_linked_tree::<_, (), _>(
            n,
            edges.clone().into_iter(),
            |&[u, v]| (u, v),
            |e, data| data.add_calls.push(*e),
            |u, data| data.update_calls.push(u),
            &mut data,
        );

        // `add_edge` must be called once per edge, in the same order:
        assert_eq!(data.add_calls, edges);

        // The only leaves are 2, 3, 4 (in that index‐order), so
        // the first element of each `update` tuple (the removed u)
        // should be [2, 3, 4].
        let removed: Vec<usize> = data.update_calls.iter().map(|u| u[0]).collect();
        assert_eq!(removed, vec![2, 3, 4, 1]);
    }

    #[test]
    fn test_xor_linked_tree_dfs_properties() {
        // Same tree as above.
        let n = 5;
        let edges = vec![[0, 1], [0, 2], [1, 3], [1, 4]];

        // We don't care about the closures here, so use () and no‐ops.
        let (p, ss, pos, dfs, depth) = xor_linked_tree_dfs::<_, (), _>(
            n,
            edges.clone().into_iter(),
            |&[u, v]| (u, v),
            |_e, _| {},
            |_u, _| {},
            &mut (),
        );

        // Subtree sizes: root 0 has all 5, node 1 has its 3, and leaves 2/3/4 have 1.
        assert_eq!(ss, vec![5, 3, 1, 1, 1]);

        // Depths: 0 at depth 0; its children 1,2 at depth 1; 3,4 at depth 2.
        assert_eq!(depth, vec![0, 1, 1, 2, 2]);

        // Parent pointers: p[0] = 0 (root), p[1]=0, p[2]=0, p[3]=1, p[4]=1.
        assert_eq!(p, vec![0, 0, 0, 1, 1]);

        // The `dfs` and `pos` arrays must invert each other:
        for i in 0..n {
            assert_eq!(dfs[pos[i]], i, "dfs[pos[{}]] != {}", i, i);
        }
        println!("{:?}", dfs);
    }
}
