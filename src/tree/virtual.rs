use crate::ds::sort::counting_sort_dedup_by_key;

// O(n + |key| f(n)) if f(n) is the cost of calling lca
// Thus total including building LCA with O(1) / O(n) lca will be O(n + |key|) = O(n)
pub fn vtree(
    n: usize,
    key: &mut [usize],
    vs: &mut Vec<usize>,
    vadj: &mut [Vec<usize>],
    pos: &[usize],
    mut lca: impl FnMut(usize, usize) -> usize,
) {
    vs.clear();
    if key.is_empty() {
        return;
    }
    let z = counting_sort_dedup_by_key(key, n, |&v| pos[v]);
    vs.truncate(z);
    vs.resize(key.len(), 0);
    vs.copy_from_slice(key);
    for i in 1..key.len() {
        vs.push(lca(key[i - 1], key[i]));
    }
    let z = counting_sort_dedup_by_key(vs, n, |&v| pos[v]);
    vs.truncate(z);
    for &v in &*vs {
        vadj[v].clear();
    }
    for i in 1..vs.len() {
        vadj[lca(vs[i - 1], vs[i])].push(vs[i]);
    }
}

#[cfg(test)]
mod tests {
    use super::{super::ancestor::LCA, vtree};
    use std::cmp::Ordering;

    /// Helper to build an LCA instance given p, dfs, pos, depth
    fn make_lca<'a>(
        p: &'a [usize],
        dfs: &'a [usize],
        pos: &'a [usize],
        depth: &'a [usize],
    ) -> LCA<'a, impl FnMut(usize, usize) -> Ordering> {
        let cmp = move |i: usize, j: usize| depth[dfs[i]].cmp(&depth[dfs[j]]);
        LCA::new(dfs.len(), p, dfs, pos, cmp)
    }

    #[test]
    fn test_vtree_empty() {
        let mut key = vec![];
        let mut vs = Vec::new();
        let mut vadj = vec![vec![]];
        vtree(1, &mut key, &mut vs, &mut vadj, &[0], |_, _| unreachable!());
        assert!(vs.is_empty());
        assert_eq!(vadj, vec![vec![]]);
    }

    #[test]
    fn test_vtree_chain() {
        let p = vec![0, 0, 1, 2];
        let depth = vec![0, 1, 2, 3];
        let dfs = vec![0, 1, 2, 3];
        let pos = vec![0, 1, 2, 3];
        let mut key = vec![3, 1];
        let mut vs = Vec::new();
        let mut vadj = vec![vec![]; 4];
        let mut inst = make_lca(&p, &dfs, &pos, &depth);
        let mut f = { |a, b| inst.query(a, b) };
        vtree(4, &mut key, &mut vs, &mut vadj, &pos, &mut f);
        assert_eq!(vs, vec![1, 3]);
        assert_eq!(vadj[1], vec![3]);
    }

    #[test]
    fn test_vtree_balanced() {
        let p = vec![0, 0, 0, 1, 1, 2, 2];
        let depth = vec![0, 1, 1, 2, 2, 2, 2];
        let dfs = vec![0, 1, 3, 4, 2, 5, 6];
        let mut pos = vec![0; dfs.len()];
        for i in 0..dfs.len() {
            pos[dfs[i]] = i;
        }
        let mut key = vec![3, 5, 4];
        let mut vs = Vec::new();
        let mut vadj = vec![vec![]; 7];
        let mut inst = make_lca(&p, &dfs, &pos, &depth);
        let mut f = { |a, b| inst.query(a, b) };
        vtree(7, &mut key, &mut vs, &mut vadj, &pos, &mut f);
        assert_eq!(vs, vec![0, 1, 3, 4, 5]);
        assert_eq!(vadj[0], vec![1, 5]);
        assert_eq!(vadj[1], vec![3, 4]);
    }
}
