#[derive(Clone, PartialEq, Default, Debug)]
pub struct DominatorTree {
    pub idom: Vec<usize>,
}

impl DominatorTree {
    /// O((n + m) log n)
    pub fn new(adj: &[Vec<usize>], root: usize) -> Self {
        let n = adj.len();
        const UNSET: usize = usize::MAX;
        let mut tin = vec![UNSET; n];
        let mut par = vec![UNSET; n];
        let mut rev = vec![UNSET; n];
        let mut sdom = vec![UNSET; n];
        let mut dom = vec![UNSET; n];
        let mut dsu = vec![0; n];
        let mut lbl = vec![0; n];
        let mut h = vec![vec![]; n];
        let mut t = 0;
        fn dfs(
            u: usize,
            t: &mut usize,
            adj: &[Vec<usize>],
            arr: &mut [usize],
            rev: &mut [usize],
            lbl: &mut [usize],
            sdom: &mut [usize],
            dsu: &mut [usize],
            par: &mut [usize],
            h: &mut [Vec<usize>],
        ) {
            arr[u] = *t;
            rev[*t] = u;
            lbl[*t] = *t;
            sdom[*t] = *t;
            dsu[*t] = *t;
            *t += 1;
            for &w in &adj[u] {
                if arr[w] == UNSET {
                    dfs(w, t, adj, arr, rev, lbl, sdom, dsu, par, h);
                    par[arr[w]] = arr[u];
                }
                h[arr[w]].push(arr[u]);
            }
        }
        dfs(
            root, &mut t, adj, &mut tin, &mut rev, &mut lbl, &mut sdom, &mut dsu, &mut par, &mut h,
        );
        for i in 0..n {
            dom[i] = i;
        }
        let mut bkt = vec![vec![]; n];
        fn find(u: usize, x: bool, dsu: &mut [usize], lbl: &mut [usize], sdom: &[usize]) -> usize {
            if u == dsu[u] {
                return if x { UNSET } else { u };
            }
            let v = find(dsu[u], true, dsu, lbl, sdom);
            if v == UNSET {
                return u;
            }
            if sdom[lbl[dsu[u]]] < sdom[lbl[u]] {
                lbl[u] = lbl[dsu[u]];
            }
            dsu[u] = v;
            if x { v } else { lbl[u] }
        }
        for i in (0..t).rev() {
            for &w in &h[i] {
                let v = find(w, false, &mut dsu, &mut lbl, &sdom);
                if sdom[v] < sdom[i] {
                    sdom[i] = sdom[v];
                }
            }
            if i != 0 {
                bkt[sdom[i]].push(i);
            }
            let bucket_nodes = std::mem::take(&mut bkt[i]);
            for w in bucket_nodes {
                let v = find(w, false, &mut dsu, &mut lbl, &sdom);
                if sdom[v] == sdom[w] {
                    dom[w] = sdom[w];
                } else {
                    dom[w] = v;
                }
            }
            if i > 1 {
                dsu[i] = par[i];
            }
        }
        for i in 1..t {
            if dom[i] != sdom[i] {
                dom[i] = dom[dom[i]];
            }
        }
        let mut idom = vec![UNSET; n];
        for i in 1..t {
            idom[rev[i]] = rev[dom[i]];
        }
        if t > 0 {
            idom[root] = root;
        }
        Self { idom }
    }
}
