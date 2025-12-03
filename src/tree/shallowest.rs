/// O(n)
pub fn greedy_labelling(adj: &[Vec<usize>]) -> Vec<usize> {
    let n = adj.len();
    let mut forbidden = vec![0; n];
    fn dfs(u: usize, p: usize, adj: &[Vec<usize>], forbidden: &mut [usize]) {
        let mut forbidden_once = 0;
        let mut forbidden_twice = 0;
        for &v in &adj[u] {
            if v != p {
                dfs(v, u, adj, forbidden);
                let forbidden_by_v = forbidden[v] + 1;
                forbidden_twice |= forbidden_once & forbidden_by_v;
                forbidden_once |= forbidden_by_v;
            }
        }
        let mask = if forbidden_twice == 0 {
            0
        } else {
            (1 << forbidden_twice.ilog2() + 1) - 1
        };
        forbidden[u] = forbidden_once | mask;
    }
    dfs(0, usize::MAX, adj, &mut forbidden);
    forbidden
        .iter()
        .map(|&mask| (mask + 1).trailing_zeros() as usize)
        .collect()
}

// https://codeforces.com/blog/entry/125018
/// O(n)
pub fn shallowest_decomposition(
    adj: &[Vec<usize>],
    root: usize,
    mut f: impl FnMut([usize; 3], &mut [usize]),
) -> usize {
    let n = adj.len();
    let mut stacks: Vec<Vec<usize>> = vec![vec![]; n.ilog2() as usize + 1];
    let mut forbidden = vec![0; n];
    fn extract_chain(
        mut labels: usize,
        mut u: usize,
        stacks: &mut [Vec<usize>],
        forbidden: &mut [usize],
        f: &mut impl FnMut([usize; 3], &mut [usize]),
    ) {
        while labels != 0 {
            let label = labels.ilog2() as usize;
            labels ^= 1 << label;
            if let Some(v) = stacks[label].pop() {
                f([v, u, labels], forbidden);
                u = v;
            }
        }
    }
    fn dfs(
        u: usize,
        p: usize,
        adj: &[Vec<usize>],
        forbidden: &mut [usize],
        stacks: &mut [Vec<usize>],
        f: &mut impl FnMut([usize; 3], &mut [usize]),
    ) {
        let mut forbidden_once = 0;
        let mut forbidden_twice = 0;
        for &v in &adj[u] {
            if v != p {
                dfs(v, u, adj, forbidden, stacks, f);
                let forbidden_by_v = forbidden[v] + 1;
                forbidden_twice |= forbidden_once & forbidden_by_v;
                forbidden_once |= forbidden_by_v;
            }
        }
        let mask = if forbidden_twice == 0 {
            0
        } else {
            (1 << forbidden_twice.ilog2() + 1) - 1
        };
        forbidden[u] = forbidden_once | mask;
        let label = (forbidden[u] + 1).trailing_zeros() as usize;
        stacks[label].push(u);
        for &v in adj[u].iter().rev() {
            if v != p {
                let labels = (forbidden[v] + 1) & ((1 << label) - 1);
                extract_chain(labels, u, stacks, forbidden, f);
            }
        }
    }
    dfs(root, usize::MAX, adj, &mut forbidden, &mut stacks, &mut f);
    let max_label = (forbidden[root] + 1).ilog2() as usize;
    let decomposition_root = stacks[max_label].pop().unwrap();
    extract_chain(
        (forbidden[root] + 1) & ((1 << max_label) - 1),
        decomposition_root,
        &mut stacks,
        &mut forbidden,
        &mut f,
    );
    decomposition_root
}
