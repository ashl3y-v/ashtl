use crate::tree::cartesian::CartesianTree;

#[derive(Debug, Clone)]
pub struct SuffixTreeNode {
    pub l: usize,
    pub r: usize,
    pub h: usize,
    pub hh: usize,
}

impl SuffixTreeNode {
    pub fn new(l: usize, r: usize, h: usize, hh: usize) -> Self {
        Self { l, r, h, hh }
    }
}

#[derive(Clone, Debug)]
pub struct SuffixTree {
    pub nodes: Vec<SuffixTreeNode>,
    pub adj: Vec<Vec<(usize, usize)>>,
}

impl SuffixTree {
    /// O(n)
    pub fn new(sa: &[usize], lcp: &[usize]) -> Self {
        let n = sa.len();
        if n == 1 {
            let mut nodes = Vec::new();
            let mut adj = Vec::new();
            nodes.push(SuffixTreeNode {
                l: 0,
                r: 1,
                h: 0,
                hh: 1,
            });
            nodes.push(SuffixTreeNode {
                l: 0,
                r: 1,
                h: 1,
                hh: 2,
            });
            adj.push(vec![(1, 1)]);
            adj.push(vec![]);
            return Self { nodes, adj };
        }
        let mut nodes = Vec::new();
        let mut adj = Vec::new();
        nodes.push(SuffixTreeNode::new(0, n, 0, 1));
        adj.push(Vec::new());
        let ct = CartesianTree::with_direction(lcp, true);
        struct Context<'a> {
            nodes: &'a mut Vec<SuffixTreeNode>,
            adj: &'a mut Vec<Vec<(usize, usize)>>,
            ct: &'a CartesianTree<usize>,
            sa: &'a [usize],
            lcp: &'a [usize],
            n: usize,
        }
        fn dfs(ctx: &mut Context, mut p: usize, idx: usize, h: usize) {
            let l_range = ctx.ct.range[idx].0;
            let r_range = ctx.ct.range[idx].1 + 1;
            let hh = ctx.lcp[idx] as usize;
            if h < hh {
                let new_node_idx = ctx.nodes.len();
                ctx.adj[p].push((new_node_idx, hh - h));
                p = new_node_idx;
                ctx.nodes
                    .push(SuffixTreeNode::new(l_range, r_range, h + 1, hh + 1));
                ctx.adj.push(Vec::new());
            }
            if ctx.ct.lch[idx] == usize::MAX {
                let suffix_len = (ctx.n - ctx.sa[idx]) as usize;
                if hh < suffix_len {
                    let new_node_idx = ctx.nodes.len();
                    ctx.adj[p].push((new_node_idx, suffix_len - hh));
                    ctx.nodes
                        .push(SuffixTreeNode::new(idx, idx + 1, hh + 1, suffix_len + 1));
                    ctx.adj.push(Vec::new());
                }
            } else {
                dfs(ctx, p, ctx.ct.lch[idx], hh);
            }
            if ctx.ct.rch[idx] == usize::MAX {
                let suffix_len = (ctx.n - ctx.sa[idx + 1]) as usize;
                if hh < suffix_len {
                    let new_node_idx = ctx.nodes.len();
                    ctx.adj[p].push((new_node_idx, suffix_len - hh));
                    ctx.nodes.push(SuffixTreeNode::new(
                        idx + 1,
                        idx + 2,
                        hh + 1,
                        suffix_len + 1,
                    ));
                    ctx.adj.push(Vec::new());
                }
            } else {
                dfs(ctx, p, ctx.ct.rch[idx], hh);
            }
        }
        let r_idx = ct.root;
        let mut ctx = Context {
            nodes: &mut nodes,
            adj: &mut adj,
            ct: &ct,
            sa,
            lcp,
            n,
        };
        let lcp_r = lcp[r_idx] as usize;
        if lcp.len() > 0 && lcp_r > 0 {
            ctx.adj[0].push((1, lcp_r));
            ctx.nodes.push(SuffixTreeNode::new(0, n, 1, lcp_r + 1));
            ctx.adj.push(Vec::new());
            dfs(&mut ctx, 1, r_idx, lcp_r);
        } else {
            dfs(&mut ctx, 0, r_idx, 0);
        }
        Self { nodes, adj }
    }

    pub fn next<T: PartialEq>(
        &self,
        sa: &[usize],
        s: &[T],
        state: Option<(usize, usize)>,
        ch: &T,
    ) -> Option<(usize, usize)> {
        let (node, length) = state?;
        let node_data = &self.nodes[node];
        if length + 1 < node_data.hh {
            if ch != &s[sa[node_data.l] + length] {
                return None;
            }
            return Some((node, length + 1));
        }
        for &(child, _) in &self.adj[node] {
            let child_data = &self.nodes[child];
            let i = sa[child_data.l];
            if ch == &s[i + length] {
                return Some((child, length + 1));
            }
        }
        None
    }
}
