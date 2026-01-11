use crate::ds::bit_vec::BitVec;
use crate::tree::cartesian::CartesianTree;

#[derive(Clone, Debug)]
pub struct SuffixArray {
    pub sa: Vec<usize>,
}

impl SuffixArray {
    /// O(n + Σ)
    pub fn new(raw_s: &[u8]) -> Self {
        let n = raw_s.len();
        let mut s = Vec::with_capacity(n + 1);
        let min_val = *raw_s.iter().min().unwrap_or(&0);
        let max_val = *raw_s.iter().max().unwrap_or(&0);
        for &c in raw_s {
            s.push((c - min_val + 1) as usize);
        }
        s.push(0);
        let sigma = (max_val - min_val + 2) as usize;
        let mut sa = vec![0; n + 1];
        Self::sa_is(&s, &mut sa, sigma);
        Self { sa: sa[1..].into() }
    }

    fn get_types(s: &[usize], ty: &mut [u8]) {
        let n = s.len() - 1;
        ty[n] = 1;
        for i in (0..n).rev() {
            if s[i] < s[i + 1] {
                ty[i] = 1;
            } else if s[i] > s[i + 1] {
                ty[i] = 0;
            } else {
                ty[i] = ty[i + 1];
            }
        }
    }

    fn lms_equal(s: &[usize], ty: &[u8], mut x: usize, mut y: usize) -> bool {
        if s[x] != s[y] {
            return false;
        }
        loop {
            x += 1;
            y += 1;
            if s[x] != s[y] || ty[x] != ty[y] {
                return false;
            }
            if ty[x] == 2 {
                return true;
            }
        }
    }

    fn induced_sort(s: &[usize], sa: &mut [usize], ty: &[u8], lms: &[usize], sigma: usize) {
        let n = s.len();
        let mut cnt = vec![0; sigma + 1];
        for &x in s {
            cnt[x] += 1;
        }
        let mut bucket_ends = vec![0; sigma + 1];
        let mut bkt = vec![0; sigma + 1];
        let mut sum = 0;
        for i in 0..=sigma {
            bkt[i] = sum;
            sum += cnt[i];
            bucket_ends[i] = sum;
        }
        sa.fill(0);
        let mut bkt_p = bucket_ends.clone();
        for &idx in lms.iter().rev() {
            let ch = s[idx];
            bkt_p[ch] -= 1;
            sa[bkt_p[ch]] = idx;
        }
        for i in 0..n {
            let idx = sa[i];
            if idx > 0 {
                let prev = idx - 1;
                if ty[prev] == 0 {
                    let ch = s[prev];
                    sa[bkt[ch]] = prev;
                    bkt[ch] += 1;
                }
            }
        }
        let mut bkt = bucket_ends;
        for i in (0..n).rev() {
            let idx = sa[i];
            if idx > 0 {
                let prev = idx - 1;
                if ty[prev] >= 1 {
                    let ch = s[prev];
                    bkt[ch] -= 1;
                    sa[bkt[ch]] = prev;
                }
            }
        }
    }

    /// O(n + Σ)
    pub fn sa_is(s: &[usize], sa: &mut [usize], sigma: usize) {
        let n = s.len();
        let mut ty = vec![0u8; n];
        Self::get_types(s, &mut ty);
        let mut lms = Vec::with_capacity(n / 2);
        for i in 1..n {
            if ty[i] == 1 && ty[i - 1] == 0 {
                ty[i] = 2;
                lms.push(i);
            }
        }
        Self::induced_sort(s, sa, &ty, &lms, sigma);
        let mut sorted_lms = Vec::with_capacity(lms.len());
        for &idx in sa.iter() {
            if ty[idx] == 2 {
                sorted_lms.push(idx);
            }
        }
        let mut reduced_s = vec![0; lms.len()];
        let mut map_pos = vec![0; n];
        if !sorted_lms.is_empty() {
            reduced_s[0] = 0;
            for i in 0..sorted_lms.len() {
                let curr = sorted_lms[i];
                map_pos[curr] = i;
            }
        }
        let mut actual_reduced_s = Vec::with_capacity(lms.len());
        let mut current_name = 0;
        let mut names = vec![0; n];
        if !sorted_lms.is_empty() {
            names[sorted_lms[0]] = 0;
            for i in 1..sorted_lms.len() {
                let prev = sorted_lms[i - 1];
                let curr = sorted_lms[i];
                if !Self::lms_equal(s, &ty, prev, curr) {
                    current_name += 1;
                }
                names[curr] = current_name;
            }
        }
        for &idx in &lms {
            actual_reduced_s.push(names[idx]);
        }
        let mut reduced_sa = vec![0; actual_reduced_s.len()];
        if current_name + 1 < lms.len() {
            Self::sa_is(&actual_reduced_s, &mut reduced_sa, current_name);
        } else {
            for (i, &x) in actual_reduced_s.iter().enumerate() {
                reduced_sa[x] = i;
            }
        }
        let mut lms_remapped = Vec::with_capacity(lms.len());
        for &idx in &reduced_sa {
            lms_remapped.push(lms[idx]);
        }
        Self::induced_sort(s, sa, &ty, &lms_remapped, sigma);
    }

    /// O(n)
    pub fn lcp<T: PartialEq>(&self, s: &[T]) -> Vec<usize> {
        let n = s.len();
        let mut lcp = vec![0; n];
        let mut rank = vec![0; n];
        for i in 0..n {
            rank[self.sa[i]] = i;
        }
        let mut k = 0;
        for i in 0..n {
            if rank[i] == n - 1 {
                k = 0;
                continue;
            }
            if k > 0 {
                k -= 1;
            }
            let j = self.sa[rank[i] + 1];
            while i + k < n && j + k < n && s[i + k] == s[j + k] {
                k += 1;
            }
            lcp[rank[i]] = k;
        }
        lcp.truncate(n - 1);
        lcp
    }
}

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
        let mut adj = vec![Vec::new(); n + 1];
        nodes.push(SuffixTreeNode::new(0, n, 0, 1));
        let ct = CartesianTree::with_direction(lcp, true);
        struct Context<'a> {
            dat: &'a mut Vec<SuffixTreeNode>,
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
                let new_node_idx = ctx.dat.len();
                ctx.adj[p].push((new_node_idx, hh - h));
                p = new_node_idx;
                ctx.dat
                    .push(SuffixTreeNode::new(l_range, r_range, h + 1, hh + 1));
            }
            if ctx.ct.lch[idx] == usize::MAX {
                let suffix_len = (ctx.n - ctx.sa[idx]) as usize;
                if hh < suffix_len {
                    let new_node_idx = ctx.dat.len();
                    ctx.adj[p].push((new_node_idx, suffix_len - hh));
                    ctx.dat
                        .push(SuffixTreeNode::new(idx, idx + 1, hh + 1, suffix_len + 1));
                }
            } else {
                dfs(ctx, p, ctx.ct.lch[idx], hh);
            }
            if ctx.ct.rch[idx] == usize::MAX {
                let suffix_len = (ctx.n - ctx.sa[idx + 1]) as usize;
                if hh < suffix_len {
                    let new_node_idx = ctx.dat.len();
                    ctx.adj[p].push((new_node_idx, suffix_len - hh));
                    ctx.dat.push(SuffixTreeNode::new(
                        idx + 1,
                        idx + 2,
                        hh + 1,
                        suffix_len + 1,
                    ));
                }
            } else {
                dfs(ctx, p, ctx.ct.rch[idx], hh);
            }
        }
        let r_idx = ct.root;
        let mut ctx = Context {
            dat: &mut nodes,
            adj: &mut adj,
            ct: &ct,
            sa,
            lcp,
            n,
        };
        if lcp.len() > 0 && lcp[r_idx] > 0 {
            let lcp_r = lcp[r_idx] as usize;
            ctx.adj[0].push((1, lcp_r));
            ctx.dat.push(SuffixTreeNode::new(0, n, 1, lcp_r + 1));
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

    pub fn get_suffix_positions(&self, sa: &[usize]) -> Vec<usize> {
        let n = sa.len();
        let mut bv = BitVec::new(n, true);
        let mut ans = vec![0; n];
        for v in (0..self.nodes.len()).rev() {
            let node = &self.nodes[v];
            let mut i = bv.next(node.l);
            while let Some(idx) = i {
                if idx >= node.r {
                    break;
                }
                bv.remove(idx);
                ans[sa[idx]] = v;
                i = bv.next(idx + 1);
            }
        }
        ans
    }
}

#[derive(Debug, Clone)]
pub struct SuffixAutomatonNode<const SIGMA: usize> {
    pub next: [usize; SIGMA],
    pub link: usize,
    pub len: usize,
}

impl<const SIGMA: usize> SuffixAutomatonNode<SIGMA> {
    fn new(link: usize, len: usize) -> Self {
        Self {
            next: [usize::MAX; SIGMA],
            link,
            len,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SuffixAutomaton<const SIGMA: usize> {
    pub nodes: Vec<SuffixAutomatonNode<SIGMA>>,
    pub last: usize,
}

impl<const SIGMA: usize> SuffixAutomaton<SIGMA> {
    pub fn new() -> Self {
        Self {
            nodes: vec![SuffixAutomatonNode::new(usize::MAX, 0)],
            last: 0,
        }
    }

    pub fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        let mut sa = Self::new();
        for c in iter {
            sa.add(c);
        }
        sa
    }

    pub fn add(&mut self, c: usize) {
        debug_assert!(c < SIGMA);
        let new_node = self.nodes.len();
        self.nodes.push(SuffixAutomatonNode::new(
            usize::MAX,
            self.nodes[self.last].len + 1,
        ));
        let mut p = self.last;
        while p != usize::MAX && self.nodes[p].next[c] == usize::MAX {
            self.nodes[p].next[c] = new_node;
            p = self.nodes[p].link;
        }
        let q = if p == usize::MAX {
            0
        } else {
            self.nodes[p].next[c]
        };
        if p == usize::MAX || self.nodes[p].len + 1 == self.nodes[q].len {
            self.nodes[new_node].link = q;
        } else {
            let new_q = self.nodes.len();
            self.nodes.push(SuffixAutomatonNode::new(
                self.nodes[q].link,
                self.nodes[p].len + 1,
            ));
            self.nodes[new_q].next = self.nodes[q].next;
            self.nodes[q].link = new_q;
            self.nodes[new_node].link = new_q;
            while p != usize::MAX && self.nodes[p].next[c] == q {
                self.nodes[p].next[c] = new_q;
                p = self.nodes[p].link;
            }
        }
        self.last = new_node;
    }

    pub fn calc_dag(&self) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut adj = vec![Vec::new(); n];
        for (v, node) in self.nodes.iter().enumerate() {
            for &to in &node.next {
                if to != usize::MAX {
                    adj[v].push(to);
                }
            }
        }
        adj
    }

    pub fn calc_link_tree(&self) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut adj = vec![Vec::new(); n];
        for v in 1..n {
            let p = self.nodes[v].link;
            if p != usize::MAX {
                adj[p].push(v);
            }
        }
        adj
    }

    pub fn count_substring_at(&self, p: usize) -> usize {
        if p == 0 {
            return 0;
        }
        self.nodes[p].len - self.nodes[self.nodes[p].link].len
    }

    pub fn count_substrings(&self) -> usize {
        (0..self.nodes.len())
            .map(|i| self.count_substring_at(i))
            .sum()
    }
}
