// TODO: improve
// https://codeforces.com/blog/entry/80145
// https://codeforces.com/blog/entry/75885
// https://codeforces.com/blog/entry/67637
// https://judge.yosupo.jp/submission/270678
// https://judge.yosupo.jp/submission/278245

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [Node<T>]),
    Push: FnMut([usize; 3], &mut [Node<T>]),
    Rev: FnMut(usize, &mut [Node<T>]),
{
    pub n: Vec<Node<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
}

impl<T, Push, Pull, Rev> LCT<T, Push, Pull, Rev>
where
    Pull: FnMut([usize; 3], &mut [Node<T>]),
    Push: FnMut([usize; 3], &mut [Node<T>]),
    Rev: FnMut(usize, &mut [Node<T>]),
{
    pub fn new(init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        Self {
            n: vec![Node {
                v: init,
                p: 0,
                ch: [0; 2],
                rev: false,
                k: -1,
            }],
            pull,
            push,
            rev,
        }
    }

    pub fn with_capacity(capacity: usize, init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        let mut nodes = Vec::with_capacity(capacity + 1);
        nodes.push(Node {
            v: init,
            p: 0,
            ch: [0; 2],
            rev: false,
            k: -1,
        });
        Self {
            n: nodes,
            pull,
            push,
            rev,
        }
    }

    pub fn add_node(&mut self, v: T) -> usize {
        self.n.push(Node {
            v,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        self.n.len() - 2
    }

    fn reverse(&mut self, x: usize) {
        if x != 0 {
            self.n[x].rev ^= true;
            (self.rev)(x, &mut self.n);
        }
    }

    fn push(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [mut ch0, mut ch1] = self.n[x].ch;
        if self.n[x].rev {
            self.n[x].ch.swap(0, 1);
            (ch0, ch1) = (ch1, ch0);
            self.n[ch0].k = 0;
            self.n[ch1].k = 1;
            self.reverse(ch0);
            self.reverse(ch1);
            self.n[x].rev = false;
        }
        (self.push)([x, ch0, ch1], &mut self.n);
    }

    fn pull(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [ch0, ch1] = self.n[x].ch;
        (self.pull)([x, ch0, ch1], &mut self.n);
    }

    fn rot(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let p = self.n[x].p;
        if p == 0 {
            return;
        }
        let g = self.n[p].p;
        let k = self.n[x].k as usize;
        let t = self.n[p].k;
        let child = self.n[x].ch[k ^ 1];
        self.n[child].p = p;
        self.n[child].k = k as i8;
        self.n[p].ch[k] = child;
        self.n[p].p = x;
        self.n[p].k = (k ^ 1) as i8;
        self.n[x].ch[k ^ 1] = p;
        self.n[x].p = g;
        self.n[x].k = t;
        if t != -1 {
            self.n[g].ch[t as usize] = x;
        }
        self.pull(p);
    }

    #[inline]
    fn is_root(&self, x: usize) -> bool {
        self.n[x].k == -1
    }

    fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.push(x);
        while !self.is_root(x) {
            let p = self.n[x].p;
            if self.is_root(p) {
                self.push(p);
                self.push(x);
                self.rot(x);
            } else {
                let g = self.n[p].p;
                self.push(g);
                self.push(p);
                self.push(x);
                if self.n[x].k == self.n[p].k {
                    self.rot(p);
                    self.rot(x);
                } else {
                    self.rot(x);
                    self.rot(x);
                }
            }
        }
    }

    fn access(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.splay(x);
        let [_, ch1] = self.n[x].ch;
        self.n[ch1].k = -1;
        self.n[x].ch[1] = 0;
        while self.n[x].p != 0 {
            let p = self.n[x].p;
            self.splay(p);
            let [_, ch1] = self.n[p].ch;
            self.n[ch1].k = -1;
            self.n[p].ch[1] = x;
            self.n[x].k = 1;
            self.rot(x);
        }
    }

    #[inline]
    fn make_root(&mut self, x: usize) {
        self.access(x);
        self.reverse(x);
    }

    #[inline]
    pub fn link(&mut self, mut w: usize, mut x: usize) {
        w += 1;
        x += 1;
        self.make_root(w);
        self.n[w].p = x;
    }

    pub fn cut(&mut self, mut u: usize, mut v: usize) {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        let [ch0, _] = self.n[v].ch;
        self.n[ch0].p = 0;
        self.n[ch0].k = -1;
        self.n[v].ch[0] = 0;
        self.pull(v);
    }

    pub fn update<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [Node<T>]) -> R,
    ) -> R {
        u += 1;
        self.splay(u);
        f(u, self.n[u].ch, &mut self.n)
    }

    pub fn query_root<R>(
        &mut self,
        mut u: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [Node<T>]) -> R,
    ) -> R {
        u += 1;
        self.make_root(u);
        f(u, self.n[u].ch, &mut self.n)
    }

    pub fn query<R>(
        &mut self,
        mut u: usize,
        mut v: usize,
        mut f: impl FnMut(usize, [usize; 2], usize, [usize; 2], &mut [Node<T>]) -> R,
    ) -> R {
        u += 1;
        v += 1;
        self.make_root(u);
        self.access(v);
        f(u, self.n[u].ch, v, self.n[v].ch, &mut self.n)
    }

    pub fn conn(&mut self, mut u: usize, mut v: usize) -> bool {
        u += 1;
        v += 1;
        if u == v {
            true
        } else {
            self.make_root(u);
            self.access(v);
            self.n[u].p != 0
        }
    }

    #[inline]
    pub fn parent(&mut self, mut v: usize, mut w: usize) {
        v += 1;
        w += 1;
        self.n[v].p = w;
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.n.len()
    }
}

// TODO: euler tour tree
// https://codeforces.com/blog/entry/128556

// TODO: top tree
// https://codeforces.com/blog/entry/103726
// https://codeforces.com/blog/entry/128556

#[cfg(test)]
mod tests {
    use super::*;

    fn create_simple_lct() -> LCT<
        i32,
        fn([usize; 3], &mut [Node<i32>]),
        fn([usize; 3], &mut [Node<i32>]),
        fn(usize, &mut [Node<i32>]),
    > {
        LCT::new(0, |_, _| {}, |_, _| {}, |_, _| {})
    }

    fn create_sum_lct() -> LCT<
        (i32, i32),
        fn([usize; 3], &mut [Node<(i32, i32)>]),
        fn([usize; 3], &mut [Node<(i32, i32)>]),
        fn(usize, &mut [Node<(i32, i32)>]),
    > {
        LCT::new(
            (0, 0),
            |[x, l, r], n| {
                n[x].v.1 = n[l].v.1 + n[r].v.1 + n[x].v.0;
            },
            |_, _| {},
            |_, _| {},
        )
    }

    #[test]
    fn test_basic_node_creation() {
        let mut lct = create_simple_lct();
        assert_eq!(lct.len(), 1); // Just dummy node
        let n1 = lct.add_node(10);
        let n2 = lct.add_node(20);
        let n3 = lct.add_node(30);
        assert_eq!(n1, 0);
        assert_eq!(n2, 1);
        assert_eq!(n3, 2);
        assert_eq!(lct.len(), 4);
        assert_eq!(lct.n[n1 + 1].v, 10);
        assert_eq!(lct.n[n2 + 1].v, 20);
        assert_eq!(lct.n[n3 + 1].v, 30);
    }

    #[test]
    fn test_single_node_connectivity() {
        let mut lct = create_simple_lct();
        let n1 = lct.add_node(42);
        assert_eq!(lct.conn(n1, n1), true);
    }

    #[test]
    fn test_two_isolated_nodes() {
        let mut lct = create_simple_lct();
        let n1 = lct.add_node(10);
        let n2 = lct.add_node(20);
        assert!(!lct.conn(n1, n2));
        assert!(!lct.conn(n2, n1));
    }

    #[test]
    fn test_basic_link_connectivity() {
        let mut lct = create_simple_lct();
        let n1 = lct.add_node(10);
        let n2 = lct.add_node(20);
        lct.link(n1, n2);
        assert!(lct.conn(n1, n2));
        assert!(lct.conn(n2, n1));
    }

    #[test]
    fn test_chain_connectivity() {
        let mut lct = create_simple_lct();
        let nodes: Vec<_> = (0..5).map(|i| lct.add_node(i * 10)).collect();
        for i in 1..5 {
            lct.link(nodes[i], nodes[i - 1]);
        }
        for i in 0..5 {
            for j in 0..5 {
                assert!(lct.conn(nodes[i], nodes[j]));
            }
        }
    }

    #[test]
    fn test_star_connectivity() {
        let mut lct = create_simple_lct();
        let center = lct.add_node(0);
        let leaves: Vec<_> = (1..=4).map(|i| lct.add_node(i * 10)).collect();

        // Create star: center connected to all leaves
        for &leaf in &leaves {
            lct.link(leaf, center);
        }

        // Center should be connected to all leaves
        for &leaf in &leaves {
            assert!(lct.conn(center, leaf));
        }

        // All leaves should be connected to each other through center
        for i in 0..leaves.len() {
            for j in 0..leaves.len() {
                assert!(lct.conn(leaves[i], leaves[j]));
            }
        }
    }

    #[test]
    fn test_cut_operation() {
        let mut lct = create_simple_lct();
        let n1 = lct.add_node(10);
        let n2 = lct.add_node(20);
        let n3 = lct.add_node(30);

        // Create chain: n1 - n2 - n3
        lct.link(n2, n1);
        lct.link(n3, n2);

        // All should be connected
        assert!(lct.conn(n1, n3));

        // Cut connection between n2 and n3
        lct.cut(n2, n3);

        // n1 and n2 should still be connected
        assert!(lct.conn(n1, n2));

        // n1 and n3 should no longer be connected
        assert!(!lct.conn(n1, n3));
        assert!(!lct.conn(n3, n1));

        // n2 and n3 should no longer be connected
        assert!(!lct.conn(n2, n3));
    }

    #[test]
    fn test_dynamic_tree_operations() {
        let mut lct = create_simple_lct();
        let nodes: Vec<_> = (0..6).map(|i| lct.add_node(i)).collect();

        // Initial tree: 0-1-2 and 3-4-5 (two components)
        lct.link(nodes[1], nodes[0]);
        lct.link(nodes[2], nodes[1]);
        lct.link(nodes[4], nodes[3]);
        lct.link(nodes[5], nodes[4]);

        // Components should be internally connected but not across
        assert!(lct.conn(nodes[0], nodes[2]));
        assert!(lct.conn(nodes[3], nodes[5]));
        assert!(!lct.conn(nodes[0], nodes[3]));

        // Connect the two components
        lct.link(nodes[2], nodes[3]);

        // Now all nodes should be connected
        for i in 0..6 {
            for j in 0..6 {
                assert!(lct.conn(nodes[i], nodes[j]));
            }
        }
    }

    #[test]
    fn test_large_chain() {
        let mut lct = create_simple_lct();
        let nodes: Vec<_> = (0..100).map(|i| lct.add_node(i)).collect();

        // Create long chain
        for i in 1..100 {
            lct.link(nodes[i], nodes[i - 1]);
        }

        // Test connectivity across the chain
        assert!(lct.conn(nodes[0], nodes[99]));
        assert!(lct.conn(nodes[25], nodes[75]));
    }

    #[test]
    fn test_complex_tree_structure() {
        let mut lct = create_simple_lct();

        // Create a more complex tree:
        //       0
        //      / \
        //     1   2
        //    /|   |\
        //   3 4   5 6
        //         |
        //         7

        let nodes: Vec<_> = (0..8).map(|i| lct.add_node(i * 10)).collect();

        // Build the tree structure
        lct.link(nodes[1], nodes[0]);
        lct.link(nodes[2], nodes[0]);
        lct.link(nodes[3], nodes[1]);
        lct.link(nodes[4], nodes[1]);
        lct.link(nodes[5], nodes[2]);
        lct.link(nodes[6], nodes[2]);
        lct.link(nodes[7], nodes[5]);

        // Test connectivity - all nodes should be connected
        for i in 0..8 {
            for j in 0..8 {
                assert!(lct.conn(nodes[i], nodes[j]));
            }
        }
    }

    #[test]
    fn test_sum_aggregation_with_connectivity() {
        let mut lct = create_sum_lct();

        let nodes: Vec<_> = (1..=5)
            .map(|i| {
                lct.add_node((i * 10, 0)) // (value, sum)
            })
            .collect();

        // Create path: n0 - n1 - n2 - n3 - n4
        for i in 1..5 {
            lct.link(nodes[i], nodes[i - 1]);
        }

        // Test connectivity
        assert!(lct.conn(nodes[0], nodes[4]));

        // Test path sum query
        let sum = lct.query(nodes[0], nodes[4], |_, _, v, [l, _], n| n[l].v.1 + n[v].v.0);

        // Should sum values from n0 to n4: 10 + 20 + 30 + 40 + 50 = 150
        assert_eq!(sum, 150);
    }

    #[test]
    fn test_with_capacity() {
        let mut lct = LCT::with_capacity(
            100,
            (0, 0),
            |[x, l, r], n| n[x].v.1 = n[l].v.1 + n[r].v.1 + n[x].v.0,
            |_, _| {},
            |_, _| {},
        );
        assert_eq!(lct.len(), 1); // Just dummy node initially

        // Add nodes up to capacity
        for i in 0..50 {
            let n = lct.add_node((i as i32, 0));
            assert_eq!(n, i);
        }

        assert_eq!(lct.len(), 51);

        // Test connectivity after capacity initialization
        lct.link(1, 2);
        lct.link(3, 2);

        assert!(lct.conn(1, 3));
        // assert_eq!(lct.lca(1, 3), 2);

        // Can still add more beyond initial capacity
        let n = lct.add_node((999, 0));
        assert_eq!(n, 50);

        let result = lct.query(n, n, |_, _, v, [l, _], n| n[l].v.1 + n[v].v.0);
        assert_eq!(result, 999);
        lct.link(n, 1);
        lct.cut(2, 1);
        lct.link(n, 2);

        let result = lct.query(2, n, |_, _, v, [l, _], n| n[l].v.1 + n[v].v.0);
        assert_eq!(result, 1001);
    }
}
