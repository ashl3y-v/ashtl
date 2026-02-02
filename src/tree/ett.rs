use std::collections::HashMap;

use rand::{Rng, rngs::ThreadRng};

#[derive(Clone, Default, Debug)]
struct ETTNode {
    l: usize,
    r: usize,
    p: usize,
    pri: u64,
}

pub struct ETT {
    nodes: Vec<ETTNode>,
    adj: Vec<HashMap<usize, usize>>,
    rng: ThreadRng,
}

impl ETT {
    pub fn new(n: usize) -> Self {
        let mut nodes = Vec::with_capacity(n * 2 + 10);
        nodes.push(ETTNode::default());
        let mut adj = Vec::with_capacity(n + 1);
        for _ in 0..=n {
            adj.push(HashMap::new());
        }
        Self {
            nodes,
            adj,
            rng: rand::rng(),
        }
    }

    fn get_root(&self, mut x: usize) -> usize {
        while self.nodes[x].p != 0 {
            x = self.nodes[x].p;
        }
        x
    }

    fn link(&mut self, x: usize, d: usize, y: usize) {
        if d == 0 {
            self.nodes[x].l = y;
        } else {
            self.nodes[x].r = y;
        }
        if y != 0 {
            self.nodes[y].p = x;
        }
    }

    fn dis(&mut self, x: usize, d: usize) -> usize {
        let y = if d == 0 {
            self.nodes[x].l
        } else {
            self.nodes[x].r
        };
        if d == 0 {
            self.nodes[x].l = 0;
        } else {
            self.nodes[x].r = 0;
        }
        if y != 0 {
            self.nodes[y].p = 0;
        }
        y
    }

    fn split(&mut self, x: usize) -> (usize, usize) {
        let mut left = self.dis(x, 0);
        let mut right = x;
        let mut curr = x;
        while self.nodes[curr].p != 0 {
            let p = self.nodes[curr].p;
            if self.nodes[p].l == curr {
                self.dis(p, 0);
                self.link(p, 0, right);
                right = p;
            } else {
                self.dis(p, 1);
                self.link(p, 1, left);
                left = p;
            }
            curr = p;
        }
        (left, right)
    }

    fn merge(&mut self, x: usize, y: usize) -> usize {
        if x == 0 || y == 0 {
            return if x != 0 { x } else { y };
        }
        if self.nodes[x].pri > self.nodes[y].pri {
            let rc = self.dis(x, 1);
            let merged = self.merge(rc, y);
            self.link(x, 1, merged);
            x
        } else {
            let lc = self.dis(y, 0);
            let merged = self.merge(x, lc);
            self.link(y, 0, merged);
            y
        }
    }

    fn make_first(&mut self, x: usize) -> usize {
        if x == 0 {
            return 0;
        }
        let (left, right) = self.split(x);
        self.merge(right, left)
    }

    fn rem_first(&mut self, mut x: usize) {
        if x == 0 {
            return;
        }
        while self.nodes[x].l != 0 {
            x = self.nodes[x].l;
        }
        let y = self.dis(x, 1);
        let p = self.nodes[x].p;
        if p != 0 {
            self.dis(p, 0);
            self.link(p, 0, y);
        }
    }

    fn make_edge_node(&mut self, u: usize, v: usize) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(ETTNode {
            l: 0,
            r: 0,
            p: 0,
            pri: self.rng.random(),
        });
        self.adj[u].insert(v, idx);
        idx
    }

    fn reroot(&mut self, u: usize) -> usize {
        if let Some(&edge_idx) = self.adj[u].values().next() {
            self.make_first(edge_idx)
        } else {
            0
        }
    }

    /// O(log n)
    pub fn add(&mut self, u: usize, v: usize) {
        let root_u = self.reroot(u);
        let root_v = self.reroot(v);
        let node_uv = self.make_edge_node(u, v);
        let node_vu = self.make_edge_node(v, u);
        let temp = self.merge(root_u, node_uv);
        let temp = self.merge(temp, root_v);
        self.merge(temp, node_vu);
    }

    /// O(log n)
    pub fn rem(&mut self, u: usize, v: usize) {
        let val_uv = *self.adj[u].get(&v).expect("Edge does not exist");
        let val_vu = *self.adj[v].get(&u).expect("Edge does not exist");
        self.make_first(val_uv);
        let (left, right) = self.split(val_vu);
        self.rem_first(left);
        self.rem_first(right);
        self.adj[u].remove(&v);
        self.adj[v].remove(&u);
    }

    /// O(log n)
    pub fn con(&mut self, u: usize, v: usize) -> bool {
        if u == v {
            return true;
        } else if self.adj[u].is_empty() || self.adj[v].is_empty() {
            return false;
        }
        let u_edge = *self.adj[u].values().next().unwrap();
        let v_edge = *self.adj[v].values().next().unwrap();
        self.get_root(u_edge) == self.get_root(v_edge)
    }
}
