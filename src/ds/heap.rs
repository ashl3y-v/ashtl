// TODO: double ended priority queue
// https://judge.yosupo.jp/problem/double_ended_priority_queue

// TODO: persistent heap
// https://usaco.guide/adv/persistent?lang=cpp

const NULL: usize = usize::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<T> {
    pub v: T,
    pub s: usize,
    pub l: usize,
    pub r: usize,
}

impl<T> Node<T> {
    pub fn new(v: T, l: usize, r: usize, s: usize) -> Self {
        Node { v, s, l, r }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersistentHeap<T> {
    pub n: Vec<Node<T>>,
    pub rt: Vec<usize>,
    pub nxt: usize,
}

impl<T: Clone + Ord> PersistentHeap<T> {
    pub fn new() -> Self {
        Self {
            n: Vec::new(),
            rt: Vec::new(),
            nxt: 0,
        }
    }

    fn new_node(&mut self, node: Node<T>) -> usize {
        let nxt = self.nxt;
        if nxt < self.n.len() {
            self.n[nxt] = node;
        } else {
            self.n.push(node);
        }
        self.nxt += 1;
        nxt
    }

    fn restructure(&mut self, x: usize) {
        if x == NULL {
            return;
        }
        if self.n[self.n[x].l].s < self.n[self.n[x].r].s {
            (self.n[x].l, self.n[x].r) = (self.n[x].r, self.n[x].l);
        }
        self.n[x].s = self.n[self.n[x].r].s + 1;
    }

    fn meld(&mut self, mut p: usize, mut q: usize) -> usize {
        if p == NULL {
            return q;
        } else if q == NULL {
            return p;
        } else if self.n[p].v > self.n[q].v {
            (p, q) = (q, p);
        }
        let mut np = self.n[p].clone();
        let nr = self.meld(np.r, q);
        np.r = nr;
        let npr = self.new_node(np);
        self.restructure(npr);
        npr
    }

    pub fn insert(&mut self, v: T) -> usize {
        let r = self.root();
        let s = Node::new(v, NULL, NULL, 0);
        let sr = self.new_node(s);
        let r_new = self.meld(r, sr);
        self.rt.push(r_new);
        r_new
    }

    pub fn peek(&self, t: usize) -> &T {
        &self.n[self.rt[t]].v
    }

    pub fn pop(&mut self, t: usize) -> Option<(T, usize)> {
        if t >= self.rt.len() {
            return None;
        }
        let r = self.rt[t];
        let m = self.n[r].v.clone();
        let l = self.n[r].l;
        let r = self.n[r].r;
        let nr = self.meld(l, r);
        self.rt.push(nr);
        Some((m, nr))
    }

    #[inline]
    fn root(&self) -> usize {
        *self.rt.last().unwrap_or(&NULL)
    }

    pub fn time(&self) -> usize {
        self.rt.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn persistent_heap_operations_no_peek() {
        // Use the new constructor that handles the sentinel node
        let mut ph = PersistentHeap::<i32>::new();

        // Version 0: Empty (Initial State)
        assert_eq!(ph.time(), 0);
        // The only way to check the content is to pop and see what we get (None)
        assert!(ph.pop(0).is_none());

        // --- Operation 1: Insert 10 (Creates Version 1) ---
        let _v1_root = ph.insert(10); // Time = 1
        assert_eq!(ph.time(), 1);

        // Check V1: Pop from V1 (Creates V2)
        // Since V1 has only 10, the pop result must be 10.
        let (min_v1, _v2_root_after_pop) = ph.pop(0).unwrap();
        assert_eq!(min_v1, 10);

        // Restore the state for V2 (Time = 2) for the next fork
        let v2_root_orig = ph.rt[1];
        ph.rt.pop(); // Remove the test pop (V2 becomes V1)
        ph.rt.push(v2_root_orig); // Restore V2 (V2 is 10, 5)

        // --- Operation 2: Insert 5 (Creates Version 2) ---
        let _v2_root = ph.insert(5); // Time = 2
        assert_eq!(ph.time(), 3);

        // Check V2: Pop from V2 (Creates V3)
        let (min_v2, _v3_root_after_pop) = ph.pop(2).unwrap();
        assert_eq!(min_v2, 5);

        // Restore the state for V3 (Time = 3) for the next fork
        let v3_root_orig = ph.rt[3];
        ph.rt.pop();
        ph.rt.push(v3_root_orig);

        // --- Operation 3: Insert 15 (Creates Version 3) ---
        let v3_root = ph.insert(15); // Time = 3
        assert_eq!(ph.time(), 5);

        // Check V3: Pop from V3 (Creates V4)
        let (min_v3, v4_root) = ph.pop(3).unwrap();
        assert_eq!(min_v3, 5); // Minimum is 5
        assert_eq!(ph.time(), 4);

        // --- Check Persistence (Forking from V3) ---

        // Check V3: Pop from V3 again (Creates V7). Must still yield 5.
        let (min_v3_recheck, _v7_root) = ph.pop(3).unwrap();
        assert_eq!(min_v3_recheck, 5);
        assert_eq!(ph.time(), 7);

        // Check V4: Pop from V4 again (Creates V8). Must still yield 10.
        let (min_v4_recheck, _v8_root) = ph.pop(4).unwrap();
        assert_eq!(min_v4_recheck, 10);
        assert_eq!(ph.time(), 8);

        // --- Check Forking (Insert 2 into V2) ---

        // V2 is at index 2 (contains 10, 5). Min is 5.
        let v2_root_idx = ph.rt[2];

        // Manually implement an insert from an old version (creates V9)
        let singleton_node = Node::new(2, NULL, NULL, 1);
        let singleton_root = ph.new_node(singleton_node);
        let v9_root = ph.meld(v2_root_idx, singleton_root);
        ph.rt.push(v9_root); // Version 9 (V2 + 2)
        assert_eq!(ph.time(), 10);

        // Check V9: Pop from V9 (Creates V10). Must yield 2.
        let (min_v9, _v10_root) = ph.pop(9).unwrap();
        assert_eq!(min_v9, 2); // Min in V2 (5, 10) + 2 is 2
        assert_eq!(ph.time(), 11);
    }
}
