use std::collections::VecDeque;

use crate::ds::persistent::PersistentArray;

pub struct AhoCorasick {
    pub tr: PersistentArray<usize>,
    pub rt: Vec<usize>,
    pub link: Vec<usize>,
    pub next: Vec<Vec<(usize, usize)>>,
    pub term: Vec<bool>,
    pub sigma: usize,
}

impl AhoCorasick {
    pub fn new(sigma: usize) -> Self {
        let (tr, rt) = PersistentArray::new(sigma);
        Self {
            tr,
            rt: vec![rt],
            link: vec![0],
            next: vec![vec![]],
            term: vec![false],
            sigma,
        }
    }

    pub fn insert(&mut self, s: impl Iterator<Item = usize>) {
        let mut u = 0;
        for c in s {
            let mut found = None;
            for &(char_code, child) in &self.next[u] {
                if char_code == c {
                    found = Some(child);
                    break;
                }
            }
            match found {
                Some(v) => u = v,
                None => {
                    let v = self.next.len();
                    self.next.push(vec![]);
                    self.next[u].push((c, v));
                    self.rt.push(0);
                    self.link.push(0);
                    self.term.push(false);
                    u = v;
                }
            }
        }
        self.term[u] = true;
    }

    /// O(n log Σ)
    pub fn build(&mut self) {
        (self.tr, self.rt[0]) = PersistentArray::from_slice(&vec![0; self.sigma]);
        let mut q = VecDeque::new();
        let mut cur_rt = self.rt[0];
        for &(c, v) in &self.next[0] {
            cur_rt = self.tr.update(cur_rt, c, v);
            self.link[v] = 0;
            q.push_back(v);
        }
        self.rt[0] = cur_rt;
        while let Some(u) = q.pop_front() {
            let f = self.link[u];
            let fail_rt = self.rt[f];
            let mut u_rt = fail_rt;
            for &(c, v) in &self.next[u] {
                self.link[v] = *self.tr.query(fail_rt, c).unwrap();
                u_rt = self.tr.update(u_rt, c, v);
                q.push_back(v);
            }
            self.rt[u] = u_rt;
        }
    }

    /// O(log Σ)
    pub fn next_state(&self, u: usize, c: usize) -> usize {
        *self.tr.query(self.rt[u], c).unwrap()
    }
}
