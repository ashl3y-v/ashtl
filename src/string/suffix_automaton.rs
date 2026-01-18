use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub struct SuffixAutomaton {
    pub nxt: Vec<BTreeMap<char, usize>>,
    pub link: Vec<usize>,
    pub len: Vec<usize>,
    pub sz: usize,
    pub last: usize,
}

impl SuffixAutomaton {
    pub fn new(n: usize) -> Self {
        let cap = 2 * n + 3;
        let nxt = vec![BTreeMap::new(); cap];
        let mut link = vec![0; cap];
        let mut len = vec![0; cap];
        link[1] = 0;
        len[1] = 0;
        Self {
            nxt,
            link,
            len,
            sz: 2,
            last: 1,
        }
    }

    /// O(log Σ) am.
    pub fn add(&mut self, c: char) -> usize {
        let cur = self.sz;
        self.sz += 1;
        self.len[cur] = self.len[self.last] + 1;
        let mut p = self.last;
        while p != 0 && !self.nxt[p].contains_key(&c) {
            self.nxt[p].insert(c, cur);
            p = self.link[p];
        }
        if p == 0 {
            self.link[cur] = 1;
        } else {
            let q = *self.nxt[p].get(&c).unwrap();
            if self.len[p] + 1 == self.len[q] {
                self.link[cur] = q;
            } else {
                let cln = self.sz;
                self.sz += 1;
                self.len[cln] = self.len[p] + 1;
                self.nxt[cln] = self.nxt[q].clone();
                self.link[cln] = self.link[q];
                while p != 0 && self.nxt[p].get(&c) == Some(&q) {
                    self.nxt[p].insert(c, cln);
                    p = self.link[p];
                }
                self.link[q] = cln;
                self.link[cur] = cln;
            }
        }
        self.last = cur;
        cur
    }

    pub fn get(&self, state: usize, c: char) -> Option<usize> {
        self.nxt[state].get(&c).copied()
    }

    pub fn from_str(s: &str) -> Self {
        let mut sa = Self::new(s.len());
        for c in s.chars() {
            sa.add(c);
        }
        sa
    }

    pub fn from_bytes(s: &[u8]) -> Self {
        let mut sa = Self::new(s.len());
        for &c in s {
            sa.add(c as char);
        }
        sa
    }
}
