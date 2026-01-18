use std::collections::BTreeMap;

/// O(n)
pub fn manacher(s: &str) -> Vec<usize> {
    let s: Vec<char> = s.chars().collect();
    let n = s.len();
    let mut res = vec![0; 2 * n];
    let mut longest = 0;
    let mut root_longest = 0;
    for i in 1..2 * n {
        let pal = if i > longest {
            1
        } else {
            (longest - i).min(res[2 * root_longest - i])
        };
        let mut pal = pal;
        while pal < i && i + pal < 2 * n && s[(i - pal) / 2 - 1] == s[(i + pal) / 2] {
            pal += 2;
        }
        res[i] = pal;
        if i + pal > longest {
            longest = i + pal;
            root_longest = i;
        }
    }
    res[1..2 * n].to_vec()
}

// https://arxiv.org/pdf/1506.04862
#[derive(Clone, Debug)]
pub struct Eertree {
    nxt: Vec<BTreeMap<char, usize>>,
    link: Vec<usize>,
    len: Vec<isize>,
    par: Vec<usize>,
    s: Vec<char>,
    n: usize,
    sz: usize,
    last: usize,
}

impl Eertree {
    pub fn new(q: usize) -> Self {
        let q = q + 3;
        let nxt = vec![BTreeMap::new(); q];
        let mut len = vec![0; q];
        let mut link = vec![0; q];
        len[1] = -1;
        link[1] = 1;
        len[2] = 0;
        link[2] = 1;
        Self {
            nxt,
            link,
            len,
            par: vec![0; q],
            s: vec!['\0'; q],
            n: 0,
            sz: 3,
            last: 2,
        }
    }

    /// O(log Σ) am.
    pub fn add(&mut self, c: char) -> usize {
        self.s[self.n] = c;
        let i = self.n;
        self.n += 1;
        let mut cur = self.last;
        loop {
            let l = self.len[cur] as usize;
            let j = i as isize - l as isize - 1;
            if j >= 0 && (self.s[j as usize] == c) {
                break;
            }
            cur = self.link[cur];
        }
        if !self.nxt[cur].contains_key(&c) {
            let nn = self.sz;
            self.sz += 1;
            self.nxt[cur].insert(c, nn);
            self.len[nn] = self.len[cur] + 2;
            self.par[nn] = cur;
            if self.len[nn] == 1 {
                self.link[nn] = 2;
            } else {
                let mut p = self.link[cur];
                loop {
                    let l = self.len[p] as usize;
                    let j = i as isize - l as isize - 1;
                    if j >= 0 && (self.s[j as usize] == c) {
                        break;
                    }
                    p = self.link[p];
                }
                self.link[nn] = self.nxt[p][&c];
            }
        }
        self.last = self.nxt[cur][&c];
        self.last - 2
    }

    pub fn sufpal(&self) -> usize {
        self.last - 2
    }

    pub fn len(&self, node: usize) -> isize {
        self.len[node + 2]
    }

    pub fn pal_count(&self) -> usize {
        self.sz - 3
    }

    pub fn print(&self) {
        println!("{}", self.sz - 3);
        for id in 3..self.sz {
            println!("{} {}", self.par[id] - 2, self.link[id] - 2);
        }
    }
}
