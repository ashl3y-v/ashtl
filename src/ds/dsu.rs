use std::{
    fmt::Debug,
    ops::{Index, IndexMut},
};

use crate::alg::monoid::Group;

pub struct DSU {
    pub p: Vec<isize>,
}

impl DSU {
    pub fn new(n: usize) -> Self {
        Self { p: vec![-1; n] }
    }

    pub fn find(&mut self, mut x: usize) -> usize {
        while self.p[x] >= 0 {
            let p = self.p[x] as usize;
            if self.p[p] >= 0 {
                self.p[x] = self.p[p];
            }
            x = p;
        }
        x
    }

    pub fn same(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn union(&mut self, x: usize, y: usize) -> (usize, bool) {
        let mut i = self.find(x);
        let mut j = self.find(y);
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (i, false);
        }
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        (i, true)
    }

    pub fn union_root(&mut self, x: usize, mut r: usize) -> (usize, bool) {
        let mut i = self.find(x);
        if i == r {
            return (r, false);
        }
        if self.p[i] > self.p[r] {
            (i, r) = (r, i);
        }
        self.p[i] += self.p[r];
        self.p[r] = i as isize;
        (i, true)
    }

    pub fn size(&mut self, x: usize) -> usize {
        let r = self.find(x);
        (-self.p[r]) as usize
    }

    pub fn resize(&mut self, n: usize) {
        self.p.resize(n, -1);
    }
}

impl Debug for DSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self.p))
    }
}

impl<Idx, T> Index<Idx> for DSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for DSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}

pub struct RollbackDSU {
    pub p: Vec<isize>,
    pub joins: Vec<(usize, isize)>,
}

impl RollbackDSU {
    pub fn new(n: usize) -> Self {
        Self {
            p: vec![-1; n],
            joins: Vec::new(),
        }
    }

    pub fn find(&self, mut i: usize) -> usize {
        while self.p[i] >= 0 {
            i = self.p[i] as usize;
        }
        i
    }

    pub fn same(&self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn size(&self, x: usize) -> usize {
        (-self.p[self.find(x)]) as usize
    }

    pub fn union(&mut self, x: usize, y: usize) -> (usize, bool) {
        let (mut i, mut j) = (self.find(x), self.find(y));
        if self.p[i] > self.p[j] {
            (i, j) = (j, i);
        }
        if i == j {
            return (i, false);
        }
        self.joins.push((j, self.p[j]));
        self.p[i] += self.p[j];
        self.p[j] = i as isize;
        return (i, true);
    }

    pub fn rollback(&mut self, t: usize) {
        while self.joins.len() > t
            && let Some((i, s)) = self.joins.pop()
        {
            let pi = self.p[i] as usize;
            self.p[pi] -= s;
            self.p[i] = s;
        }
    }

    pub fn undo(&mut self) {
        if let Some((i, s)) = self.joins.pop() {
            let pi = self.p[i] as usize;
            self.p[pi] -= s;
            self.p[i] = s;
        }
    }
}

impl Debug for RollbackDSU {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}, {:?}", self.p, self.joins))
    }
}

impl<Idx, T> Index<Idx> for RollbackDSU
where
    Vec<isize>: Index<Idx, Output = T>,
{
    type Output = T;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.p[index]
    }
}

impl<Idx, T> IndexMut<Idx> for RollbackDSU
where
    Vec<isize>: IndexMut<Idx, Output = T>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.p[index]
    }
}

#[derive(Debug, Clone)]
pub struct PotentialDSU<G: Group> {
    f: Vec<isize>,
    p: Vec<G::T>,
    size: usize,
    group_cnt: usize,
}

impl<G: Group> PotentialDSU<G> {
    pub fn new(n: usize) -> Self {
        let mut table = Self {
            f: Vec::with_capacity(n),
            p: Vec::with_capacity(n),
            size: n,
            group_cnt: n,
        };
        table.resize(n);
        table
    }

    pub fn resize(&mut self, n: usize) {
        self.size = n;
        self.group_cnt = n;
        if n == 0 {
            return;
        }
        self.f = vec![-1; n];
        self.p = vec![G::identity(); n];
    }

    pub fn find(&mut self, i: usize) -> (usize, G::T) {
        if self.f[i] < 0 {
            return (i, self.p[i]);
        }
        let f = self.f[i] as usize;
        let (root, root_val) = self.find(f);
        self.f[i] = root as isize;
        self.p[i] = G::op(&self.p[i], &root_val);
        (root, self.p[i])
    }

    pub fn size(&mut self, i: usize) -> usize {
        let (root, _) = self.find(i);
        (-self.f[root]) as usize
    }

    pub fn union_to(&mut self, a: usize, b: usize, p: G::T) {
        self.f[b] += self.f[a];
        self.f[a] = b as isize;
        self.p[a] = p;
        self.group_cnt -= 1;
    }

    pub fn union(&mut self, a: usize, b: usize, mut p: G::T) -> bool {
        let (a, va) = self.find(a);
        let (b, vb) = self.find(b);
        if a == b {
            return false;
        }
        let inv_a = G::inverse(&va);
        p = G::op(&G::op(&inv_a, &p), &vb);
        if self.f[a] < self.f[b] {
            self.union_to(b, a, G::inverse(&p));
        } else {
            self.union_to(a, b, p);
        }
        true
    }

    pub fn calc(&mut self, a: usize, b: usize) -> Option<G::T> {
        let (a, va) = self.find(a);
        let (b, vb) = self.find(b);
        if a != b {
            return None;
        }
        Some(G::op(&va, &G::inverse(&vb)))
    }

    pub fn is_head(&self, i: usize) -> bool {
        self.f[i] < 0
    }

    pub fn count(&self) -> usize {
        self.group_cnt
    }
}

pub struct RangeParallelDSU {
    pub lay: Vec<DSU>,
    pub num_layers: usize,
}

impl RangeParallelDSU {
    /// O(n log n)
    pub fn new(n: usize) -> Self {
        let num_layers = if n == 0 { 0 } else { n.ilog2() as usize + 1 };
        let mut lay = Vec::with_capacity(num_layers);
        for k in 0..num_layers {
            lay.push(DSU::new(n - (1 << k) + 1));
        }
        Self { lay, num_layers }
    }

    fn merge_level(&mut self, k: usize, u: usize, v: usize) {
        if k == 0 {
            self.lay[0].union(u, v);
            return;
        }
        let (_, united) = self.lay[k].union(u, v);
        if united {
            let half_len = 1 << (k - 1);
            self.merge_level(k - 1, u, v);
            self.merge_level(k - 1, u + half_len, v + half_len);
        }
    }

    /// O(q α(n) + n log n α(n)) am.
    pub fn union_range(&mut self, u: usize, v: usize, len: usize) {
        if len == 0 {
            return;
        }
        let log_len = if len == 0 { 0 } else { len.ilog2() as usize };
        self.merge_level(log_len, u, v);
        let shift = len - (1 << log_len);
        self.merge_level(log_len, u + shift, v + shift);
    }

    /// O(α(n))
    pub fn same(&mut self, u: usize, v: usize) -> bool {
        self.lay[0].same(u, v)
    }

    /// O(α(n))
    pub fn size(&mut self, u: usize) -> usize {
        self.lay[0].size(u)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PersistentDSUQuery {
    pub id: usize,
    pub op_type: u8,
    pub u: usize,
    pub v: usize,
}

pub struct PersistentDSU {
    dsu: RollbackDSU,
    adj: Vec<Vec<usize>>,
    queries: Vec<PersistentDSUQuery>,
    results: Vec<u8>,
}

impl PersistentDSU {
    pub fn new(n: usize, q_count: usize) -> Self {
        let mut queries = Vec::with_capacity(q_count + 1);
        queries.push(PersistentDSUQuery {
            id: 0,
            op_type: 0,
            u: 0,
            v: 0,
        });
        Self {
            dsu: RollbackDSU::new(n),
            adj: vec![vec![]; q_count + 1],
            queries,
            results: vec![2; q_count],
        }
    }

    pub fn add_query(&mut self, id: usize, op_type: u8, k: usize, u: usize, v: usize) {
        self.adj[k].push(id + 1);
        self.queries.push(PersistentDSUQuery { id, op_type, u, v });
    }

    fn rec(
        u: usize,
        adj: &[Vec<usize>],
        queries: &[PersistentDSUQuery],
        dsu: &mut RollbackDSU,
        results: &mut Vec<u8>,
    ) {
        let mut merged = false;
        if u > 0 {
            let q = &queries[u];
            if q.op_type == 0 {
                merged = dsu.union(q.u, q.v).1;
            } else {
                let is_same = dsu.same(q.u, q.v);
                results[q.id] = if is_same { 1 } else { 0 };
            }
        }
        let is_query_node = if u > 0 {
            queries[u].op_type == 1
        } else {
            false
        };
        if !is_query_node {
            for &v in &adj[u] {
                Self::rec(v, adj, queries, dsu, results);
            }
        }
        if merged {
            dsu.undo();
        }
    }

    pub fn calc(&mut self) {
        Self::rec(
            0,
            &self.adj,
            &self.queries,
            &mut self.dsu,
            &mut self.results,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_updates() {
        // Scenario:
        // 0 -> Union(1, 2) -> Union(2, 3) -> Check(1, 3)
        // k=0      id=0         id=1         id=2
        // Version: 1            2            3

        let mut p_dsu = PersistentDSU::new(10, 3);

        // id 0: Union(1, 2) based on root (k=0)
        p_dsu.add_query(0, 0, 0, 1, 2);

        // id 1: Union(2, 3) based on version 1 (k=1)
        // Note: version index = id + 1, so previous query id 0 created version 1.
        p_dsu.add_query(1, 0, 1, 2, 3);

        // id 2: Check(1, 3) based on version 2 (k=2)
        p_dsu.add_query(2, 1, 2, 1, 3);

        p_dsu.calc();

        assert_eq!(p_dsu.results[0], 2); // Merge op has no output
        assert_eq!(p_dsu.results[1], 2); // Merge op has no output
        assert_eq!(p_dsu.results[2], 1); // 1 and 3 should be connected
    }

    #[test]
    fn test_branching() {
        // Scenario:
        // Root (v0)
        //  |
        //  +-> Union(1, 2) [v1, id=0]
        //       |
        //       +-> Union(3, 4) [v2, id=1] -> Check(1, 2) [v3, id=2] (Should be True)
        //       |                             Check(3, 4) [v4, id=3] (Should be True)
        //       |
        //       +-> Union(1, 3) [v5, id=4] -> Check(2, 3) [v6, id=5] (Should be True: 1-2 is in v1, 1-3 is in v5)
        //                                     Check(3, 4) [v7, id=6] (Should be False: 3-4 happened in v2, not here)

        let mut p_dsu = PersistentDSU::new(10, 7);

        // v1 (id=0): Union(1, 2) on v0
        p_dsu.add_query(0, 0, 0, 1, 2);

        // Branch 1: v2 (id=1): Union(3, 4) on v1
        p_dsu.add_query(1, 0, 1, 3, 4);

        // Check in Branch 1
        p_dsu.add_query(2, 1, 2, 1, 2); // Check(1, 2) on v2
        p_dsu.add_query(3, 1, 2, 3, 4); // Check(3, 4) on v2

        // Branch 2: v5 (id=4): Union(1, 3) on v1 (Note k=1)
        p_dsu.add_query(4, 0, 1, 1, 3);

        // Check in Branch 2
        p_dsu.add_query(5, 1, 5, 2, 3); // Check(2, 3) on v5
        p_dsu.add_query(6, 1, 5, 3, 4); // Check(3, 4) on v5

        p_dsu.calc();

        // Branch 1 results
        assert_eq!(p_dsu.results[2], 1, "v2: 1-2 should be connected");
        assert_eq!(p_dsu.results[3], 1, "v2: 3-4 should be connected");

        // Branch 2 results
        assert_eq!(
            p_dsu.results[5], 1,
            "v5: 2-3 should be connected (via 1-2 and 1-3)"
        );
        assert_eq!(
            p_dsu.results[6], 0,
            "v5: 3-4 should NOT be connected (happened in parallel branch)"
        );
    }

    #[test]
    fn test_checking_past_version() {
        // Scenario:
        // v0 -> Union(1, 2) [v1] -> Union(2, 3) [v2]
        // We want to check (1, 3) on v1 (before the second union happened).

        let mut p_dsu = PersistentDSU::new(10, 3);

        // v1 (id=0): Union(1, 2) on v0
        p_dsu.add_query(0, 0, 0, 1, 2);

        // v2 (id=1): Union(2, 3) on v1
        p_dsu.add_query(1, 0, 1, 2, 3);

        // Check on v1 (id=2): Check(1, 3) on v1 (k=1)
        // Even though v2 exists, we are branching off v1 to check state of v1
        p_dsu.add_query(2, 1, 1, 1, 3);

        p_dsu.calc();

        assert_eq!(p_dsu.results[2], 0, "At v1, 1 and 3 are not yet connected");
    }
}
