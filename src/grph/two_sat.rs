use crate::grph::scc::scc;

/// 2SAT O(n + m)
pub struct TwoSat {
    n: usize,
    adj: Vec<Vec<usize>>,
    pub values: Vec<bool>,
}

impl TwoSat {
    #[inline]
    pub fn new(n: usize) -> Self {
        TwoSat {
            n,
            adj: vec![Vec::new(); n << 1],
            values: Vec::new(),
        }
    }

    #[inline]
    pub fn add_var(&mut self) -> isize {
        let v = self.n;
        self.adj.push(Vec::new());
        self.adj.push(Vec::new());
        self.n += 1;
        v as isize
    }

    #[inline]
    fn idx(lit: isize) -> usize {
        if lit >= 0 {
            (lit as usize) << 1
        } else {
            ((!lit) as usize) << 1 | 1
        }
    }

    #[inline]
    pub fn set_value(&mut self, x: isize) -> &mut Self {
        self.either(x, x);
        self
    }

    #[inline]
    pub fn either(&mut self, f: isize, j: isize) -> &mut Self {
        let u = Self::idx(f) ^ 1;
        let v = Self::idx(j);
        self.adj[u].push(v);
        let u2 = Self::idx(j) ^ 1;
        let v2 = Self::idx(f);
        self.adj[u2].push(v2);
        self
    }

    #[inline]
    pub fn at_most_one(&mut self, li: &[isize]) -> &mut Self {
        if li.len() <= 1 {
            return self;
        }
        let mut cur = !li[0];
        for &lit in &li[2..] {
            let nxt = self.add_var();
            self.either(cur, !lit);
            self.either(cur, nxt);
            self.either(!lit, nxt);
            cur = !nxt;
        }
        self.either(cur, !li[1]);
        self
    }

    pub fn solve(&mut self) -> bool {
        let comp = scc(&self.adj, |_| {});

        self.values = vec![false; self.n];
        for i in 0..self.n {
            if comp[2 * i] == comp[2 * i + 1] {
                return false;
            }
            self.values[i] = comp[2 * i] < comp[2 * i + 1];
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// (x0 ∨ x1) is obviously satisfiable.
    #[test]
    fn test_simple_sat() {
        let mut ts = TwoSat::new(2);
        assert!(ts.either(0, 1).solve(), "should be satisfiable");
        // check that the returned assignment actually satisfies (x0 || x1)
        let vals = &ts.values;
        assert!(vals[0] || vals[1]);
    }

    /// x0 = true, then adding (¬x0 ∨ ¬x0) makes it unsatisfiable.
    #[test]
    fn test_simple_unsat() {
        let mut ts = TwoSat::new(1);
        ts.set_value(0); // force x0 = true
        ts.either(!0, !0); // clause (¬x0 ∨ ¬x0) → x0 must be false
        assert!(!ts.solve(), "should be unsatisfiable");
    }

    /// at_most_one on {x0,x1,x2}: setting two of them true is impossible.
    #[test]
    fn test_at_most_one_unsat() {
        let mut ts = TwoSat::new(3);
        ts.at_most_one(&[0, 1, 2]).set_value(0).set_value(1);
        assert!(!ts.solve(), "at most one of three but set two");
    }

    /// at_most_one on {x0,x1,x2}: setting exactly one is fine.
    #[test]
    fn test_at_most_one_sat() {
        let mut ts = TwoSat::new(3);
        ts.at_most_one(&[0, 1, 2]);
        ts.set_value(1);
        assert!(ts.solve(), "should be satisfiable with exactly one true");
        // ensure only x1 is true
        let vals = &ts.values;
        assert!(!vals[0] && vals[1] && !vals[2]);
    }

    /// dynamically adding a variable with add_var(), then forcing it true.
    #[test]
    fn test_add_var_and_set() {
        let mut ts = TwoSat::new(0);
        let v = ts.add_var(); // first new var has index 0
        ts.set_value(v);
        assert!(ts.solve(), "new var forced true is obviously satisfiable");
        assert_eq!(ts.values.len(), 1);
        assert!(ts.values[0]);
    }

    /// A small implication chain:
    /// (¬x0 → x1), (¬x1 → x2), (¬x2 → ¬x0)
    /// one can satisfy this by x0 = false, x1 = false, x2 = false.
    #[test]
    fn test_implication_chain() {
        let mut ts = TwoSat::new(3);
        ts.either(!0, 1);
        ts.either(!1, 2);
        ts.either(!2, !0);
        ts.solve();
        assert!(
            ts.solve(),
            "implication cycle should admit the all-false assignment"
        );
        let vals = &ts.values;
        assert!(!vals[0] && vals[1] && vals[2]);
    }
}
