use std::collections::BTreeMap;

use crate::ds::dsu::DSU;

pub struct MaxGe<K, V> {
    m: BTreeMap<K, V>,
}

impl<K: Copy + Ord, V: Copy + Ord> MaxGe<K, V> {
    pub fn new() -> Self {
        Self { m: BTreeMap::new() }
    }

    pub fn insert(&mut self, a: K, b: V) {
        if let Some((_, d)) = self.m.range(&a..).next()
            && d >= &b
        {
            return;
        }
        self.m.insert(a, b);
        let to_remove = self
            .m
            .range(..&a)
            .rev()
            .take_while(|(_, d)| *d <= &b)
            .map(|(c, _)| *c)
            .collect::<Vec<_>>();
        for c in to_remove {
            self.m.remove(&c);
        }
    }

    pub fn query(&self, a: K) -> Option<V> {
        self.m.range(&a..).next().map(|(_, &b)| b)
    }
}

/// O(α(n))
pub struct SuffixMax<T> {
    n: usize,
    a: Vec<T>,
    dsu: DSU,
    st: Vec<(usize, T)>,
}

impl<T: Clone + PartialOrd> SuffixMax<T> {
    pub fn new() -> Self {
        Self {
            n: 0,
            a: Vec::new(),
            dsu: DSU::new(0),
            st: Vec::new(),
        }
    }

    pub fn push(&mut self, x: T) {
        let p = self.n;
        self.n += 1;
        self.dsu.resize(self.n);
        self.a.push(x.clone());
        while let Some((i, v)) = self.st.last()
            && v <= &x
        {
            self.dsu.union(p, *i);
            self.st.pop();
        }
        let r = self.dsu.find(p);
        self.st.push((r, x.clone()));
        self.a[r] = x;
    }

    pub fn query(&mut self, i: usize) -> &T {
        debug_assert!(i < self.n);
        &self.a[self.dsu.find(i)]
    }
}
