use std::collections::BTreeMap;

pub struct SuffixMax<K, V> {
    m: BTreeMap<K, V>,
}

impl<K: Copy + Ord, V: Copy + Ord> SuffixMax<K, V> {
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
