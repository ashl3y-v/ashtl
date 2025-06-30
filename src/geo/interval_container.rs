use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct IntervalCover<T: Copy + Ord> {
    intervals: BTreeMap<T, T>,
}

impl<T: Ord + Copy> IntervalCover<T> {
    pub fn new() -> Self {
        IntervalCover {
            intervals: BTreeMap::new(),
        }
    }

    /// O(log n)
    pub fn add(&mut self, l: T, r: T) -> Option<(T, T)> {
        if l >= r {
            return None;
        }
        let mut new_l = l;
        let mut new_r = r;
        let mut to_remove = Vec::new();
        let mut iter = self.intervals.range(l..);
        while let Some((&start, &end)) = iter.next()
            && start <= new_r
        {
            new_r = new_r.max(end);
            to_remove.push(start);
        }
        if let Some((&start, &end)) = self.intervals.range(..l).next_back()
            && end >= l
        {
            new_l = new_l.min(start);
            new_r = new_r.max(end);
            to_remove.push(start);
        }
        for start in to_remove {
            self.intervals.remove(&start);
        }
        self.intervals.insert(new_l, new_r);
        Some((new_l, new_r))
    }

    /// O(log n)
    pub fn remove(&mut self, l: T, r: T) {
        if l < r
            && let Some((start, end)) = self.add(l, r)
        {
            self.intervals.remove(&start);
            if start < l {
                self.intervals.insert(start, l);
            }
            if r < end {
                self.intervals.insert(r, end);
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (T, T)> {
        self.intervals.iter().map(|(&l, &r)| (l, r))
    }
}

#[cfg(test)]
mod tests {
    use super::IntervalCover;

    #[test]
    fn test_add_and_iter() {
        let mut ic = IntervalCover::new();
        assert_eq!(ic.add(1, 4), Some((1, 4)));
        assert_eq!(ic.add(2, 5), Some((1, 5)));
        assert_eq!(ic.add(7, 8), Some((7, 8)));
        let intervals: Vec<_> = ic.iter().collect();
        assert_eq!(intervals, vec![(1, 5), (7, 8)]);
    }

    #[test]
    fn test_remove() {
        let mut ic = IntervalCover::new();
        ic.add(1, 10);
        ic.remove(3, 6);
        let intervals: Vec<_> = ic.iter().collect();
        assert_eq!(intervals, vec![(1, 3), (6, 10)]);
        ic.remove(20, 25);
        let intervals2: Vec<_> = ic.iter().collect();
        assert_eq!(intervals2, intervals);
    }
}
