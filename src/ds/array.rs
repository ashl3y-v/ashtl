const NULL: usize = usize::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<T> {
    pub v: Option<T>,
    pub l: usize,
    pub r: usize,
}

impl<T> Node<T> {
    pub fn new(v: T, l: usize, r: usize) -> Self {
        Node { v: Some(v), l, r }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersistentArray<T> {
    pub n: usize,
    pub v: Vec<Node<T>>,
    pub rt: Vec<usize>,
}

impl<T: Clone> PersistentArray<T> {
    pub fn new(a: &[T]) -> Self {
        let mut s = Self {
            n: a.len(),
            v: Vec::new(),
            rt: Vec::new(),
        };
        let r0 = s.build(0, a.len(), &a);
        s.rt.push(r0);
        s
    }

    fn build(&mut self, l: usize, r: usize, a: &[T]) -> usize {
        if r - l == 1 {
            self.v.push(Node::new(a[l].clone(), NULL, NULL));
        } else {
            let m = l + (r - l >> 1);
            let l = self.build(l, m, a);
            let r = self.build(m, r, a);
            self.v.push(Node { v: None, l, r });
        }
        self.v.len() - 1
    }

    pub fn query(&self, mut rt: usize, i: usize) -> &T {
        let (mut l, mut r) = (0, self.n);
        while r - l > 1 {
            let m = l + (r - l >> 1);
            if i < m {
                (rt, r) = (self.v[rt].l, m);
            } else {
                (rt, l) = (self.v[rt].r, m);
            }
        }
        self.v[rt].v.as_ref().unwrap()
    }

    pub fn get(&self, i: usize, time: usize) -> &T {
        self.query(self.rt[time], i)
    }

    pub fn update(&mut self, rt: usize, i: usize, v: T) -> usize {
        self.update_rec(rt, i, 0, self.n, v)
    }

    fn update_rec(&mut self, rt: usize, i: usize, l: usize, r: usize, v: T) -> usize {
        if r - l == 1 {
            self.v.push(Node::new(v, NULL, NULL));
            self.v.len() - 1
        } else {
            let m = l + (r - l >> 1);
            if i < m {
                let l = self.update_rec(self.v[rt].l, i, l, m, v);
                self.v.push(Node {
                    v: None,
                    l: l,
                    r: self.v[rt].r,
                });
                self.v.len() - 1
            } else {
                let r = self.update_rec(self.v[rt].r, i, m, r, v);
                self.v.push(Node {
                    v: None,
                    l: self.v[rt].l,
                    r,
                });
                self.v.len() - 1
            }
        }
    }

    pub fn set(&mut self, i: usize, time_prev: usize, time: usize, v: T) {
        debug_assert!(time_prev <= self.rt.len());
        while time >= self.rt.len() {
            self.rt.push(NULL);
        }
        self.rt[time] = self.update(self.rt[time_prev], i, v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_and_get() {
        let a = vec![10, 20, 30, 40, 50];
        let pa = PersistentArray::new(&a);

        assert_eq!(pa.n, 5);
        assert_eq!(pa.rt.len(), 1);

        // Check all values at time 0
        assert_eq!(*pa.get(0, 0), 10);
        assert_eq!(*pa.get(1, 0), 20);
        assert_eq!(*pa.get(2, 0), 30);
        assert_eq!(*pa.get(3, 0), 40);
        assert_eq!(*pa.get(4, 0), 50);
    }

    #[test]
    fn test_set_and_persistence() {
        let a = vec![0, 1, 2, 3, 4];
        let mut pa = PersistentArray::new(&a);

        // Update index 2, based on time 0, to create time 1
        pa.set(2, 0, 1, 99);

        assert_eq!(pa.rt.len(), 2);

        // Check new version (time 1)
        assert_eq!(*pa.get(0, 1), 0);
        assert_eq!(*pa.get(1, 1), 1);
        assert_eq!(*pa.get(2, 1), 99); // Changed
        assert_eq!(*pa.get(3, 1), 3);
        assert_eq!(*pa.get(4, 1), 4);

        // Check old version (time 0) - this is the persistence check
        assert_eq!(*pa.get(0, 0), 0);
        assert_eq!(*pa.get(1, 0), 1);
        assert_eq!(*pa.get(2, 0), 2); // Unchanged
        assert_eq!(*pa.get(3, 0), 3);
        assert_eq!(*pa.get(4, 0), 4);
    }

    #[test]
    fn test_time_branching() {
        let a = vec![100, 200, 300];
        let mut pa = PersistentArray::new(&a); // time 0

        // Create time 1 from time 0
        pa.set(0, 0, 1, 101);

        // Create time 2 from time 1
        pa.set(1, 1, 2, 202);

        // Create time 3 from time 0 (branching)
        pa.set(2, 0, 3, 303);

        assert_eq!(pa.rt.len(), 4);

        // Check time 0
        assert_eq!(*pa.get(0, 0), 100);
        assert_eq!(*pa.get(1, 0), 200);
        assert_eq!(*pa.get(2, 0), 300);

        // Check time 1 (based on 0)
        assert_eq!(*pa.get(0, 1), 101);
        assert_eq!(*pa.get(1, 1), 200);
        assert_eq!(*pa.get(2, 1), 300);

        // Check time 2 (based on 1)
        assert_eq!(*pa.get(0, 2), 101);
        assert_eq!(*pa.get(1, 2), 202);
        assert_eq!(*pa.get(2, 2), 300);

        // Check time 3 (based on 0)
        assert_eq!(*pa.get(0, 3), 100);
        assert_eq!(*pa.get(1, 3), 200);
        assert_eq!(*pa.get(2, 3), 303);
    }

    #[test]
    #[should_panic]
    fn test_get_invalid_time() {
        let a = vec![1, 2];
        let pa = PersistentArray::new(&a);
        pa.get(0, 1); // time 1 doesn't exist
    }

    #[test]
    #[should_panic]
    fn test_set_invalid_prev_time() {
        let a = vec![1, 2];
        let mut pa = PersistentArray::new(&a);
        pa.set(0, 5, 1, 99); // time_prev 5 doesn't exist
    }

    #[test]
    fn test_sparse_time_set() {
        let a = vec![10, 20];
        let mut pa = PersistentArray::new(&a);

        // Create time 5 from time 0
        pa.set(0, 0, 5, 11);

        assert_eq!(pa.rt.len(), 6);
        assert_eq!(*pa.get(0, 5), 11);
        assert_eq!(*pa.get(1, 5), 20);

        // Check that time 0 is still good
        assert_eq!(*pa.get(0, 0), 10);
    }

    #[test]
    #[should_panic]
    fn test_get_sparse_null_time() {
        let a = vec![10, 20];
        let mut pa = PersistentArray::new(&a);
        // Create time 5 from time 0
        pa.set(0, 0, 5, 11);

        // This should panic because rt[2] is NULL
        pa.get(0, 2);
    }
}
