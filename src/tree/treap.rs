// TODO: make this use an array, reduce pushes and pulls to strictly necessary (inspir from splay), make Y inputed by user

use rand::Rng;

#[derive(Clone, Debug)]
pub struct Node<T, D> {
    l: Option<Box<Node<T, D>>>,
    r: Option<Box<Node<T, D>>>,
    x: T,
    d: D,
    y: u32,
    c: usize,
}

impl<T, D: Default> Node<T, D> {
    #[inline]
    pub fn new(val: T, rng: &mut impl Rng) -> Self {
        Node {
            l: None,
            r: None,
            x: val,
            d: D::default(),
            y: rng.random(),
            c: 1,
        }
    }
}

impl<T, D: Default> Node<T, D> {
    #[inline]
    fn cnt(n: &Option<Box<Node<T, D>>>) -> usize {
        n.as_ref().map_or(0, |node| node.c)
    }
}

#[derive(Clone, Debug)]
pub struct Treap<T, D, PushF, PullF> {
    root: Option<Box<Node<T, D>>>,
    push: PushF,
    pull: PullF,
}

impl<T, D: Default + PartialEq, PushF: FnMut(&mut Node<T, D>), PullF: FnMut(&mut Node<T, D>)>
    Treap<T, D, PushF, PullF>
{
    pub fn new(push: PushF, pull: PullF) -> Self {
        Self {
            root: None,
            push,
            pull,
        }
    }

    fn pull(&mut self, node: &mut Node<T, D>) {
        node.c = Node::cnt(&node.l) + Node::cnt(&node.r) + 1;
        (self.pull)(node);
    }

    pub fn split(
        &mut self,
        n: Option<Box<Node<T, D>>>,
        k: usize,
    ) -> (Option<Box<Node<T, D>>>, Option<Box<Node<T, D>>>) {
        match n {
            None => (None, None),
            Some(mut node) => {
                (self.push)(&mut node);
                if Node::cnt(&node.l) >= k {
                    let (l, r) = self.split(node.l.take(), k);
                    node.l = r;
                    self.pull(&mut node);
                    (l, Some(node))
                } else {
                    let (l, r) = self.split(node.r.take(), k - Node::cnt(&node.l) - 1);
                    node.r = l;
                    self.pull(&mut node);
                    (Some(node), r)
                }
            }
        }
    }

    pub fn merge(
        &mut self,
        l: Option<Box<Node<T, D>>>,
        r: Option<Box<Node<T, D>>>,
    ) -> Option<Box<Node<T, D>>> {
        match (l, r) {
            (None, r) => r,
            (l, None) => l,
            (Some(mut l_node), Some(mut r_node)) => {
                (self.push)(&mut l_node);
                (self.push)(&mut r_node);
                if l_node.y > r_node.y {
                    l_node.r = self.merge(l_node.r.take(), Some(r_node));
                    self.pull(&mut l_node);
                    Some(l_node)
                } else {
                    r_node.l = self.merge(Some(l_node), r_node.l.take());
                    self.pull(&mut r_node);
                    Some(r_node)
                }
            }
        }
    }

    pub fn insert(&mut self, pos: usize, val: T, rng: &mut impl Rng) {
        let root = self.root.take();
        let (l, r) = self.split(root, pos);
        let merged_left = self.merge(l, Some(Box::new(Node::new(val, rng))));
        self.root = self.merge(merged_left, r);
    }

    pub fn delete(&mut self, pos: usize) {
        let root = self.root.take();
        let (l, r) = self.split(root, pos);
        let (_, r) = self.split(r, 1);
        self.root = self.merge(l, r);
    }

    pub fn update_range<F>(&mut self, l: usize, r: usize, mut f: F)
    where
        F: FnMut(&mut Node<T, D>),
    {
        let root = self.root.take();
        let (a, b) = self.split(root, l);
        let (mut b, c) = self.split(b, r - l);
        if let Some(ref mut node) = b {
            f(node);
        }
        let merged_ab = self.merge(a, b);
        self.root = self.merge(merged_ab, c);
    }

    pub fn query_range<R, F>(&mut self, l: usize, r: usize, mut f: F) -> R
    where
        F: FnMut(&mut Node<T, D>) -> R,
    {
        let root = self.root.take();
        let (a, b) = self.split(root, l);
        let (mut b, c) = self.split(b, r - l);
        let result = if let Some(ref mut node) = b {
            f(node)
        } else {
            panic!("Empty range query");
        };
        let merged_ab = self.merge(a, b);
        self.root = self.merge(merged_ab, c);
        result
    }

    pub fn each<F>(&mut self, mut f: F)
    where
        F: FnMut(&T),
    {
        let root = self.root.take();
        self.root = self.each_impl(root, &mut f);
    }

    fn each_impl<F>(&mut self, n: Option<Box<Node<T, D>>>, f: &mut F) -> Option<Box<Node<T, D>>>
    where
        F: FnMut(&T),
    {
        match n {
            None => None,
            Some(mut node) => {
                (self.push)(&mut node);
                let left = node.l.take();
                let right = node.r.take();
                node.l = self.each_impl(left, f);
                f(&node.x);
                node.r = self.each_impl(right, f);
                Some(node)
            }
        }
    }
}

impl<T: Clone, D: Default + PartialEq, PushF: FnMut(&mut Node<T, D>), PullF: FnMut(&mut Node<T, D>)>
    Treap<T, D, PushF, PullF>
{
    #[inline]
    pub fn from_slice(vals: &[T], push: PushF, pull: PullF, rng: &mut impl Rng) -> Self {
        let mut treap = Self::new(push, pull);
        treap.root = treap.build_recursive(vals, rng);
        treap
    }

    fn build_recursive(&mut self, vals: &[T], rng: &mut impl Rng) -> Option<Box<Node<T, D>>> {
        if vals.is_empty() {
            return None;
        }
        let mid = vals.len() / 2;
        let mut node = Box::new(Node::new(vals[mid].clone(), rng));
        node.l = self.build_recursive(&vals[..mid], rng);
        node.r = self.build_recursive(&vals[mid + 1..], rng);
        self.heapify(&mut node);
        self.pull(&mut node);
        Some(node)
    }

    // TODO: i'm pretty sure this is just wrong for the case of non random Y at least
    fn heapify(&mut self, mut node: &mut Box<Node<T, D>>) {
        loop {
            let left_priority = node.l.as_ref().map(|n| n.y);
            let right_priority = node.r.as_ref().map(|n| n.y);
            let current_priority = node.y;
            let max_is_left = left_priority.map_or(false, |lp| {
                lp > current_priority && right_priority.map_or(true, |rp| lp >= rp)
            });
            let max_is_right =
                !max_is_left && right_priority.map_or(false, |rp| rp > current_priority);
            if max_is_left {
                if let Some(ref mut left) = node.l {
                    std::mem::swap(&mut node.y, &mut left.y);
                    node = left;
                    continue;
                }
            } else if max_is_right {
                if let Some(ref mut right) = node.r {
                    std::mem::swap(&mut node.y, &mut right.y);
                    node = right;
                    continue;
                }
            }
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rng;

    // Data structure to hold both sum and lazy update values
    #[derive(Clone, Debug, Default, PartialEq)]
    struct SumData {
        sum: i32,
        lazy: i32,
    }

    // Helper function to create a simple treap for testing
    fn create_simple_treap()
    -> Treap<i32, (), impl FnMut(&mut Node<i32, ()>), impl FnMut(&mut Node<i32, ()>)> {
        let push = |_node: &mut Node<i32, ()>| {};
        let pull = |_node: &mut Node<i32, ()>| {};
        Treap::new(push, pull)
    }

    // Helper function to create a treap with range sum functionality
    fn create_sum_treap()
    -> Treap<i32, SumData, impl FnMut(&mut Node<i32, SumData>), impl FnMut(&mut Node<i32, SumData>)>
    {
        let push = |node: &mut Node<i32, SumData>| {
            if node.d.lazy != 0 {
                node.x += node.d.lazy;
                node.d.sum += node.d.lazy * node.c as i32;
                if let Some(ref mut l) = node.l {
                    l.d.lazy += node.d.lazy;
                }
                if let Some(ref mut r) = node.r {
                    r.d.lazy += node.d.lazy;
                }
                node.d.lazy = 0;
            }
        };
        let pull = |node: &mut Node<i32, SumData>| {
            node.d.sum = node.x;
            if let Some(ref l) = node.l {
                node.d.sum += l.d.sum;
            }
            if let Some(ref r) = node.r {
                node.d.sum += r.d.sum;
            }
        };
        Treap::new(push, pull)
    }

    // Helper function to extract all values from treap
    fn extract_values(
        treap: &mut Treap<i32, (), impl FnMut(&mut Node<i32, ()>), impl FnMut(&mut Node<i32, ()>)>,
    ) -> Vec<i32> {
        let mut values = Vec::new();
        treap.each(|x| values.push(*x));
        values
    }

    // Helper function to extract all values from sum treap
    fn extract_sum_values(
        treap: &mut Treap<
            i32,
            SumData,
            impl FnMut(&mut Node<i32, SumData>),
            impl FnMut(&mut Node<i32, SumData>),
        >,
    ) -> Vec<i32> {
        let mut values = Vec::new();
        treap.each(|x| values.push(*x));
        values
    }

    #[test]
    fn test_empty_treap() {
        let mut treap = create_simple_treap();
        let values = extract_values(&mut treap);
        assert_eq!(values, Vec::<i32>::new());
    }

    #[test]
    fn test_single_insert() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        treap.insert(0, 10, &mut rng);
        let values = extract_values(&mut treap);
        assert_eq!(values, vec![10]);
    }

    #[test]
    fn test_multiple_inserts_at_end() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        treap.insert(0, 1, &mut rng);
        treap.insert(1, 2, &mut rng);
        treap.insert(2, 3, &mut rng);
        treap.insert(3, 4, &mut rng);

        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_multiple_inserts_at_beginning() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        treap.insert(0, 4, &mut rng);
        treap.insert(0, 3, &mut rng);
        treap.insert(0, 2, &mut rng);
        treap.insert(0, 1, &mut rng);

        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_inserts_at_middle() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        treap.insert(0, 1, &mut rng);
        treap.insert(1, 3, &mut rng);
        treap.insert(1, 2, &mut rng);
        treap.insert(3, 4, &mut rng);

        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_delete_single_element() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        treap.insert(0, 42, &mut rng);
        treap.delete(0);

        let values = extract_values(&mut treap);
        assert_eq!(values, Vec::<i32>::new());
    }

    #[test]
    fn test_delete_from_beginning() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        treap.delete(0); // Remove first element (1)
        let values = extract_values(&mut treap);
        assert_eq!(values, vec![2, 3, 4, 5]);
    }

    #[test]
    fn test_delete_from_end() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        treap.delete(4); // Remove last element (5)
        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_delete_from_middle() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        treap.delete(2); // Remove middle element (3)
        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 4, 5]);
    }

    #[test]
    fn test_range_sum_query() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Query sum of range [1, 3] (values 2, 3, 4)
        let sum = treap.query_range(1, 4, |node| node.d.sum);
        assert_eq!(sum, 9); // 2 + 3 + 4 = 9
    }

    #[test]
    fn test_range_sum_query_full_range() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Query sum of entire range
        let sum = treap.query_range(0, 5, |node| node.d.sum);
        assert_eq!(sum, 15); // 1 + 2 + 3 + 4 + 5 = 15
    }

    #[test]
    fn test_range_update() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Add 10 to range [1, 3] (positions 1, 2, 3)
        treap.update_range(1, 4, |node| node.d.lazy += 10);

        let values = extract_sum_values(&mut treap);
        assert_eq!(values, vec![1, 12, 13, 14, 5]);
    }

    #[test]
    fn test_range_update_and_query() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Add 10 to range [1, 3]
        treap.update_range(1, 4, |node| node.d.lazy += 10);

        // Query sum of updated range
        let sum = treap.query_range(1, 4, |node| node.d.sum);
        assert_eq!(sum, 39); // (2+10) + (3+10) + (4+10) = 12 + 13 + 14 = 39
    }

    #[test]
    fn test_complex_operations() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Build array [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Insert 10 at position 2: [1, 2, 10, 3, 4, 5]
        treap.insert(2, 10, &mut rng);

        // Delete position 1: [1, 10, 3, 4, 5]
        treap.delete(1);

        // Add 5 to range [1, 3]: [1, 15, 8, 9, 5]
        treap.update_range(1, 4, |node| node.d.lazy += 5);

        let values = extract_sum_values(&mut treap);
        assert_eq!(values, vec![1, 15, 8, 9, 5]);

        // Query sum of range [1, 3]
        let sum = treap.query_range(1, 4, |node| node.d.sum);
        assert_eq!(sum, 32); // 15 + 8 + 9 = 32
    }

    #[test]
    fn test_split_and_merge_operations() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Test split at position 2
        let root = treap.root.take();
        let (left, right) = treap.split(root, 2);

        // Verify split worked by merging back
        treap.root = treap.merge(left, right);

        let values = extract_values(&mut treap);
        assert_eq!(values, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_large_sequence() {
        let mut treap = create_simple_treap();
        let mut rng = rng();

        // Insert 1000 elements
        for i in 0..1000 {
            treap.insert(i, i as i32, &mut rng);
        }

        // Delete every other element
        for i in (0..500).rev() {
            treap.delete(i * 2);
        }

        let values = extract_values(&mut treap);
        let expected: Vec<i32> = (0..1000).filter(|x| x % 2 == 1).collect();
        assert_eq!(values, expected);
    }

    #[test]
    fn test_empty_range_operations() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert single element
        treap.insert(0, 42, &mut rng);

        // Update range of size 0 (should do nothing)
        treap.update_range(0, 0, |node| node.d.lazy += 100);

        let values = extract_sum_values(&mut treap);
        assert_eq!(values, vec![42]);
    }

    #[test]
    fn test_stress_random_operations() {
        let mut treap = create_simple_treap();
        let mut rng = rng();
        let mut reference = Vec::new();

        // Perform 100 random operations
        for _ in 0..100 {
            let op = rng.random_range(0..3);

            match op {
                0 => {
                    // Insert
                    let pos = if reference.is_empty() {
                        0
                    } else {
                        rng.random_range(0..=reference.len())
                    };
                    let val = rng.random_range(0..1000);
                    treap.insert(pos, val, &mut rng);
                    reference.insert(pos, val);
                }
                1 => {
                    // Delete
                    if !reference.is_empty() {
                        let pos = rng.random_range(0..reference.len());
                        treap.delete(pos);
                        reference.remove(pos);
                    }
                }
                _ => {
                    // Verify current state
                    let values = extract_values(&mut treap);
                    assert_eq!(values, reference);
                }
            }
        }

        // Final verification
        let values = extract_values(&mut treap);
        assert_eq!(values, reference);
    }

    #[test]
    fn test_multiple_range_updates() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5]
        for i in 1..=5 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Add 10 to range [0, 3) (indices 0, 1, 2)
        treap.update_range(0, 3, |node| node.d.lazy += 10);

        // Add 5 to range [2, 5) (indices 2, 3, 4)
        treap.update_range(2, 5, |node| node.d.lazy += 5);

        let values = extract_sum_values(&mut treap);
        assert_eq!(values, vec![11, 12, 18, 9, 10]); // [1+10, 2+10, 3+10+5, 4+5, 5+5]
    }

    #[test]
    fn test_overlapping_range_operations() {
        let mut treap = create_sum_treap();
        let mut rng = rng();

        // Insert values [1, 2, 3, 4, 5, 6]
        for i in 1..=6 {
            treap.insert(i - 1, i as i32, &mut rng);
        }

        // Add 10 to range [1, 4]
        treap.update_range(1, 5, |node| node.d.lazy += 10);

        // Query overlapping ranges
        let sum1 = treap.query_range(0, 3, |node| node.d.sum); // [1, 12, 13] = 26
        let sum2 = treap.query_range(2, 5, |node| node.d.sum); // [13, 14, 15] = 42
        let sum3 = treap.query_range(4, 6, |node| node.d.sum); // [15, 6] = 21

        assert_eq!(sum1, 26);
        assert_eq!(sum2, 42);
        assert_eq!(sum3, 21);
    }

    // Helper function to collect all values in order
    fn collect_values<D: Default + PartialEq>(
        treap: &mut Treap<i32, D, impl FnMut(&mut Node<i32, D>), impl FnMut(&mut Node<i32, D>)>,
    ) -> Vec<i32> {
        let mut values = Vec::new();
        treap.each(|x| values.push(*x));
        values
    }

    #[test]
    fn test_from_slice_empty() {
        let mut rng = rand::rng();
        let treap = Treap::<_, (), _, _>::from_slice(&[], |_| {}, |_| {}, &mut rng);
        let mut treap = treap;
        let values = collect_values(&mut treap);
        assert_eq!(values, Vec::<i32>::new());
    }

    #[test]
    fn test_from_slice_single_element() {
        let mut rng = rand::rng();
        let arr = [5];
        let mut treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![5]);
    }

    #[test]
    fn test_from_slice_multiple_elements() {
        let mut rng = rand::rng();
        let arr = [1, 3, 5, 7, 9, 11];
        let mut treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![1, 3, 5, 7, 9, 11]);
    }

    #[test]
    fn test_from_slice_then_insert() {
        let mut rng = rand::rng();
        let arr = [1, 3, 5, 7, 9];
        let mut treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);

        // Insert at beginning
        treap.insert(0, 0, &mut rng);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![0, 1, 3, 5, 7, 9]);

        // Insert in middle
        treap.insert(3, 4, &mut rng);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![0, 1, 3, 4, 5, 7, 9]);

        // Insert at end
        treap.insert(7, 10, &mut rng);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![0, 1, 3, 4, 5, 7, 9, 10]);
    }

    #[test]
    fn test_from_slice_then_delete() {
        let mut rng = rand::rng();
        let arr = [1, 3, 5, 7, 9, 11, 13];
        let mut treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);

        // Delete from beginning
        treap.delete(0);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![3, 5, 7, 9, 11, 13]);

        // Delete from middle
        treap.delete(2);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![3, 5, 9, 11, 13]);

        // Delete from end
        treap.delete(4);
        let values = collect_values(&mut treap);
        assert_eq!(values, vec![3, 5, 9, 11]);
    }

    #[test]
    fn test_from_slice_range_operations() {
        let mut rng = rand::rng();
        let arr = [1, 2, 3, 4, 5, 6, 7, 8];

        // Create treap with lazy propagation for range updates
        let mut treap = Treap::from_slice(
            &arr,
            |node| {
                // Push operation (for lazy propagation)
                if node.d != 0 {
                    node.x += node.d;
                    if let Some(ref mut left) = node.l {
                        left.d += node.d;
                    }
                    if let Some(ref mut right) = node.r {
                        right.d += node.d;
                    }
                    node.d = 0;
                }
            },
            |_| {}, // Pull operation (no aggregation needed for this test)
            &mut rng,
        );

        // Test range update: add 10 to elements at positions 2-5 (inclusive)
        treap.update_range(2, 6, |node| {
            node.d += 10;
        });

        let values = collect_values(&mut treap);
        assert_eq!(values, vec![1, 2, 13, 14, 15, 16, 7, 8]);
    }

    #[test]
    fn test_from_slice_with_sum_aggregation() {
        let mut rng = rand::rng();
        let arr = [1, 2, 3, 4, 5];

        // Create treap with sum aggregation in data field
        let mut treap = Treap::from_slice(
            &arr,
            |_| {}, // No lazy propagation for this test
            |node| {
                // Pull operation: compute sum of subtree
                let mut sum = node.x;
                if let Some(ref left) = node.l {
                    sum += left.d;
                }
                if let Some(ref right) = node.r {
                    sum += right.d;
                }
                node.d = sum;
            },
            &mut rng,
        );

        // Query sum of range [1, 4) (positions 1, 2, 3)
        let range_sum = treap.query_range(1, 4, |node| node.d);
        assert_eq!(range_sum, 2 + 3 + 4); // sum of elements at positions 1, 2, 3
    }

    #[test]
    fn test_from_slice_large_array() {
        let mut rng = rand::rng();
        let arr: Vec<i32> = (0..1000).collect();
        let mut treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);

        // Test that all elements are present and in order
        let values = collect_values(&mut treap);
        assert_eq!(values.len(), 1000);
        assert_eq!(values, arr);

        // Test some operations on large treap
        treap.insert(500, -1, &mut rng);
        treap.delete(0);
        treap.delete(999); // Now at position 999 since we deleted position 0

        let values = collect_values(&mut treap);
        assert_eq!(values.len(), 999);
        assert_eq!(values[0], 1); // First element is now 1 (0 was deleted)
        assert_eq!(values[499], -1); // Inserted element
        assert_eq!(values[500], 500); // Original element shifted
    }

    #[test]
    fn test_from_slice_heap_property() {
        let mut rng = rand::rng();
        let arr = [10, 20, 30, 40, 50];
        let treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);

        // Helper function to check heap property recursively
        fn check_heap_property<T, D>(node: &Option<Box<Node<T, D>>>) -> bool {
            match node {
                None => true,
                Some(n) => {
                    let left_ok = n.l.as_ref().map_or(true, |left| left.y <= n.y);
                    let right_ok = n.r.as_ref().map_or(true, |right| right.y <= n.y);
                    left_ok && right_ok && check_heap_property(&n.l) && check_heap_property(&n.r)
                }
            }
        }

        assert!(check_heap_property(&treap.root), "Heap property violated");
    }

    #[test]
    fn test_from_slice_count_property() {
        let mut rng = rand::rng();
        let arr = [1, 2, 3, 4, 5, 6, 7];
        let treap = Treap::<_, (), _, _>::from_slice(&arr, |_| {}, |_| {}, &mut rng);

        // Helper function to check count property recursively
        fn check_count_property<T, D>(node: &Option<Box<Node<T, D>>>) -> (bool, usize) {
            match node {
                None => (true, 0),
                Some(n) => {
                    let (left_ok, left_count) = check_count_property(&n.l);
                    let (right_ok, right_count) = check_count_property(&n.r);
                    let expected_count = left_count + right_count + 1;
                    let count_ok = n.c == expected_count;
                    (left_ok && right_ok && count_ok, expected_count)
                }
            }
        }

        let (property_ok, total_count) = check_count_property(&treap.root);
        assert!(property_ok, "Count property violated");
        assert_eq!(total_count, 7, "Total count mismatch");
    }
}
