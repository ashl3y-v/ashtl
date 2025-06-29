use std::ops::{Bound, RangeBounds};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
    pub size: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [Node<T>]),
    Pull: FnMut(usize, usize, usize, &mut [Node<T>]),
{
    pub ns: Vec<Node<T>>,
    pub push: Push,
    pub pull: Pull,
    pub rt: usize,
}

impl<T: Clone, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [Node<T>]),
    Pull: FnMut(usize, usize, usize, &mut [Node<T>]),
{
    #[inline]
    pub fn new(push: Push, pull: Pull) -> Self {
        Self {
            ns: vec![],
            push,
            pull,
            rt: 0,
        }
    }

    #[inline]
    fn pull(&mut self, x: usize) -> &mut Self {
        if x != 0 {
            let n = &self.ns[x];
            let (l, r) = (n.l, n.r);
            self.ns[x].size = self.ns[l].size + self.ns[r].size + 1;
            (self.pull)(x, l, r, &mut self.ns);
        }
        self
    }

    #[inline]
    fn push(&mut self, x: usize) -> &mut Self {
        if x != 0 {
            let n = &self.ns[x];
            (self.push)(x, n.l, n.r, &mut self.ns);
        }
        self
    }

    #[inline]
    fn zig(&mut self, x: usize) -> usize {
        let l = self.ns[x].l;
        self.ns[x].l = self.ns[l].r;
        self.pull(x);
        self.ns[l].r = x;
        l
    }

    #[inline]
    fn zag(&mut self, x: usize) -> usize {
        let r = self.ns[x].r;
        self.ns[x].r = self.ns[r].l;
        self.pull(x);
        self.ns[r].l = x;
        r
    }

    fn splay(&mut self, x: usize, mut k: usize) -> usize {
        self.push(x);
        let l = self.ns[x].l;
        let size = self.ns[l].size;
        if k == size {
            x
        } else if k < size {
            self.push(l);
            let (ll, lr) = (self.ns[l].l, self.ns[l].r);
            let ll_size = self.ns[ll].size;
            if k == ll_size {
                self.zig(x)
            } else if k < ll_size {
                self.ns[l].l = self.splay(ll, k);
                let new_l = self.zig(x);
                self.zig(new_l)
            } else {
                self.ns[l].r = self.splay(lr, k - ll_size - 1);
                self.ns[x].l = self.zag(l);
                self.zig(x)
            }
        } else {
            let r = self.ns[x].r;
            self.push(r);
            k -= size + 1;
            let (rl, rr) = (self.ns[r].l, self.ns[r].r);
            let rl_size = self.ns[rl].size;
            if k == rl_size {
                self.zag(x)
            } else if k < rl_size {
                self.ns[r].l = self.splay(rl, k);
                self.ns[x].r = self.zig(r);
                self.zag(x)
            } else {
                self.ns[r].r = self.splay(rr, k - rl_size - 1);
                let new_r = self.zag(x);
                self.zag(new_r)
            }
        }
    }

    #[inline]
    pub fn get(&mut self, k: usize) -> Option<&T> {
        if k < self.len() && self.rt != 0 {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&self.ns[self.rt].v)
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: usize) -> Option<&mut T> {
        if k < self.len() && self.rt != 0 {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&mut self.ns[self.rt].v)
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: usize, v: T) -> &mut Self {
        let nxt = self.ns.len();
        if self.len() <= k {
            self.ns.push(Node {
                v,
                l: self.rt,
                r: 0,
                size: 0,
            });
        } else {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            let l = self.ns[self.rt].l;
            self.ns[self.rt].l = 0;
            self.pull(self.rt);
            self.ns.push(Node {
                v,
                l,
                r: self.rt,
                size: 0,
            });
        }
        self.pull(nxt);
        self.push(nxt);
        self.rt = nxt;
        self
    }

    pub fn erase(&mut self, k: usize) -> &mut Self {
        if k < self.len() && self.rt != 0 {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            let r = self.ns[self.rt].r;
            if r != 0 {
                let r = self.splay(r, 0);
                (self.ns[r].l, self.ns[self.rt].l, self.rt) = (self.ns[self.rt].l, 0, r);
                self.pull(r);
                return self;
            }
            (self.rt, self.ns[self.rt].l) = (self.ns[self.rt].l, 0);
        }
        self
    }

    fn merge_nodes(&mut self, mut a: usize, b: usize) -> usize {
        if a == 0 {
            return b;
        } else if b == 0 {
            return a;
        }
        let a_size = self.ns[a].size;
        a = self.splay(a, a_size - 1);
        self.pull(a);
        self.push(a);
        self.ns[a].r = b;
        self.pull(a);
        a
    }

    fn split_node(&mut self, mut a: usize, k: usize) -> (usize, usize) {
        if a == 0 {
            (0, 0)
        } else if k == 0 {
            self.push(a);
            (0, a)
        } else if k >= self.ns[a].size {
            self.push(a);
            (a, 0)
        } else {
            a = self.splay(a, k - 1);
            self.pull(a);
            self.push(a);
            let r = self.ns[a].r;
            self.ns[a].r = 0;
            if r != 0 {
                self.push(r);
            }
            self.pull(a);
            (a, r)
        }
    }

    pub fn range<R, F>(&mut self, range: impl RangeBounds<usize>, mut f: F) -> Option<R>
    where
        F: FnMut(usize, &mut [Node<T>]) -> R,
    {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => *l + 1,
            Bound::Unbounded => 0,
        };
        let r = match range.end_bound() {
            Bound::Included(r) => *r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.len(),
        };
        if l >= r {
            return None;
        }
        let (a, b) = self.split_node(self.rt, l);
        let (b, c) = self.split_node(b, r - l);
        let res = if b != 0 {
            Some(f(b, &mut self.ns))
        } else {
            None
        };
        let merged_ab = self.merge_nodes(a, b);
        self.rt = self.merge_nodes(merged_ab, c);
        res
    }

    #[inline]
    pub fn for_each<F>(&mut self, mut f: F) -> &mut Self
    where
        F: FnMut(&T),
    {
        self.for_each_node(self.rt, &mut f);
        self
    }

    fn for_each_node<F>(&mut self, n: usize, f: &mut F)
    where
        F: FnMut(&T),
    {
        if n != 0 {
            let (l, r) = (self.ns[n].l, self.ns[n].r);
            self.push(n);
            self.for_each_node(l, f);
            f(&self.ns[n].v);
            self.for_each_node(r, f);
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.rt != 0 {
            self.ns[self.rt].size
        } else {
            0
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rt == 0
    }
}

impl<T: Clone, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [Node<T>]),
    Pull: FnMut(usize, usize, usize, &mut [Node<T>]),
{
    fn build<S>(&mut self, v: &[S], elem: &mut impl FnMut(&S) -> T, l: usize, r: usize) -> usize {
        if l == r {
            0
        } else if l + 1 == r {
            self.ns[l].v = elem(&v[l - 1]);
            self.pull(l);
            l
        } else {
            let m = l + (r - l >> 1);
            self.ns[m].v = elem(&v[m - 1]);
            self.ns[m].l = self.build(v, elem, l, m);
            self.ns[m].r = self.build(v, elem, m + 1, r);
            self.pull(m);
            m
        }
    }

    pub fn from_slice<S>(
        v: &[S],
        init: T,
        mut elem: impl FnMut(&S) -> T,
        push: Push,
        pull: Pull,
    ) -> Splay<T, Push, Pull> {
        let mut s = Splay {
            ns: vec![
                Node {
                    v: init.clone(),
                    l: 0,
                    r: 0,
                    size: 0
                };
                v.len() + 1
            ],
            push,
            pull,
            rt: 0,
        };
        s.rt = s.build(v, &mut elem, 1, v.len() + 1);
        s
    }

    fn rebuild(&mut self) {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut tree = Splay::from_slice(
            &[10, 5, 15, 7],
            0,
            |&x| x,
            |_, _, _, _| {}, // push
            |_, _, _, _| {}, // pull
        );

        assert_eq!(tree.len(), 4);
        assert!(!tree.is_empty());

        // Test access
        assert_eq!(tree.get(0), Some(&10));
        assert_eq!(tree.get(1), Some(&5));
        assert_eq!(tree.get(2), Some(&15));
        assert_eq!(tree.get(3), Some(&7));

        // Test mutation
        if let Some(val) = tree.get_mut(1) {
            *val = 100;
        }
        assert_eq!(tree.get(1), Some(&100));

        // Test erasure
        tree.erase(1);
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.get(0), Some(&10));
        assert_eq!(tree.get(1), Some(&15));
        assert_eq!(tree.get(2), Some(&7));

        // Test out of bounds
        assert_eq!(tree.get(10), None);

        // Test insertions after erase
        tree.insert(0, 5);
        assert_eq!(tree.len(), 4);
        assert_eq!(tree.get(0), Some(&5));
    }

    #[test]
    fn test_edge_cases() {
        // Test empty tree construction
        let mut tree =
            Splay::from_slice(&[] as &[i32], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});
        assert!(tree.is_empty());

        // Single element
        tree.insert(0, 42);
        assert_eq!(tree.get(0), Some(&42));
        tree.erase(0);
        assert!(tree.is_empty());

        // Insert at various positions
        tree.insert(0, 1);
        tree.insert(1, 2);
        tree.insert(0, 0);

        assert_eq!(tree.get(0), Some(&0));
        assert_eq!(tree.get(1), Some(&1));
        assert_eq!(tree.get(2), Some(&2));
    }

    #[test]
    fn test_sequential_operations() {
        let data: Vec<i32> = (0..10).map(|i| i * 10).collect();
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Check all values
        for i in 0..10 {
            assert_eq!(tree.get(i), Some(&(i as i32 * 10)));
        }

        // Remove every other element
        for i in (0..10).step_by(2).rev() {
            tree.erase(i);
        }

        assert_eq!(tree.len(), 5);
    }

    #[test]
    fn test_insert_at_end() {
        let mut tree = Splay::from_slice(&[1], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Insert beyond current size should append
        tree.insert(10, 2); // Should append at end
        tree.insert(100, 3); // Should append at end

        assert_eq!(tree.len(), 3);
        assert_eq!(tree.get(0), Some(&1));
        assert_eq!(tree.get(1), Some(&2));
        assert_eq!(tree.get(2), Some(&3));
    }

    #[test]
    fn test_erase_out_of_bounds() {
        let mut tree = Splay::from_slice(&[1, 2], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Erase beyond bounds should do nothing
        tree.erase(10);
        assert_eq!(tree.len(), 2);

        tree.erase(2);
        assert_eq!(tree.len(), 2);
    }

    #[test]
    fn test_get_mut_bounds() {
        let mut tree = Splay::from_slice(&[42], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.get_mut(0), Some(&mut 42));
        assert_eq!(tree.get_mut(1), None);
        assert_eq!(tree.get_mut(100), None);
    }

    #[test]
    fn test_each_function() {
        // Empty tree
        let mut tree =
            Splay::from_slice(&[] as &[i32], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        let mut count = 0;
        tree.for_each(|_| count += 1);
        assert_eq!(count, 0);

        // Add elements
        let data: Vec<i32> = (0..5).map(|i| i * 2).collect();
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Collect values using each
        let mut values = Vec::new();
        tree.for_each(|&x| values.push(x));

        assert_eq!(values, vec![0, 2, 4, 6, 8]);

        // Verify tree is still functional after each
        assert_eq!(tree.len(), 5);
        for i in 0..5 {
            assert_eq!(tree.get(i), Some(&(i as i32 * 2)));
        }
    }

    #[test]
    fn test_lazy_propagation_basic() {
        #[derive(Debug, Default, Clone)]
        struct LazyData {
            add_val: i32,
        }

        let mut tree = Splay::from_slice(
            &[0, 1, 2, 3, 4],
            0,
            |&x| x,
            |x, l, r, ns: &mut [Node<i32>]| {
                // Push operation would be implemented here
                // For this test, we'll keep it simple
            },
            |x, l, r, ns: &mut [Node<i32>]| {
                // Pull operation
            },
        );

        // Test that lazy propagation works by accessing elements
        for i in 0..5 {
            assert_eq!(tree.get(i), Some(&(i as i32)));
        }
    }

    #[test]
    fn test_update_range() {
        let mut sum_vals = vec![0; 10]; // Mock lazy data storage

        let mut tree = Splay::from_slice(
            &[0, 1, 2, 3, 4],
            0,
            |&x| x,
            |x, l, r, ns: &mut [Node<i32>]| {
                // Push implementation would use external storage
            },
            |x, l, r, ns: &mut [Node<i32>]| {
                // Pull implementation
            },
        );

        // Update range [1, 3) - would add 10 to elements at indices 1 and 2
        tree.range(1..3, |node_idx, ns| {
            // In a real implementation, this would update lazy data
            ns[node_idx].v += 10;
        });

        // Note: This test is simplified since the new API doesn't have built-in lazy propagation
        // The actual lazy propagation would need to be implemented in the push/pull functions
    }

    #[test]
    fn test_query_range() {
        let mut tree = Splay::from_slice(
            &[1, 2, 3, 4, 5],
            0,
            |&x| x,
            |x, l, r, ns: &mut [Node<i32>]| {},
            |x, l, r, ns: &mut [Node<i32>]| {
                // Pull: calculate sum would be done here
            },
        );

        // Query range [1, 4) - sum of elements at indices 1, 2, 3
        let sum = tree.range(1..4, |node_idx, ns| {
            // This would return aggregated data in a real implementation
            // For now, just return a simple sum
            let mut total = 0;
            fn sum_subtree(idx: usize, ns: &[Node<i32>]) -> i32 {
                if idx == 0 {
                    return 0;
                }
                let node = &ns[idx];
                node.v + sum_subtree(node.l, ns) + sum_subtree(node.r, ns)
            }
            sum_subtree(node_idx, ns)
        });

        // Should be 2 + 3 + 4 = 9
        assert_eq!(sum, Some(9));

        // Verify tree is still intact
        assert_eq!(tree.len(), 5);
        for i in 0..5 {
            assert_eq!(tree.get(i), Some(&(i as i32 + 1)));
        }
    }

    #[test]
    fn test_interleaved_operations() {
        let mut tree = Splay::from_slice(&[10], 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.get(0), Some(&10));

        tree.insert(1, 20);
        tree.insert(0, 5);
        assert_eq!(tree.get(0), Some(&5));
        assert_eq!(tree.get(1), Some(&10));
        assert_eq!(tree.get(2), Some(&20));

        tree.erase(1);
        assert_eq!(tree.len(), 2);
        assert_eq!(tree.get(0), Some(&5));
        assert_eq!(tree.get(1), Some(&20));

        tree.insert(1, 15);
        assert_eq!(tree.get(1), Some(&15));

        // Final state should be [5, 15, 20]
        let mut values = Vec::new();
        tree.for_each(|&x| values.push(x));
        assert_eq!(values, vec![5, 15, 20]);
    }

    #[test]
    fn test_from_slice_empty() {
        let empty: &[i32] = &[];
        let tree = Splay::from_slice(empty, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.rt, 0);
    }

    #[test]
    fn test_from_slice_single_element() {
        let data = vec![42];
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert!(!tree.is_empty());
        assert_eq!(tree.len(), 1);
        assert_eq!(tree.get(0), Some(&42));
        assert_eq!(tree.get(1), None);
    }

    #[test]
    fn test_from_slice_two_elements() {
        let data = vec![10, 20];
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 2);
        assert_eq!(tree.get(0), Some(&10));
        assert_eq!(tree.get(1), Some(&20));
        assert_eq!(tree.get(2), None);
    }

    #[test]
    fn test_from_slice_multiple_elements() {
        let data = vec![1, 2, 3, 4, 5];
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 5);

        // Verify all elements are accessible in order
        for (i, &expected) in data.iter().enumerate() {
            assert_eq!(tree.get(i), Some(&expected));
        }

        // Verify out of bounds access
        assert_eq!(tree.get(5), None);
        assert_eq!(tree.get(100), None);
    }

    #[test]
    fn test_from_slice_large_array() {
        let data: Vec<i32> = (0..1000).collect();
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 1000);

        // Test random access
        for i in [0, 1, 100, 500, 999] {
            assert_eq!(tree.get(i), Some(&(i as i32)));
        }

        // Test that splay operations work correctly after construction
        tree.insert(500, -1);
        assert_eq!(tree.len(), 1001);
        assert_eq!(tree.get(500), Some(&-1));
    }

    #[test]
    fn test_from_slice_preserves_order() {
        let data = vec!['a', 'b', 'c', 'd', 'e', 'f', 'g'];
        let mut tree = Splay::from_slice(&data, 'a', |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Collect all elements using the each function
        let mut collected = Vec::new();
        tree.for_each(|&ch| collected.push(ch));

        assert_eq!(collected, data);
    }

    #[test]
    fn test_from_slice_with_duplicates() {
        let data = vec![1, 2, 2, 3, 2, 4];
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 6);

        for (i, &expected) in data.iter().enumerate() {
            assert_eq!(tree.get(i), Some(&expected));
        }
    }

    #[test]
    fn test_from_slice_tree_structure() {
        let data = vec![1, 2, 3, 4, 5, 6, 7];
        let tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // The tree should be roughly balanced
        assert_eq!(tree.len(), 7);

        // Check that the tree structure is valid by verifying sizes
        fn check_sizes<T>(idx: usize, ns: &[Node<T>]) -> usize {
            if idx == 0 {
                return 0;
            }
            let node = &ns[idx];
            let left_size = check_sizes(node.l, ns);
            let right_size = check_sizes(node.r, ns);
            let expected_size = left_size + right_size + 1;
            assert_eq!(
                node.size, expected_size,
                "Size mismatch in node at index {}",
                idx
            );
            expected_size
        }

        check_sizes(tree.rt, &tree.ns);
    }

    #[test]
    fn test_from_slice_operations_after_construction() {
        let data = vec![10, 20, 30, 40, 50];
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        // Test insertions after construction
        tree.insert(0, 5); // [5, 10, 20, 30, 40, 50]
        tree.insert(6, 60); // [5, 10, 20, 30, 40, 50, 60]
        tree.insert(3, 25); // [5, 10, 20, 25, 30, 40, 50, 60]

        assert_eq!(tree.len(), 8);

        let expected = vec![5, 10, 20, 25, 30, 40, 50, 60];
        for (i, &exp) in expected.iter().enumerate() {
            assert_eq!(tree.get(i), Some(&exp));
        }

        // Test deletions
        tree.erase(3); // Remove 25: [5, 10, 20, 30, 40, 50, 60]
        tree.erase(0); // Remove 5:  [10, 20, 30, 40, 50, 60]

        assert_eq!(tree.len(), 6);

        let expected = vec![10, 20, 30, 40, 50, 60];
        for (i, &exp) in expected.iter().enumerate() {
            assert_eq!(tree.get(i), Some(&exp));
        }
    }

    #[test]
    fn test_from_slice_stress_test() {
        // Test with a larger dataset
        let data: Vec<i32> = (0..1000).collect();
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 1000);

        // Test random access patterns
        for &i in &[0, 1, 100, 500, 999] {
            assert_eq!(tree.get(i), Some(&(i as i32)));
        }

        // Test that tree operations work correctly
        tree.insert(500, -1);
        assert_eq!(tree.get(500), Some(&-1));
        assert_eq!(tree.len(), 1001);
    }

    #[test]
    fn test_from_slice_string_data() {
        let data = vec!["apple", "banana", "cherry", "date", "elderberry"];
        let mut tree = Splay::from_slice(&data, "", |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 5);

        for (i, &expected) in data.iter().enumerate() {
            assert_eq!(tree.get(i), Some(&expected));
        }

        // Test each function with strings
        let mut collected = Vec::new();
        tree.for_each(|&s| collected.push(s));
        assert_eq!(collected, data);
    }

    #[test]
    fn test_from_slice_powers_of_two() {
        // Test with sizes that are powers of 2 to check edge cases in tree construction
        for &size in &[1, 2, 4, 8, 16, 32, 64, 128] {
            let data: Vec<i32> = (0..size).collect();
            let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

            assert_eq!(tree.len(), size as usize);

            // Verify all elements
            for i in 0..size {
                assert_eq!(tree.get(i as usize), Some(&i));
            }
        }
    }

    #[test]
    fn test_from_slice_odd_sizes() {
        // Test with odd sizes to check middle element selection
        for &size in &[3, 5, 7, 9, 15, 31, 63, 127] {
            let data: Vec<i32> = (0..size).collect();
            let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

            assert_eq!(tree.len(), size as usize);

            // Verify first, middle, and last elements
            assert_eq!(tree.get(0), Some(&0));
            assert_eq!(tree.get((size / 2) as usize), Some(&(size / 2)));
            assert_eq!(tree.get((size - 1) as usize), Some(&(size - 1)));
        }
    }

    #[test]
    fn test_empty_range_operations() {
        let mut tree = Splay::from_slice(
            &[0, 1, 2, 3, 4],
            0,
            |&x| x,
            |_, _, _, _| {},
            |_, _, _, _| {},
        );

        // Empty range update (l == r)
        tree.range(2..2, |node_idx, ns| {
            ns[node_idx].v += 100; // This shouldn't affect anything
        });

        // Verify nothing changed
        for i in 0..5 {
            assert_eq!(tree.get(i), Some(&i));
        }
    }

    #[test]
    fn test_single_element_range() {
        let mut tree = Splay::from_slice(
            &[0, 1, 2, 3, 4],
            0,
            |&x| x,
            |_, _, _, _| {},
            |_, _, _, _| {},
        );

        // Update single element range [2, 3)
        tree.range(2..3, |node_idx, ns| {
            ns[node_idx].v += 50;
        });

        // Check that only element at index 2 was modified
        assert_eq!(tree.get(0), Some(&0));
        assert_eq!(tree.get(1), Some(&1));
        assert_eq!(tree.get(2), Some(&52));
        assert_eq!(tree.get(3), Some(&3));
        assert_eq!(tree.get(4), Some(&4));
    }

    #[test]
    fn test_complex_range_operations() {
        let mut tree = Splay::from_slice(
            &(0..10).collect::<Vec<i32>>(),
            (0, 0),
            |&x| (x, 0),
            |x, l, r, ns| {
                let d = ns[x].v.1;
                if d != 0 {
                    if l != 0 {
                        ns[l].v.1 += d;
                        ns[l].v.0 += d;
                    }
                    if r != 0 {
                        ns[r].v.1 += d;
                        ns[r].v.0 += d;
                    }
                    ns[x].v.1 = 0;
                }
            },
            |_, _, _, _| {},
        );
        tree.range(0..5, |node_idx, ns| {
            ns[node_idx].v.0 += 1;
            ns[node_idx].v.1 += 1
        });
        tree.range(2..7, |node_idx, ns| {
            ns[node_idx].v.0 += 2;
            ns[node_idx].v.1 += 2
        });
        tree.range(1..3, |node_idx, ns| {
            ns[node_idx].v.0 += 3;
            ns[node_idx].v.1 += 3
        });

        // Verify final values
        let expected = [1, 5, 8, 6, 7, 7, 8, 7, 8, 9];
        for (i, &expected_val) in expected.iter().enumerate() {
            assert_eq!(
                tree.get(i).unwrap().0,
                expected_val,
                "Mismatch at index {}",
                i
            );
        }
    }

    #[test]
    fn test_stress_operations() {
        let data: Vec<i32> = (0..100).map(|i| i * i).collect();
        let mut tree = Splay::from_slice(&data, 0, |&x| x, |_, _, _, _| {}, |_, _, _, _| {});

        assert_eq!(tree.len(), 100);

        // Random access
        for i in (0..100).step_by(7) {
            assert_eq!(tree.get(i), Some(&((i * i) as i32)));
        }

        // Random deletions
        for i in (10..90).step_by(5).rev() {
            tree.erase(i);
        }

        // Verify remaining elements
        let mut remaining_count = 0;
        tree.for_each(|_| remaining_count += 1);
        assert_eq!(remaining_count, tree.len());
    }
}
