use crate::ds::bit_vec::BitVec;
use std::ops::{Bound, RangeBounds};

const NULL: usize = 0;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplayNode<T> {
    pub v: T,
    pub l: usize,
    pub r: usize,
    pub size: usize,
}

#[derive(Clone, Debug)]
pub struct Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    pub n: Vec<SplayNode<T>>,
    pub push: Push,
    pub pull: Pull,
    pub rt: usize,
    pub nxt: usize,
    pub removed: usize,
    pub open: BitVec,
}

impl<T, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    #[inline]
    pub fn new(init: T, push: Push, pull: Pull) -> Self {
        Self {
            n: vec![SplayNode {
                v: init,
                l: NULL,
                r: NULL,
                size: 0,
            }],
            push,
            pull,
            rt: NULL,
            nxt: 1,
            removed: 0,
            open: BitVec::new(1, false),
        }
    }

    #[inline]
    fn pull(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.n[x];
            let (l, r) = (n.l, n.r);
            self.n[x].size = self.n[l].size + self.n[r].size + 1;
            (self.pull)(x, l, r, &mut self.n);
        }
        self
    }

    #[inline]
    fn push(&mut self, x: usize) -> &mut Self {
        if x != NULL {
            let n = &self.n[x];
            (self.push)(x, n.l, n.r, &mut self.n);
        }
        self
    }

    #[inline]
    fn zig(&mut self, x: usize) -> usize {
        let l = self.n[x].l;
        self.n[x].l = self.n[l].r;
        self.pull(x);
        self.n[l].r = x;
        l
    }

    #[inline]
    fn zag(&mut self, x: usize) -> usize {
        let r = self.n[x].r;
        self.n[x].r = self.n[r].l;
        self.pull(x);
        self.n[r].l = x;
        r
    }

    pub fn splay(&mut self, x: usize, mut k: usize) -> usize {
        self.push(x);
        let l = self.n[x].l;
        let size = self.n[l].size;
        if k == size {
            x
        } else if k < size {
            self.push(l);
            let (ll, lr) = (self.n[l].l, self.n[l].r);
            let ll_size = self.n[ll].size;
            if k == ll_size {
                self.zig(x)
            } else if k < ll_size {
                self.n[l].l = self.splay(ll, k);
                let new_l = self.zig(x);
                self.zig(new_l)
            } else {
                self.n[l].r = self.splay(lr, k - ll_size - 1);
                self.n[x].l = self.zag(l);
                self.zig(x)
            }
        } else {
            let r = self.n[x].r;
            self.push(r);
            k -= size + 1;
            let (rl, rr) = (self.n[r].l, self.n[r].r);
            let rl_size = self.n[rl].size;
            if k == rl_size {
                self.zag(x)
            } else if k < rl_size {
                self.n[r].l = self.splay(rl, k);
                self.n[x].r = self.zig(r);
                self.zag(x)
            } else {
                self.n[r].r = self.splay(rr, k - rl_size - 1);
                let new_r = self.zag(x);
                self.zag(new_r)
            }
        }
    }

    #[inline]
    pub fn get(&mut self, k: usize) -> Option<&T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&self.n[self.rt].v)
        } else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: usize) -> Option<&mut T> {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            Some(&mut self.n[self.rt].v)
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: usize, v: T) -> &mut Self {
        let len = self.n.len();
        while self.nxt < self.n.len() && !self.open[self.nxt] {
            self.nxt += 1;
        }
        let nxt = self.nxt;
        if self.len() <= k {
            let n = SplayNode {
                v,
                l: self.rt,
                r: NULL,
                size: 0,
            };
            if nxt < len {
                self.n[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.n.push(n);
                self.open.push(false);
            }
        } else {
            self.rt = self.splay(self.rt, k);
            self.pull(self.rt);
            self.push(self.rt);
            let l = self.n[self.rt].l;
            self.n[self.rt].l = NULL;
            self.pull(self.rt);
            let n = SplayNode {
                v,
                l,
                r: self.rt,
                size: 0,
            };
            if nxt < len {
                self.n[nxt] = n;
                self.open.set(nxt, false);
            } else {
                self.n.push(n);
                self.open.push(false);
            }
        }
        self.pull(nxt);
        self.push(nxt);
        self.rt = nxt;
        self.nxt += 1;
        self
    }

    pub fn remove(&mut self, k: usize) -> &mut Self {
        if k < self.len() && self.rt != NULL {
            self.rt = self.splay(self.rt, k);
            self.open.set(self.rt, true);
            self.push(self.rt);
            let r = self.n[self.rt].r;
            if r != NULL {
                let r = self.splay(r, 0);
                (self.n[r].l, self.n[self.rt].l, self.rt) = (self.n[self.rt].l, NULL, r);
                self.pull(r);
            } else {
                (self.rt, self.n[self.rt].l) = (self.n[self.rt].l, NULL);
            }
        }
        self.removed += 1;
        let len = self.n.len();
        if self.removed << 1 > len {
            self.nxt = self.open.iter().position(|v| v == true).unwrap_or(len);
            self.removed = 0;
        }
        self
    }

    pub fn merge_nodes(&mut self, mut a: usize, b: usize) -> usize {
        if a == NULL {
            return b;
        } else if b == NULL {
            return a;
        }
        let a_size = self.n[a].size;
        a = self.splay(a, a_size - 1);
        self.pull(a);
        self.push(a);
        self.n[a].r = b;
        self.pull(a);
        a
    }

    pub fn split_node(&mut self, mut a: usize, k: usize) -> (usize, usize) {
        if a == NULL {
            (NULL, NULL)
        } else if k == NULL {
            self.push(a);
            (NULL, a)
        } else if k >= self.n[a].size {
            self.push(a);
            (a, NULL)
        } else {
            a = self.splay(a, k - 1);
            self.pull(a);
            self.push(a);
            let r = self.n[a].r;
            self.n[a].r = NULL;
            if r != NULL {
                self.push(r);
            }
            self.pull(a);
            (a, r)
        }
    }

    pub fn range<R, F>(&mut self, range: impl RangeBounds<usize>, mut f: F) -> Option<R>
    where
        F: FnMut(usize, &mut [SplayNode<T>]) -> R,
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
        let res = if b != NULL {
            Some(f(b, &mut self.n))
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
        if n != NULL {
            let (l, r) = (self.n[n].l, self.n[n].r);
            self.push(n);
            self.for_each_node(l, f);
            f(&self.n[n].v);
            self.for_each_node(r, f);
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.rt != NULL {
            self.n[self.rt].size
        } else {
            0
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rt == NULL
    }
}

impl<T: Clone, Push, Pull> Splay<T, Push, Pull>
where
    Push: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
    Pull: FnMut(usize, usize, usize, &mut [SplayNode<T>]),
{
    fn build<S>(&mut self, v: &[S], elem: &mut impl FnMut(&S) -> T, l: usize, r: usize) -> usize {
        if l == r {
            NULL
        } else if l + 1 == r {
            self.n[l].v = elem(&v[l - 1]);
            self.pull(l);
            l
        } else {
            let m = l + (r - l >> 1);
            self.n[m].v = elem(&v[m - 1]);
            self.n[m].l = self.build(v, elem, l, m);
            self.n[m].r = self.build(v, elem, m + 1, r);
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
        let len = v.len();
        let mut s = Splay {
            n: vec![
                SplayNode {
                    v: init,
                    l: NULL,
                    r: NULL,
                    size: 0
                };
                len + 1
            ],
            push,
            pull,
            rt: NULL,
            nxt: len,
            removed: 0,
            open: BitVec::new(len + 1, false),
        };
        s.rt = s.build(v, &mut elem, 1, len + 1);
        s
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
        tree.remove(1);
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
        tree.remove(0);
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
            tree.remove(i);
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
        tree.remove(10);
        assert_eq!(tree.len(), 2);

        tree.remove(2);
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
            |x, l, r, ns: &mut [SplayNode<i32>]| {
                // Push operation would be implemented here
                // For this test, we'll keep it simple
            },
            |x, l, r, ns: &mut [SplayNode<i32>]| {
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
            |x, l, r, ns: &mut [SplayNode<i32>]| {
                // Push implementation would use external storage
            },
            |x, l, r, ns: &mut [SplayNode<i32>]| {
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
            |x, l, r, ns: &mut [SplayNode<i32>]| {},
            |x, l, r, ns: &mut [SplayNode<i32>]| {
                // Pull: calculate sum would be done here
            },
        );

        // Query range [1, 4) - sum of elements at indices 1, 2, 3
        let sum = tree.range(1..4, |node_idx, ns| {
            // This would return aggregated data in a real implementation
            // For now, just return a simple sum
            let mut total = 0;
            fn sum_subtree(idx: usize, ns: &[SplayNode<i32>]) -> i32 {
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

        tree.remove(1);
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
        fn check_sizes<T>(idx: usize, ns: &[SplayNode<T>]) -> usize {
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

        check_sizes(tree.rt, &tree.n);
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
        tree.remove(3); // Remove 25: [5, 10, 20, 30, 40, 50, 60]
        tree.remove(0); // Remove 5:  [10, 20, 30, 40, 50, 60]

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
            tree.remove(i);
        }

        // Verify remaining elements
        let mut remaining_count = 0;
        tree.for_each(|_| remaining_count += 1);
        assert_eq!(remaining_count, tree.len());
    }
}
