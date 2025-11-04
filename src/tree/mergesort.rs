pub struct MergeSortTree<T> {
    t: Vec<Vec<T>>,
    n: usize,
}

impl<T> MergeSortTree<T>
where
    T: Copy + Ord,
{
    pub fn new(a: &[T]) -> Self {
        let n = a.len();
        let mut t = vec![Vec::new(); n.next_power_of_two() << 1];
        let mut a = a
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, i))
            .collect::<Vec<_>>();
        a.sort_unstable();
        for (v, mut i) in a {
            i += n;
            while i > 0 {
                t[i].push(v);
                i >>= 1;
            }
        }
        Self { t, n }
    }

    fn _merge(a: &[T], b: &[T]) -> Vec<T> {
        let mut res = Vec::with_capacity(a.len() + b.len());
        let mut i = 0;
        let mut j = 0;
        while i < a.len() && j < b.len() {
            if a[i] < b[j] {
                res.push(a[i]);
                i += 1;
            } else {
                res.push(b[j]);
                j += 1;
            }
        }
        res.extend_from_slice(&a[i..]);
        res.extend_from_slice(&b[j..]);
        res
    }

    pub fn count_le(&self, mut l: usize, mut r: usize, k: T) -> usize {
        let n = self.n;
        let mut res = 0;
        l += n;
        r += n;
        while l < r {
            if l & 1 != 0 {
                res += self.t[l].partition_point(|&x| x <= k);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res += self.t[r].partition_point(|&x| x <= k);
            }
            l >>= 1;
            r >>= 1;
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let a: Vec<i32> = vec![];
        let tree = MergeSortTree::new(&a);
        assert_eq!(tree.count_le(0, 0, 100), 0);
    }

    #[test]
    fn test_single_element() {
        let a = [5];
        let tree = MergeSortTree::new(&a);
        assert_eq!(tree.count_le(0, 1, 4), 0);
        assert_eq!(tree.count_le(0, 1, 5), 1);
        assert_eq!(tree.count_le(0, 1, 6), 1);
    }

    #[test]
    fn test_simple_array() {
        let a = [1, 5, 2, 8, 3];
        let tree = MergeSortTree::new(&a);

        // Full range [0, 5)
        assert_eq!(tree.count_le(0, 5, 0), 0); // None <= 0
        assert_eq!(tree.count_le(0, 5, 1), 1); // {1}
        assert_eq!(tree.count_le(0, 5, 4), 3); // {1, 2, 3}
        assert_eq!(tree.count_le(0, 5, 8), 5); // {1, 5, 2, 8, 3}
        assert_eq!(tree.count_le(0, 5, 100), 5); // All

        // Partial range [1, 4) -> elements {5, 2, 8}
        assert_eq!(tree.count_le(1, 4, 1), 0);
        assert_eq!(tree.count_le(1, 4, 2), 1); // {2}
        assert_eq!(tree.count_le(1, 4, 6), 2); // {5, 2}
        assert_eq!(tree.count_le(1, 4, 8), 3); // {5, 2, 8}

        // Partial range [0, 2) -> elements {1, 5}
        assert_eq!(tree.count_le(0, 2, 3), 1); // {1}

        // Partial range [3, 5) -> elements {8, 3}
        assert_eq!(tree.count_le(3, 5, 7), 1); // {3}
        assert_eq!(tree.count_le(3, 5, 8), 2); // {8, 3}
    }

    #[test]
    fn test_with_duplicates() {
        let a = [5, 2, 5, 1, 8, 2];
        let tree = MergeSortTree::new(&a);

        // Full range [0, 6)
        assert_eq!(tree.count_le(0, 6, 2), 3); // {2, 1, 2}
        assert_eq!(tree.count_le(0, 6, 5), 5); // {5, 2, 5, 1, 2}

        // Partial range [1, 4) -> elements {2, 5, 1}
        assert_eq!(tree.count_le(1, 4, 0), 0);
        assert_eq!(tree.count_le(1, 4, 1), 1); // {1}
        assert_eq!(tree.count_le(1, 4, 3), 2); // {2, 1}
        assert_eq!(tree.count_le(1, 4, 5), 3); // {2, 5, 1}

        // Partial range [0, 3) -> elements {5, 2, 5}
        assert_eq!(tree.count_le(0, 3, 4), 1); // {2}
        assert_eq!(tree.count_le(0, 3, 5), 3); // {5, 2, 5}
    }

    #[test]
    fn test_sorted_array() {
        let a = [10, 20, 30, 40, 50];
        let tree = MergeSortTree::new(&a);

        // Full range [0, 5)
        assert_eq!(tree.count_le(0, 5, 30), 3); // {10, 20, 30}
        assert_eq!(tree.count_le(0, 5, 35), 3); // {10, 20, 30}
        assert_eq!(tree.count_le(0, 5, 9), 0);

        // Partial range [2, 4) -> elements {30, 40}
        assert_eq!(tree.count_le(2, 4, 29), 0);
        assert_eq!(tree.count_le(2, 4, 30), 1); // {30}
        assert_eq!(tree.count_le(2, 4, 40), 2); // {30, 40}
    }

    #[test]
    fn test_reverse_sorted_array() {
        let a = [5, 4, 3, 2, 1];
        let tree = MergeSortTree::new(&a);

        // Full range [0, 5)
        assert_eq!(tree.count_le(0, 5, 3), 3); // {3, 2, 1}

        // Partial range [1, 4) -> elements {4, 3, 2}
        assert_eq!(tree.count_le(1, 4, 3), 2); // {3, 2}
        assert_eq!(tree.count_le(1, 4, 1), 0);
        assert_eq!(tree.count_le(1, 4, 5), 3); // {4, 3, 2}
    }
}
