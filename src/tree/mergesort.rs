#[derive(Clone, Debug)]
pub struct MergeSortTree<T> {
    t: Vec<Vec<T>>,
    n: usize,
}

impl<T> MergeSortTree<T>
where
    T: Clone + PartialOrd,
{
    /// O(n log n)
    pub fn new(a: &[T]) -> Self {
        let n = a.len();
        let mut t = vec![Vec::new(); n.next_power_of_two() << 1];
        let mut a = a
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i))
            .collect::<Vec<_>>();
        a.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        for (v, mut i) in a {
            i += n;
            while i > 0 {
                t[i].push(v.clone());
                i >>= 1;
            }
        }
        Self { t, n }
    }

    /// O(log^2 n)
    pub fn count_le(&self, mut l: usize, mut r: usize, k: T) -> usize {
        let n = self.n;
        let mut res = 0;
        l += n;
        r += n;
        while l < r {
            if l & 1 != 0 {
                res += self.t[l].partition_point(|x| x <= &k);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res += self.t[r].partition_point(|x| x <= &k);
            }
            l >>= 1;
            r >>= 1;
        }
        res
    }
}

#[derive(Clone, Debug)]
pub struct FCMergeSortTree<T> {
    t: Vec<Vec<T>>,
    li: Vec<Vec<usize>>,
    n: usize,
    m: usize,
}

impl<T> FCMergeSortTree<T>
where
    T: Clone + PartialOrd,
{
    /// O(n log n)
    pub fn new(a: &[T]) -> Self {
        let n = a.len();
        let m = if n == 0 { 1 } else { n.next_power_of_two() };
        let mut t = vec![Vec::new(); m * 2];
        let mut tl = vec![Vec::new(); m * 2];
        let mut a_sorted = a
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i))
            .collect::<Vec<_>>();
        a_sorted.sort_unstable_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        for (v, idx) in a_sorted {
            let mut u = idx + m;
            t[u].push(v.clone());
            u >>= 1;
            while u > 0 {
                t[u].push(v.clone());
                tl[u].push(t[u << 1].len());
                u >>= 1;
            }
        }
        Self { t, li: tl, n, m }
    }

    /// O(log n)
    pub fn count_le(&self, l: usize, r: usize, k: T) -> usize {
        if l >= r || self.n == 0 {
            return 0;
        }
        self.query_rec(1, 0, self.m, l, r, self.t[1].partition_point(|x| x <= &k))
    }

    fn query_rec(
        &self,
        u: usize,
        nl: usize,
        nr: usize,
        ql: usize,
        qr: usize,
        k_idx: usize,
    ) -> usize {
        if ql >= nr || qr <= nl {
            return 0;
        } else if ql <= nl && nr <= qr {
            return k_idx;
        }
        let m = nl + (nr - nl) / 2;
        let l_k_idx = if k_idx == 0 { 0 } else { self.li[u][k_idx - 1] };
        self.query_rec(2 * u, nl, m, ql, qr, l_k_idx)
            + self.query_rec(2 * u + 1, m, nr, ql, qr, k_idx - l_k_idx)
    }
}
