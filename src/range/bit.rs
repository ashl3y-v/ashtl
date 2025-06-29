pub struct BIT<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn new(mut bit: Vec<T>, mut f: F) -> Self {
        let n = bit.len();
        for i in 0..n {
            if i | i + 1 < n {
                bit[i | i + 1] = f(&bit[i | i + 1], &bit[i]);
            }
        }
        Self { bit, f }
    }

    pub fn update(&mut self, mut i: usize, d: T) -> &mut Self {
        while i < self.bit.len() {
            self.bit[i] = (self.f)(&self.bit[i], &d);
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, mut i: usize, identity: T) -> T {
        let mut res = identity;

        while i > 0 {
            res = (self.f)(&res, &self.bit[i - 1]);
            i &= i - 1;
        }
        res
    }
}

impl<T: PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT<T, F> {
    pub fn lower_bound(&self, max: T) -> usize {
        let mut pos = 0;

        let n = self.bit.len();
        let mut pw = usize::MAX.unbounded_shr(n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= n && self.bit[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}

pub struct BIT2D<T, F: FnMut(&T, &T) -> T> {
    bit: Vec<T>,
    n: usize,
    m: usize,
    f: F,
}

impl<T, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn new(mut bit: Vec<T>, n: usize, m: usize, mut f: F) -> Self {
        for i in 0..n {
            for j in 0..m {
                if j | j + 1 < m {
                    bit[i * m + (j | j + 1)] = f(&bit[i * m + (j | j + 1)], &bit[i * m + j]);
                }
            }
        }
        for i in 0..n {
            if i | i + 1 < n {
                for j in 0..m {
                    bit[(i | i + 1) * m + j] = f(&bit[(i | i + 1) * m + j], &bit[i * m + j]);
                }
            }
        }
        Self { bit, n, m, f }
    }

    pub fn update(&mut self, (mut i, j): (usize, usize), d: T) -> &mut Self {
        while i < self.n {
            let mut j = j;
            while j < self.m {
                self.bit[i * self.m + j] = (self.f)(&self.bit[i * self.m + j], &d);
                j |= j + 1;
            }
            i |= i + 1;
        }
        self
    }

    pub fn query(&mut self, (mut i, j): (usize, usize), identity: T) -> T {
        let mut res = identity;

        while i > 0 {
            let mut j = j;
            while j > 0 {
                res = (self.f)(&res, &self.bit[(i - 1) * self.m + j - 1]);
                j &= j - 1;
            }
            i &= i - 1;
        }
        res
    }
}

impl<T: std::cmp::PartialOrd<T>, F: FnMut(&T, &T) -> T> BIT2D<T, F> {
    pub fn lower_bound_row(&self, i: usize, max: T) -> usize {
        let mut pos = 0;

        let row = &self.bit[i * self.m..(i + 1) * self.m];
        let mut pw = usize::MAX.unbounded_shr(self.m.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.m && row[pos | pw - 1] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }

    pub fn lower_bound_col(&self, j: usize, max: T) -> usize {
        let mut pos = 0;

        let mut pw = usize::MAX.unbounded_shr(self.n.leading_zeros() + 1) + 1;
        while pw != 0 {
            if pos | pw <= self.n && self.bit[(pos | pw - 1) * self.m + j] < max {
                pos |= pw;
            };
            pw >>= 1;
        }

        pos
    }
}

#[cfg(test)]
mod tests {
    use super::{BIT, BIT2D};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    // Naïve prefix-sum helper for 1D
    fn naive_prefix<T: Copy + std::ops::Add<Output = T>>(a: &[T], idx: usize, identity: T) -> T {
        let mut sum = identity;
        for i in 0..idx {
            sum = sum + a[i];
        }
        sum
    }

    // Naïve rectangle-sum helper for 2D
    fn naive_rect<T: Copy + std::ops::Add<Output = T>>(
        a: &[T],
        n: usize,
        m: usize,
        hi: usize,
        hj: usize,
        identity: T,
    ) -> T {
        let mut sum = identity;
        for i in 0..hi {
            for j in 0..hj {
                sum = sum + a[i * m + j];
            }
        }
        sum
    }

    #[test]
    fn bit_sum_and_update_random() {
        let mut rng = StdRng::seed_from_u64(0x1234);
        for &n in &[1, 2, 7, 16, 31, 64, 100] {
            // build random base array
            let base: Vec<i64> = (0..n).map(|_| rng.random_range(-50..50)).collect();
            let mut bit = BIT::new(base.clone(), |&x, &y| x + y);
            // test all prefixes initially
            for q in 0..=n {
                assert_eq!(
                    bit.query(q, 0),
                    naive_prefix(&base, q, 0),
                    "initial prefix {} of len {}",
                    q,
                    n
                );
            }
            // random updates + re-query
            let mut arr = base.clone();
            for _ in 0..n * 3 {
                let idx = rng.random_range(0..n);
                let delta = rng.random_range(-30..30);
                arr[idx] += delta;
                bit.update(idx, delta);
                for q in 0..=n {
                    assert_eq!(
                        bit.query(q, 0),
                        naive_prefix(&arr, q, 0),
                        "after update at {}, prefix {}",
                        idx,
                        q
                    );
                }
            }
        }
    }

    #[test]
    fn bit_lower_bound_edge_cases() {
        // build non-decreasing bit: f = max
        let data = vec![1, 2, 2, 5, 5, 8, 10];
        let mut bit = BIT::new(data.clone(), |&x, &y| x.max(y));
        // lower_bound should find first prefix max >= target
        for target in 0..12 {
            let pos = bit.lower_bound(target);
            // brute force
            let mut want = 0;
            while want < data.len() && data[want] < target {
                want += 1;
            }
            assert_eq!(pos, want, "target {}", target);
        }
    }

    #[test]
    fn bit_1_element_and_empty() {
        // single element
        let mut bit = BIT::new(vec![42], |&x, &y| x + y);
        assert_eq!(bit.query(0, 0), 0);
        assert_eq!(bit.query(1, 0), 42);
        assert_eq!(bit.update(0, 5).query(1, 0), 47);

        // zero-length BIT should panic on new
        let result = std::panic::catch_unwind(|| {
            BIT::<i32, _>::new(vec![], |&a, &b| a + b);
        });
        assert!(
            result.is_ok(),
            "zero-length allowed but query/update will panic"
        );
    }

    #[test]
    fn bit2d_sum_and_update_random() {
        let mut rng = StdRng::seed_from_u64(0xdead_beef);
        for &(n, m) in &[(1, 1), (2, 3), (5, 5), (7, 4), (8, 8)] {
            let mut base: Vec<i64> = Vec::with_capacity(n * m);
            for _ in 0..n * m {
                base.push(rng.random_range(-20..20));
            }
            let mut bit2 = BIT2D::new(base.clone(), n, m, |&x, &y| x + y);

            // test all prefixes
            for hi in 0..=n {
                for hj in 0..=m {
                    let want = naive_rect(&base, n, m, hi, hj, 0);
                    assert_eq!(
                        bit2.query((hi, hj), 0),
                        want,
                        "init rect ({},{}) of {}×{}",
                        hi,
                        hj,
                        n,
                        m
                    );
                }
            }

            // random updates
            for _ in 0..(n * m) * 2 {
                let i = rng.random_range(0..n);
                let j = rng.random_range(0..m);
                let delta = rng.random_range(-15..15);
                base[i * m + j] += delta;
                bit2.update((i, j), delta);
                // re-test all prefixes
                for hi in 0..=n {
                    for hj in 0..=m {
                        let want = naive_rect(&base, n, m, hi, hj, 0);
                        assert_eq!(
                            bit2.query((hi, hj), 0),
                            want,
                            "after upd ({},{}) rect ({},{})",
                            i,
                            j,
                            hi,
                            hj
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn bit2d_lower_bound_per_row_and_col() {
        // construct row-wise non-decreasing for each row, and similarly columns
        let n = 4;
        let m = 5;
        let mut base = vec![0; n * m];
        for i in 0..n {
            for j in 0..m {
                base[i * m + j] = (i * 10 + j) as i64;
            }
        }
        let bit2 = BIT2D::new(base.clone(), n, m, |&x, &y| x.max(y));
        // rows
        for i in 0..n {
            for target in [
                -5_i64,
                0,
                i as i64 * 10,
                i as i64 * 10 + 2,
                i as i64 * 10 + 10,
                i as i64 * 10 + m as i64,
            ]
            .iter()
            .cloned()
            {
                let pos = bit2.lower_bound_row(i, target as i64);
                let mut want = 0;
                while want < m && base[i * m + want] < target {
                    want += 1;
                }
                assert_eq!(pos, want, "row {} target {}", i, target);
            }
        }
        // cols
        for j in 0..m {
            for target in [-1, 0, 10, 20, 30, 40].iter().cloned() {
                let pos = bit2.lower_bound_col(j, target);
                let mut want = 0;
                while want < n && base[want * m + j] < target {
                    want += 1;
                }
                assert_eq!(pos, want, "col {} target {}", j, target);
            }
        }
    }

    #[test]
    fn stress_small_sizes() {
        // brute force compare all small sizes up to 5×5 for sum, updates
        for n in 1..=5 {
            for m in 1..=5 {
                let mut base: Vec<i32> = (0..n * m).map(|x| x as i32).collect();
                let mut bit2 = BIT2D::new(base.clone(), n, m, |&x, &y| x + y);
                // do a full grid of updates
                for i in 0..n {
                    for j in 0..m {
                        let delta = (i + j) as i32;
                        base[i * m + j] += delta;
                        bit2.update((i, j), delta);
                        // test one random rect after each update
                        let hi = (i + 1).min(n);
                        let hj = (j + 1).min(m);
                        let want = naive_rect(&base, n, m, hi, hj, 0);
                        assert_eq!(bit2.query((hi, hj), 0), want);
                    }
                }
            }
        }
    }
}
