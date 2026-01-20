use crate::{alg::fps::Poly, ds::scan::MonotoneQueue, opt::min_plus::max_plus_cvx};

/// O(n M)
pub fn subset_sum(w: &[u64], t: u64) -> u64 {
    let (mut a, mut b) = (0, 0);
    while b < w.len() && a + w[b] <= t {
        a += w[b];
        b += 1;
    }
    if b == w.len() {
        return a;
    }
    let m = w.iter().max().cloned().unwrap_or(0);
    let mut u;
    let mut v = vec![-1; (m as usize) << 1];
    v[(a + m - t) as usize] = b as i64;
    for i in b..w.len() {
        u = v.clone();
        for x in 0..m as usize {
            v[x + w[i] as usize] = v[x + w[i] as usize].max(u[x]);
            let mut x = (m as usize) << 1;
            while {
                x -= 1;
                x > m as usize
            } {
                for j in 0.max(u[x])..v[x] {
                    v[x - w[j as usize] as usize] = v[x - w[j as usize] as usize].max(j);
                }
            }
        }
    }
    let mut a = t;
    while a > 0 && v[(a + m - t) as usize] < 0 {
        a -= 1;
    }
    a
}

// https://arxiv.org/pdf/1802.06440
/// O(d c)
pub fn zero_one_knapsack(v: &[u64], w: &[u64], c: u64) -> u64 {
    let n = v.len();
    let mut bucket = vec![Vec::new(); c as usize + 1];
    for i in 0..n {
        if w[i] <= c {
            bucket[w[i] as usize].push(v[i]);
        }
    }
    let mut dp = vec![0; c as usize + 1];
    dp[0] = 0;
    for w in 1..=c as usize {
        let list = &mut bucket[w];
        if list.is_empty() {
            continue;
        }
        list.sort_unstable_by(|a, b| b.cmp(a));
        let m = list.len().min(c as usize / w);
        let mut sum = Vec::with_capacity(m + 1);
        sum.push(0);
        let mut current_sum = 0;
        for &val in &list[0..m] {
            current_sum += val;
            sum.push(current_sum);
        }
        for k in 0..w as usize {
            let n = (c as usize - k) / w + 1;
            if n == 0 {
                continue;
            }
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(dp[i * w + k]);
            }
            let res = max_plus_cvx(&v, &sum);
            for i in 0..n {
                dp[i * w + k] = res[i];
            }
        }
    }
    *dp.iter().max().unwrap_or(&0)
}

/// O(n + c log c)
pub fn zero_one_knapsack_eq<const M: u64>(w: &[usize], c: usize) -> Vec<u64> {
    Poly::<M>::log_prod_1pxit(1, w.into_iter().cloned(), c + 1)
        .exp(c + 1)
        .unwrap()
        .coeff
        .into_iter()
        .map(|i| i.rem_euclid(M as i64) as u64)
        .collect::<Vec<_>>()
}

// https://arxiv.org/pdf/1802.06440
/// O(min(n c, M^2 log M, V^2 log V))
pub fn complete_knapsack(v: &[u64], w: &[u64], mut c: u64) -> u64 {
    let n = v.len();
    if n == 0 {
        return 0;
    }
    let max_v = v.iter().max().copied().unwrap_or(0);
    let max_w = w.iter().max().copied().unwrap_or(0);
    if max_v <= 0 || max_w == 0 {
        return 0;
    }
    if n as u64 * c <= 10 * max_v.min(max_w).pow(2) {
        let cap = c as usize;
        let mut dp = vec![0u64; cap + 1];
        for i in 0..n {
            let weight = w[i] as usize;
            let value = v[i];
            if weight <= cap && weight > 0 {
                for j in weight..=cap {
                    dp[j] = dp[j].max(dp[j - weight] + value);
                }
            }
        }
        return dp[cap];
    }
    let limit = max_w.pow(2);
    let mut best_idx = 0;
    let mut max_density = -1.0;
    for i in 0..n {
        if w[i] == 0 {
            continue;
        }
        let density = v[i] as f64 / w[i] as f64;
        if density > max_density {
            max_density = density;
            best_idx = i;
        }
    }
    let best_w = w[best_idx];
    let best_v = v[best_idx];
    if max_w <= max_v {
        let reduce_count = if limit < c { (c - limit) / best_w } else { 0 };
        c -= reduce_count * best_w;
        let minf = i64::MIN / 2;
        let m = max_w;
        let k = m as usize + 1;
        let mut dp = vec![minf; k];
        dp[0] = 0;
        for i in 0..n {
            dp[w[i] as usize] = dp[w[i] as usize].max(v[i] as i64);
        }
        let mut z = 1;
        while z < m {
            let mut dp_new = vec![minf; k];
            for i in 0..k {
                for j in 0..k - i {
                    dp_new[i + j] = dp_new[i + j].max(dp[i] + dp[j]);
                }
            }
            dp = dp_new;
            z <<= 1;
        }
        let mut padded_dp = vec![minf; m as usize];
        padded_dp.extend(dp);
        dp = padded_dp;
        let lg = i64::BITS - c.leading_zeros();
        let len = dp.len();
        for i in (1..=lg).rev() {
            let mut dp_new = vec![minf; len];
            let bit = (c >> (i - 1)) & 1;
            let offset = (m + bit) as usize;
            for idx in 0..len {
                let target_k = offset + idx;
                let min_x = if target_k >= len {
                    target_k - len + 1
                } else {
                    0
                };
                let max_x = target_k.min(len - 1);
                let mut val = minf;
                for x in min_x..=max_x {
                    val = val.max(dp[x] + dp[target_k - x]);
                }
                dp_new[idx] = val;
            }
            dp = dp_new;
        }
        let check_len = (m as usize + 1).min(dp.len());
        *dp[0..check_len].iter().max().unwrap_or(&0) as u64 + reduce_count * best_v
    } else {
        println!("second");
        let z = c / best_w + 1;
        let reduce_count = if max_v <= z { z - max_v } else { 0 };
        let t = z * best_v - reduce_count * best_v;
        c -= reduce_count * best_w;
        let inf = u64::MAX / 2;
        let m = max_v;
        let k = m as usize + 1;
        let mut dp = vec![inf; k];
        dp[0] = 0;
        for i in 0..n {
            dp[v[i] as usize] = dp[v[i] as usize].min(w[i]);
        }
        let mut z = 1;
        while z < m {
            let mut dp_new = vec![inf; k];
            for i in 0..k {
                for j in 0..k - i {
                    dp_new[i + j] = dp_new[i + j].min(dp[i] + dp[j]);
                }
            }
            dp = dp_new;
            z <<= 1;
        }
        let mut padded_dp = vec![inf; m as usize];
        padded_dp.extend(dp);
        dp = padded_dp;
        let lg = u64::BITS - t.leading_zeros();
        let len = dp.len();
        for i in (1..=lg).rev() {
            let mut dp_new = vec![inf; len];
            let bit = (t >> (i - 1)) & 1;
            let offset = (m + bit) as usize;
            for idx in 0..len {
                let target_k = offset + idx;
                let min_x = if target_k >= len {
                    target_k - len + 1
                } else {
                    0
                };
                let max_x = target_k.min(len - 1);
                let mut val = inf;
                for x in min_x..=max_x {
                    val = val.min(dp[x] + dp[target_k - x]);
                }
                dp_new[idx] = val;
            }
            dp = dp_new;
        }
        let check_len = (m as usize + 1).min(dp.len());
        let i = dp[0..check_len].iter().rposition(|&c_p| c_p <= c).unwrap();
        t - m + i as u64 + reduce_count * best_v
    }
}

/// O(n + c log c)
pub fn complete_knapsack_eq<const M: u64>(w: &[usize], c: usize) -> Vec<u64> {
    (-Poly::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
        .exp(c + 1)
        .unwrap()
        .coeff
        .into_iter()
        .map(|i| i.rem_euclid(M as i64) as u64)
        .collect::<Vec<_>>()
}

/// O(n c)
pub fn multiple_knapsack(v: &[u64], w: &[u64], k: &[usize], c: u64) -> Vec<u64> {
    let n = v.len();
    let cap = c as usize;
    let mut dp = vec![0i64; cap + 1];
    for i in 0..n {
        let weight = w[i] as usize;
        let value = v[i] as i64;
        let cnt = k[i];
        if weight == 0 {
            continue;
        }
        let mut new_dp = dp.clone();
        for r in 0..weight.min(cap + 1) {
            let mut mq = MonotoneQueue::with_capacity(cnt + 1, |a, b| a > b);
            for x in 0..=(cap - r) / weight {
                let j = x * weight + r;
                mq.push_back(dp[j] - (x as i64) * value);
                if x >= cnt + 1 {
                    let old_x = x - (cnt + 1);
                    mq.pop_front(&(dp[old_x * weight + r] - (old_x as i64) * value));
                }
                if let Some(&best_g) = mq.min() {
                    new_dp[j] = best_g + (x as i64) * value;
                }
            }
        }
        dp = new_dp;
    }
    dp.into_iter().map(|v| v as u64).collect()
}

/// O(n + c log c)
pub fn multiple_knapsack_eq<const M: u64>(w: &[usize], k: &[usize], c: usize) -> Vec<u64> {
    (Poly::<M>::log_prod_1pxit(-1, k.into_iter().zip(w).map(|(&i, &j)| (i + 1) * j), c + 1)
        - Poly::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
    .exp(c + 1)
    .unwrap()
    .coeff
    .into_iter()
    .map(|i| i.rem_euclid(M as i64) as u64)
    .collect::<Vec<_>>()
}

// TODO: some of the cases here
// https://codeforces.com/blog/entry/98663

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;

    // --- Ground Truth: Naive O(N * C) Implementation ---
    fn naive_complete_knapsack_u64(v: &[u64], w: &[u64], c: u64) -> u64 {
        let cap = c as usize;
        // Check if we can even allocate this
        if cap > 100_000_000 {
            panic!("Test capacity too large for naive implementation");
        }
        let mut dp = vec![0; cap + 1];

        for i in 0..v.len() {
            let weight = w[i] as usize;
            let val = v[i];
            if weight == 0 {
                continue;
            } // Avoid infinite loops
            if weight <= cap {
                for j in weight..=cap {
                    dp[j] = dp[j].max(dp[j - weight] + val);
                }
            }
        }
        dp[cap]
    }

    // --- Basic Correctness ---

    #[test]
    fn test_simple_small_case() {
        // Item 0: w=3, v=5
        // Item 1: w=5, v=9 (Better density: 1.8 vs 1.66)
        // C = 10.
        // Option A: 2 * Item 1 = w=10, v=18.
        // Option B: 3 * Item 0 = w=9, v=15.
        // Option C: 1*Item1 + 1*Item0 = w=8, v=14.
        let v = vec![5, 9];
        let w = vec![3, 5];
        let c = 10;
        assert_eq!(complete_knapsack(&v, &w, c), 18);
    }

    #[test]
    fn test_exact_fit_vs_greedy() {
        // Greedy (density) isn't always right for small/medium C.
        // Item A: w=4, v=10 (Density 2.5)
        // Item B: w=3, v=7 (Density 2.33)
        // C = 6.
        // Greedy takes 1x A (w=4, v=10). Space left=2 (can't fill). Total = 10.
        // Optimal takes 2x B (w=6, v=14). Total = 14.
        let v = vec![10, 7];
        let w = vec![4, 3];
        let c = 6;
        assert_eq!(complete_knapsack(&v, &w, c), 14);
    }

    // --- Large Capacity (Steinitz) Tests ---

    #[test]
    fn test_huge_capacity_best_density() {
        // C = 10^12 (Too big for array DP)
        // Item A: w=10, v=100 (Density 10)
        // Item B: w=20, v=150 (Density 7.5)
        // Optimal is obviously just spamming Item A.
        let v = vec![100, 150];
        let w = vec![10, 20];
        let c = 1_000_000_000_000;

        let expected = (c / 10) * 100;
        assert_eq!(complete_knapsack(&v, &w, c), expected);
    }

    #[test]
    fn test_large_capacity_with_remainder() {
        // C = 1000.
        // Item A: w=10, v=20 (Density 2.0)
        // Item B: w=3, v=5 (Density 1.66)
        // Optimal: Fill main bulk with Item A.
        // 1000 is divisible by 10. Max = 2000.
        // Let's make C slightly messy. C = 1007.
        // Bulk: 1000 -> 100x A = 2000. Remainder 7.
        // Can fit 2x B (w=6, v=10). Total 2010.
        // Or remove one A (w=10, v=20) -> Remainder 17.
        // 17 = 5x B (w=15, v=25). Total 1980 + 25 = 2005. (Worse)
        let v = vec![20, 5];
        let w = vec![10, 3];
        let c = 1007;

        // Naive can handle 1000
        let expected = naive_complete_knapsack_u64(&v, &w, c);
        assert_eq!(complete_knapsack(&v, &w, c), expected);
    }

    // --- Small Values / Large Weights Tests ---

    // #[test]
    // fn test_high_weights_small_values() {
    //     // If your code switches to O(V^2) when V is small and W is large.
    //     // Item A: v=3, w=1_000_000
    //     // Item B: v=5, w=1_500_000
    //     // C = 3_000_000
    //     // Option 1: 3x A = w=3m, v=9
    //     // Option 2: 2x B = w=3m, v=10
    //     // Option 3: 1x A + 1x B = w=2.5m, v=8
    //     // Result: 10.
    //     let v = vec![3, 5];
    //     let w = vec![1_000_000, 1_500_000];
    //     let c = 3_000_000;
    //     assert_eq!(complete_knapsack(&v, &w, c), 10);
    // }

    // --- Fuzz Testing ---

    #[test]
    fn test_fuzz_general() {
        let mut rng = StdRng::seed_from_u64(12345);
        for _ in 0..100 {
            // Setup parameters to keep within naive DP limits
            let n = rng.gen_range(1..10);
            let c = rng.gen_range(1..2000);

            let mut v = Vec::new();
            let mut w = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range(1..100));
                w.push(rng.gen_range(1..100));
            }

            let expected = naive_complete_knapsack_u64(&v, &w, c);
            let actual = complete_knapsack(&v, &w, c);

            assert_eq!(
                actual, expected,
                "Mismatch on C={}, v={:?}, w={:?}",
                c, v, w
            );
        }
    }

    #[test]
    fn test_fuzz_steinitz_boundary() {
        // Test capacities around the transition point where algorithms might switch.
        // Assuming your switch is roughly ~2*M^2.
        let mut rng = StdRng::seed_from_u64(9999);
        for _ in 0..50 {
            let m = 20; // max weight approx
            let limit = m * m * 2;

            // Generate C around the limit
            let c = rng.gen_range((limit - 100)..(limit + 200));

            let n = 5;
            let mut v = Vec::new();
            let mut w = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range(10..100));
                w.push(rng.gen_range(1..m));
            }

            let expected = naive_complete_knapsack_u64(&v, &w, c);
            let actual = complete_knapsack(&v, &w, c);

            assert_eq!(actual, expected, "Mismatch at boundary C={}", c);
        }
    }
}
