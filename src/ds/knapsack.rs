use crate::{alg::poly::Poly, ds::scan::MonotoneQueue};

/// O(n max w_i)
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

/// O(n c)
pub fn zero_one_knapsack(v: &[u64], w: &[u64], c: u64) -> Vec<u64> {
    let n = v.len();
    let mut f = vec![0; c as usize + 1];
    for i in 0..n {
        for j in (w[i] as usize..=c as usize).rev() {
            f[j] = f[j].max(f[j - w[i] as usize] + v[i]);
        }
    }
    f
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

/// O(n c)
pub fn complete_knapsack(v: &[u64], w: &[u64], c: u64) -> Vec<u64> {
    let n = v.len();
    let mut f = vec![0; c as usize + 1];
    for i in 0..n {
        for j in w[i] as usize..=c as usize {
            f[j] = f[j].max(f[j - w[i] as usize] + v[i]);
        }
    }
    f
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

/// O(n)
pub fn min_plus_cvx_cvx(a: &[i64], b: &[i64]) -> Vec<i64> {
    if a.is_empty() || b.is_empty() {
        return if a.is_empty() { b.to_vec() } else { a.to_vec() };
    }
    let (n0, n1) = (a.len(), b.len());
    let mut c = vec![0; n0 + n1 - 1];
    let (mut i0, mut i1) = (0, 0);
    c[0] = a[i0] + b[i1];
    for i in 1..n0 + n1 - 1 {
        if i1 == n1 - 1 || (i0 != n0 - 1 && a[i0 + 1] + b[i1] < a[i0] + b[i1 + 1]) {
            i0 += 1;
        } else {
            i1 += 1;
        }
        c[i] = a[i0] + b[i1];
    }
    c
}

// TODO: min plus only one convex convolution (also add to poly)
// https://judge.yosupo.jp/submission/296643
// https://codeforces.com/blog/entry/98663
pub fn min_plus_cvx(a: &[i64], b: &[i64]) -> Vec<i64> {
    unimplemented!()
}

// TODO: other knapsack optimizations
// https://codeforces.com/blog/entry/98663

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_test_case() -> (Vec<u64>, Vec<u64>, u64) {
        let values = vec![60, 100, 120];
        let weights = vec![10, 20, 30];
        let capacity = 50;
        (values, weights, capacity)
    }

    fn medium_test_case() -> (Vec<u64>, Vec<u64>, u64) {
        let values = vec![10, 40, 30, 50];
        let weights = vec![5, 4, 6, 3];
        let capacity = 10;
        (values, weights, capacity)
    }

    fn large_test_case() -> (Vec<u64>, Vec<u64>, u64) {
        let values: Vec<u64> = (1..=100).map(|i| i * 2).collect();
        let weights: Vec<u64> = (1..=100).collect();
        let capacity = 500;
        (values, weights, capacity)
    }

    fn empty_items() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![], vec![], 10)
    }

    fn zero_capacity() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![10, 20], vec![5, 10], 0)
    }

    fn single_item() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![50], vec![10], 20)
    }

    fn all_items_too_heavy() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![100, 200, 300], vec![20, 30, 40], 10)
    }

    fn zero_weight_items() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![10, 20, 30], vec![0, 5, 0], 10)
    }

    fn identical_items() -> (Vec<u64>, Vec<u64>, u64) {
        (vec![10, 10, 10, 10], vec![5, 5, 5, 5], 15)
    }

    fn verify_dp_properties(dp: &[u64], capacity: u64) {
        assert_eq!(dp.len(), capacity as usize + 1);
        for i in 1..dp.len() {
            assert!(
                dp[i] >= dp[i - 1],
                "DP array should be non-decreasing: dp[{}]={} < dp[{}]={}",
                i,
                dp[i],
                i - 1,
                dp[i - 1]
            );
        }
    }

    fn brute_force_01_knapsack(values: &[u64], weights: &[u64], capacity: u64) -> u64 {
        let n = values.len();
        let mut max_value = 0;
        for i in 0..(1 << n) {
            let mut total_weight = 0;
            let mut total_value = 0;
            for j in 0..n {
                if (i >> j) & 1 == 1 {
                    total_weight += weights[j];
                    total_value += values[j];
                }
            }
            if total_weight <= capacity {
                max_value = max_value.max(total_value);
            }
        }
        max_value
    }

    #[test]
    fn test_zero_one_knapsack_basic() {
        let (values, weights, capacity) = simple_test_case();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 220);
    }

    #[test]
    fn test_zero_one_knapsack_against_brute_force() {
        let test_cases = vec![
            simple_test_case(),
            medium_test_case(),
            (vec![1, 4, 5, 7], vec![1, 3, 4, 5], 7),
        ];
        for (values, weights, capacity) in test_cases {
            if values.len() <= 20 {
                let dp = zero_one_knapsack(&values, &weights, capacity);
                let brute_force_result = brute_force_01_knapsack(&values, &weights, capacity);
                assert_eq!(
                    dp[capacity as usize], brute_force_result,
                    "Mismatch for case: values={:?}, weights={:?}, capacity={}",
                    values, weights, capacity
                );
            }
        }
    }

    #[test]
    fn test_zero_one_knapsack_edge_cases() {
        let (values, weights, capacity) = empty_items();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
        let (values, weights, capacity) = zero_capacity();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
        let (values, weights, capacity) = single_item();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 50);
        let (values, weights, capacity) = all_items_too_heavy();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
    }

    #[test]
    fn test_zero_one_knapsack_zero_weights() {
        let (values, weights, capacity) = zero_weight_items();
        let dp = zero_one_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 60);
    }

    #[test]
    fn test_complete_knapsack_basic() {
        let (values, weights, capacity) = simple_test_case();
        let dp = complete_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 300);
    }

    #[test]
    fn test_complete_knapsack_vs_zero_one() {
        let test_cases = vec![simple_test_case(), medium_test_case()];
        for (values, weights, capacity) in test_cases {
            let dp_01 = zero_one_knapsack(&values, &weights, capacity);
            let dp_complete = complete_knapsack(&values, &weights, capacity);
            assert!(
                dp_complete[capacity as usize] >= dp_01[capacity as usize],
                "Complete knapsack result {} should be >= 0-1 knapsack result {}",
                dp_complete[capacity as usize],
                dp_01[capacity as usize]
            );
        }
    }

    #[test]
    fn test_complete_knapsack_edge_cases() {
        let (values, weights, capacity) = empty_items();
        let dp = complete_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
        let (values, weights, capacity) = zero_capacity();
        let dp = complete_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
        let dp = complete_knapsack(&[10], &[3], 10);
        verify_dp_properties(&dp, 10);
        assert_eq!(dp[10], 30);
        let (values, weights, capacity) = all_items_too_heavy();
        let dp = complete_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 0);
    }

    #[test]
    fn test_complete_knapsack_identical_items() {
        let (values, weights, capacity) = identical_items();
        let dp = complete_knapsack(&values, &weights, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 30);
    }

    #[test]
    fn test_multiple_knapsack_basic() {
        let values = vec![60, 100, 120];
        let weights = vec![10, 20, 30];
        let quantities = vec![1, 2, 1];
        let capacity = 50;
        let dp = multiple_knapsack(&values, &weights, &quantities, capacity);
        verify_dp_properties(&dp, capacity);
        assert_eq!(dp[capacity as usize], 260);
    }

    #[test]
    fn test_multiple_knapsack_vs_others() {
        let values = vec![10, 20, 30];
        let weights = vec![5, 10, 15];
        let capacity = 20;
        let dp_01 = zero_one_knapsack(&values, &weights, capacity);
        let quantities_one = vec![1, 1, 1];
        let dp_mult_one = multiple_knapsack(&values, &weights, &quantities_one, capacity);
        assert_eq!(dp_01[capacity as usize], dp_mult_one[capacity as usize]);
        let dp_complete = complete_knapsack(&values, &weights, capacity);
        let quantities_large = vec![100, 100, 100];
        let dp_mult_large = multiple_knapsack(&values, &weights, &quantities_large, capacity);
        assert_eq!(
            dp_complete[capacity as usize],
            dp_mult_large[capacity as usize]
        );
    }

    #[test]
    fn test_multiple_knapsack_edge_cases() {
        let dp = multiple_knapsack(&[], &[], &[], 10);
        verify_dp_properties(&dp, 10);
        assert_eq!(dp[10], 0);
        let dp = multiple_knapsack(&[10], &[5], &[2], 0);
        verify_dp_properties(&dp, 0);
        assert_eq!(dp[0], 0);
        let dp = multiple_knapsack(&[10, 20], &[5, 10], &[0, 0], 20);
        verify_dp_properties(&dp, 20);
        assert_eq!(dp[20], 0);
        let dp = multiple_knapsack(&[10, 20, 30], &[5, 10, 15], &[0, 2, 1], 25);
        verify_dp_properties(&dp, 25);
        assert_eq!(dp[25], 50);
    }

    #[test]
    fn test_multiple_knapsack_zero_weights() {
        let dp = multiple_knapsack(&[10, 20], &[0, 5], &[5, 2], 10);
        verify_dp_properties(&dp, 10);
        assert_eq!(dp[10], 40);
    }

    #[test]
    fn test_large_inputs_performance() {
        let (values, weights, capacity) = large_test_case();
        let start = std::time::Instant::now();
        let dp_01 = zero_one_knapsack(&values, &weights, capacity);
        let time_01 = start.elapsed();
        let start = std::time::Instant::now();
        let dp_complete = complete_knapsack(&values, &weights, capacity);
        let time_complete = start.elapsed();
        let quantities: Vec<usize> = vec![1; values.len()];
        let start = std::time::Instant::now();
        let dp_multiple = multiple_knapsack(&values, &weights, &quantities, capacity);
        let time_multiple = start.elapsed();
        verify_dp_properties(&dp_01, capacity);
        verify_dp_properties(&dp_complete, capacity);
        verify_dp_properties(&dp_multiple, capacity);
        assert!(dp_complete[capacity as usize] >= dp_01[capacity as usize]);
        assert_eq!(dp_01[capacity as usize], dp_multiple[capacity as usize]);
        assert!(
            time_01.as_millis() < 1000,
            "0-1 knapsack took too long: {:?}",
            time_01
        );
        assert!(
            time_complete.as_millis() < 1000,
            "Complete knapsack took too long: {:?}",
            time_complete
        );
        assert!(
            time_multiple.as_millis() < 5000,
            "Multiple knapsack took too long: {:?}",
            time_multiple
        );
    }

    #[test]
    fn test_input_validation_assumptions() {
        let dp = zero_one_knapsack(&[100], &[50], 100);
        assert_eq!(dp[100], 100);
        let dp = complete_knapsack(&[100], &[50], 100);
        assert_eq!(dp[100], 200);
        let dp = multiple_knapsack(&[100], &[50], &[3], 100);
        assert_eq!(dp[100], 200);
    }

    #[test]
    fn test_capacity_boundaries() {
        let values = vec![10, 20, 30];
        let weights = vec![5, 10, 15];
        let dp = zero_one_knapsack(&values, &weights, 0);
        assert_eq!(dp[0], 0);
        let dp = zero_one_knapsack(&values, &weights, 1);
        assert_eq!(dp[1], 0);
        let dp = zero_one_knapsack(&values, &weights, 5);
        assert_eq!(dp[5], 10);
        let dp = zero_one_knapsack(&values, &weights, 15);
        assert_eq!(dp[15], 30);
        let dp = zero_one_knapsack(&values, &weights, 30);
        assert_eq!(dp[30], 60);
    }

    #[test]
    fn test_value_weight_ratios() {
        let values = vec![1, 4, 7, 9];
        let weights = vec![5, 5, 4, 5];
        let capacity = 10;
        let dp_01 = zero_one_knapsack(&values, &weights, capacity);
        assert_eq!(dp_01[capacity as usize], 16);
        let dp_complete = complete_knapsack(&values, &weights, capacity);
        assert_eq!(dp_complete[capacity as usize], 18);
    }

    #[test]
    fn test_pathological_cases() {
        let values = vec![10, 10, 10, 10];
        let weights = vec![1, 2, 3, 4];
        let capacity = 10;
        let dp_01 = zero_one_knapsack(&values, &weights, capacity);
        let dp_complete = complete_knapsack(&values, &weights, capacity);
        assert!(dp_complete[capacity as usize] >= dp_01[capacity as usize]);
        assert_eq!(dp_complete[capacity as usize], 100); // 10 copies of item 0
    }

    #[test]
    fn test_subset_sum_basic() {
        // Basic case: weights [3, 5, 7, 9], target 12
        let weights = vec![3, 5, 7, 9];
        let target = 12;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 12); // Can achieve exactly 12 with 3+9

        // Another case: weights [4, 6, 8], target 10
        let weights = vec![4, 6, 8];
        let target = 10;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 10); // Can achieve exactly 10 with 4+6

        // Case where exact target isn't possible
        let weights = vec![5, 7, 11];
        let target = 10;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 7); // Best we can do is 7

        let weights = vec![1, 2, 3];
        let target = 4;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 4); // Can achieve exactly 4 with 1+3
    }

    #[test]
    fn test_subset_sum_edge_cases() {
        // Empty weights
        assert_eq!(subset_sum(&[], 10), 0);

        // Zero target
        assert_eq!(subset_sum(&[1, 2, 3], 0), 0);

        // Single weight that fits
        assert_eq!(subset_sum(&[5], 10), 5);

        // Single weight that doesn't fit
        assert_eq!(subset_sum(&[15], 10), 0);

        // All weights too large
        assert_eq!(subset_sum(&[20, 25, 30], 10), 0);

        // Target smaller than smallest weight
        assert_eq!(subset_sum(&[5, 7, 9], 3), 0);
    }

    #[test]
    fn test_subset_sum_greedy_phase() {
        // Case where greedy phase gets everything
        let weights = vec![1, 2, 3, 4];
        let target = 10;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 10); // 1+2+3+4 = 10

        // Case where greedy phase gets partial solution
        let weights = vec![1, 2, 3, 10];
        let target = 8;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 6); // 1+2+3 = 6, then 10 doesn't fit
    }

    #[test]
    fn test_subset_sum_optimization_needed() {
        // Case where greedy isn't optimal - need to backtrack
        let weights = vec![1, 3, 4, 5];
        let target = 7;
        let result = subset_sum(&weights, target);
        // Greedy would take 1+3=4, then 4 gives 8 > 7, so stops at 4
        // But optimal is 3+4=7
        assert_eq!(result, 7);

        // Another optimization case
        let weights = vec![2, 3, 6, 7];
        let target = 9;
        let result = subset_sum(&weights, target);
        // Should find 2+7=9 or 3+6=9
        assert_eq!(result, 9);
    }

    #[test]
    fn test_subset_sum_large_weights() {
        // Test with larger weights to stress the O(n * max(w_i)) complexity
        let weights = vec![10, 20, 30, 40, 50];
        let target = 80;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 80); // 10+20+50 = 80 or 30+50 = 80

        // Test where we can't reach target
        let weights = vec![15, 25, 35];
        let target = 50;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 50); // 15+35 = 40
    }

    #[test]
    fn test_subset_sum_all_same_weight() {
        // All weights are the same
        let weights = vec![5, 5, 5, 5];
        let target = 12;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 10); // Can take 2 items: 5+5=10 <= 12

        // Exact multiple
        let weights = vec![3, 3, 3, 3];
        let target = 9;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 9); // Can take 3 items: 3+3+3=9
    }

    #[test]
    fn test_subset_sum_single_large_item() {
        // One large item among small ones
        let weights = vec![1, 2, 3, 100];
        let target = 50;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 6); // 1+2+3=6, can't include 100

        // Large item that fits
        let weights = vec![1, 2, 3, 50];
        let target = 60;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 56); // 1+2+3+50=56
    }

    #[test]
    fn test_subset_sum_performance() {
        // Test with moderately large input to ensure reasonable performance
        let weights: Vec<u64> = (1..=50).collect();
        let target = 500;

        let start = std::time::Instant::now();
        let result = subset_sum(&weights, target);
        let elapsed = start.elapsed();

        // Should complete quickly and give a reasonable result
        assert!(
            elapsed.as_millis() < 100,
            "Algorithm took too long: {:?}",
            elapsed
        );
        assert!(result > 0 && result <= target);

        // Verify it's close to optimal (sum of 1..50 = 1275, so we should get close to 500)
        assert!(result >= 400, "Result {} seems too small", result);
    }

    #[test]
    fn test_subset_sum_boundary_values() {
        // Test with boundary values
        let weights = vec![1];
        let target = 1;
        assert_eq!(subset_sum(&weights, target), 1);

        // Large single weight
        let weights = vec![1000];
        let target = 999;
        assert_eq!(subset_sum(&weights, target), 0);

        let weights = vec![1000];
        let target = 1000;
        assert_eq!(subset_sum(&weights, target), 1000);
    }

    #[test]
    fn test_subset_sum_ordering_independence() {
        // Result should be independent of input ordering
        let weights1 = vec![3, 7, 2, 8, 1];
        let weights2 = vec![1, 2, 3, 7, 8];
        let weights3 = vec![8, 7, 3, 2, 1];
        let target = 10;

        let result1 = subset_sum(&weights1, target);
        let result2 = subset_sum(&weights2, target);
        let result3 = subset_sum(&weights3, target);

        assert_eq!(result1, result2);
        assert_eq!(result2, result3);
        assert_eq!(result1, 10); // Should be able to achieve exactly 10
    }

    #[test]
    fn test_subset_sum_impossible() {
        // Test case: weights = [5, 10], target = 3
        let weights = vec![5, 10];
        let target = 3;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 0); // Cannot achieve any positive sum <= 3
    }

    #[test]
    fn test_subset_sum_exact_fit() {
        // Test case: weights = [2, 3, 5], target = 10
        let weights = vec![2, 3, 5];
        let target = 10;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 10); // Can achieve exactly 10 with 2+3+5
    }

    #[test]
    fn test_subset_sum_single_weight() {
        // Test case: weights = [7], target = 10
        let weights = vec![7];
        let target = 10;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 7); // Can only achieve 7
    }

    #[test]
    fn test_subset_sum_empty() {
        // Test case: empty weights
        let weights = vec![];
        let target = 5;
        let result = subset_sum(&weights, target);
        assert_eq!(result, 0); // No weights means sum is 0
    }
}
