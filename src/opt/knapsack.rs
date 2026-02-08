use rand::seq::SliceRandom;

use crate::{alg::fps::FPS, ds::scan::MonotoneQueue, opt::min_plus::max_plus_ccv};

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

// https://arxiv.org/pdf/2308.11307
/// Õ(n^3/2 w)
pub fn shuffle_zero_one_knapsack(capacity: i64, mut items: Vec<(i64, i64)>) -> i64 {
    let n = items.len();
    let w_max = items.iter().map(|i| i.0).max().unwrap_or(0);
    let sum_weight: i64 = items.iter().map(|i| i.0).sum();
    let target_weight = capacity.min(sum_weight);
    let mut rng = rand::rng();
    items.shuffle(&mut rng);
    let neg_inf = i64::MIN / 2;
    let mut prev_dp = vec![0; (capacity + 1) as usize];
    let mut curr_dp = prev_dp.clone();
    let c_delta = 4.0;
    for i in 1..=n {
        let item = &items[i - 1];
        let w_i = item.0;
        let p_i = item.1;
        let mu_i = (i as f64 / n as f64) * target_weight as f64;
        let delta_i = c_delta * (i as f64).sqrt() * w_max as f64;
        let start_j = (mu_i - delta_i).floor() as i64;
        let end_j = (mu_i + delta_i).ceil() as i64;
        for j in start_j..=end_j {
            if j < 0 || j > capacity {
                continue;
            }
            let j_idx = j as usize;
            let term1 = prev_dp[j_idx];
            let term2 = if j - w_i < 0 {
                neg_inf
            } else {
                let prev_idx = (j - w_i) as usize;
                if prev_idx >= prev_dp.len() || prev_dp[prev_idx] == neg_inf {
                    neg_inf
                } else {
                    prev_dp[prev_idx] + p_i
                }
            };
            curr_dp[j_idx] = term1.max(term2);
        }
        let copy_start = start_j.max(0) as usize;
        let copy_end = capacity.min(end_j) as usize;
        for k in copy_start..=copy_end {
            prev_dp[k] = curr_dp[k];
        }
    }
    *prev_dp.iter().max().unwrap_or(&0)
}

// https://arxiv.org/pdf/1802.06440
/// O(d c log c)
pub fn axiotis_tzamos_zero_one(v: &[u64], w: &[u64], c: u64) -> u64 {
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
            let res = max_plus_ccv(&v, &sum);
            for i in 0..n {
                dp[i * w + k] = res[i];
            }
        }
    }
    *dp.iter().max().unwrap_or(&0)
}

/// O(n + c log c)
pub fn zero_one_knapsack_eq<const M: u64>(w: &[usize], c: usize) -> Vec<u64> {
    FPS::<M>::log_prod_1pxit(1, w.into_iter().cloned(), c + 1)
        .exp(c + 1)
        .unwrap()
        .coeff
        .into_iter()
        .map(|i| i.rem_euclid(M as i64) as u64)
        .collect::<Vec<_>>()
}

// https://arxiv.org/pdf/1802.06440
/// O(min(n c, M^2 log M, V^2 log V))
pub fn axiotis_tzamos_complete(v: &[u64], w: &[u64], mut c: u64) -> u64 {
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
    (-FPS::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
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
    (FPS::<M>::log_prod_1pxit(-1, k.into_iter().zip(w).map(|(&i, &j)| (i + 1) * j), c + 1)
        - FPS::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
    .exp(c + 1)
    .unwrap()
    .coeff
    .into_iter()
    .map(|i| i.rem_euclid(M as i64) as u64)
    .collect::<Vec<_>>()
}

// TODO: some of the cases here
// https://codeforces.com/blog/entry/98663
