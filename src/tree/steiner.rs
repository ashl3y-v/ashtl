use crate::ds::bit_vec::BitVec;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::ops::Add;

/// O(n 3^k + (n + m) 2^k log n)
pub fn dreyfus_wagner<T>(adj: &[Vec<(usize, T)>], term: &[usize], inf: T) -> T
where
    T: Copy + Default + Add<Output = T> + Ord,
{
    let n = adj.len();
    let t = term.len();
    if t <= 1 {
        return T::default();
    }
    let mut dp = vec![vec![inf; n]; 1 << t];
    for (i, &terminal) in term.iter().enumerate() {
        dp[1 << i][terminal] = T::default();
    }
    for mask in 1..(1 << t) {
        for i in 0..n {
            let mut sub_mask = (mask - 1) & mask;
            while sub_mask > 0 {
                let cost = dp[sub_mask][i] + dp[mask ^ sub_mask][i];
                if cost < dp[mask][i] {
                    dp[mask][i] = cost;
                }
                sub_mask = (sub_mask - 1) & mask;
            }
        }
        if mask == (1 << t) - 1 {
            continue;
        }
        let mut pq = BinaryHeap::new();
        for i in 0..n {
            if dp[mask][i] < inf {
                pq.push(Reverse((dp[mask][i], i)));
            }
        }
        while let Some(Reverse((d, u))) = pq.pop() {
            if d > dp[mask][u] {
                continue;
            }
            for &(v, weight) in &adj[u] {
                let new_dist = d + weight;
                if new_dist < dp[mask][v] {
                    dp[mask][v] = new_dist;
                    pq.push(Reverse((new_dist, v)));
                }
            }
        }
    }
    dp[(1 << t) - 1][term[0]]
}

/// O(2^k * m * n^2) time, O(n^2) space
pub fn nederlof<const M: u64>(
    n: usize,
    g: &[usize],
    d: &[usize],
    terminals: &[usize],
) -> Option<usize> {
    if terminals.is_empty() {
        return Some(0);
    } else if terminals.len() == 1 {
        return Some(1);
    }
    let k = terminals.len();
    fn willow<const M: u64>(
        n: usize,
        g: &[usize],
        d: &[usize],
        avoid: &BitVec,
        total_willows: &mut [u64],
        add: bool,
    ) {
        let mut dp = vec![0; (n + 1) * n];
        for u in 0..n {
            if !avoid.get(u) {
                dp[n + u] = 1;
            }
        }
        for s in 2..=n {
            for u in 0..n {
                if avoid.get(u) {
                    continue;
                }
                for &v in &g[d[u]..d[u + 1]] {
                    if avoid.get(v) {
                        continue;
                    }
                    let mut sum = 0;
                    for i in 1..s {
                        let count_u = dp[i * n + u];
                        let count_v = dp[(s - i) * n + v];
                        sum = (sum + count_u * count_v) % M;
                    }
                    dp[s * n + u] = (dp[s * n + u] + sum) % M;
                }
            }
        }
        for s in 1..=n {
            let mut sum = 0;
            for u in 0..n {
                sum = (sum + dp[s * n + u]) % M;
            }
            if add {
                total_willows[s] = (total_willows[s] + sum) % M;
            } else {
                total_willows[s] = (total_willows[s] + M - sum) % M;
            }
        }
    }
    let mut total_willows = vec![0; n + 1];
    let n_words = (k + 63) / 64;
    let mut counter = vec![0u64; n_words];
    let mut avoid = BitVec::new(n, false);
    let mut avoid_count = 0;
    willow::<M>(n, g, d, &avoid, &mut total_willows, true);
    loop {
        let flip_bit = {
            let mut bit = n_words * 64;
            for (i, word) in counter.iter_mut().enumerate() {
                let old = *word;
                *word = word.wrapping_add(1);
                if old != u64::MAX {
                    bit = i * 64 + word.trailing_zeros() as usize;
                    break;
                }
            }
            bit
        };
        if flip_bit >= k {
            break;
        }
        let terminal_idx = terminals[flip_bit];
        let was_avoiding = avoid.get(terminal_idx);
        if was_avoiding {
            avoid.set(terminal_idx, false);
            avoid_count -= 1;
        } else {
            avoid.set(terminal_idx, true);
            avoid_count += 1;
        }
        let add_to_total = avoid_count % 2 == 0;
        willow::<M>(n, g, d, &avoid, &mut total_willows, add_to_total);
    }
    for l in k..=n {
        if total_willows[l] > 0 {
            return Some(l);
        }
    }
    None
}
