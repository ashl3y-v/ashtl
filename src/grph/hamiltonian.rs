use crate::ds::bit_vec::BitVec;

/// O(2^n n (n + m)) time, O(n) space
pub fn count_hamiltonian_paths_from<const M: u64>(
    n: usize,
    g: &[usize],
    d: &[usize],
    start: usize,
) -> u64 {
    fn compute_a_from<const M: u64>(
        n: usize,
        g: &[usize],
        d: &[usize],
        avoid: &BitVec,
        start: usize,
    ) -> u64 {
        if avoid[start] {
            return 0;
        }
        let mut dp = vec![0; n];
        dp[start] = 1;
        for _ in 1..n {
            let mut dp_next = vec![0; n];
            for v in 0..n {
                if dp[v] == 0 {
                    continue;
                }
                for &t in &g[d[v]..d[v + 1]] {
                    if !avoid[t] {
                        dp_next[t] = (dp_next[t] + dp[v]) % M;
                    }
                }
            }
            dp = dp_next;
        }
        dp.iter().fold(0, |acc, &x| (acc + x) % M)
    }
    if n == 0 {
        return 1;
    } else if n == 1 {
        return 1;
    }
    let n_words = (n + 63) / 64;
    let mut counter = vec![0u64; n_words];
    let mut avoid = BitVec::new(n, false);
    let mut avoid_size = 0;
    let mut res = compute_a_from::<M>(n, g, d, &avoid, start);
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
        if flip_bit >= n {
            break;
        }
        if avoid[flip_bit] {
            avoid.set(flip_bit, false);
            avoid_size -= 1;
        } else {
            avoid.set(flip_bit, true);
            avoid_size += 1;
        }
        let a_x = compute_a_from::<M>(n, g, d, &avoid, start);
        if avoid_size % 2 == 0 {
            res = (res + a_x) % M;
        } else {
            res = (res + M - a_x) % M;
        }
    }
    res
}

/// O(2^n n^2 (n + m)) time, O(n) space
pub fn has_hamiltonian_path<const M: u64>(n: usize, g: &[usize], d: &[usize]) -> bool {
    for start in 0..n {
        if count_hamiltonian_paths_from::<M>(n, g, d, start) != 0 {
            return true;
        }
    }
    false
}

// TODO: hamiltonian path heuristic
// https://codeforces.com/blog/entry/90513

// TODO: minimum hamiltonian cycle
// https://maspypy.github.io/library/graph/minimum_hamiltonian_cycle.hpp
