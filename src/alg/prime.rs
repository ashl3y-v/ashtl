use super::{gcd::gcd, ops::mod_pow_non_const};
use crate::ds::sort::{counting_sort, counting_sort_dedup};

/// O(log^3 n)
/// Works up to 7 * 10^18
pub fn miller_rabin(n: u64) -> bool {
    if n < 2 || n % 6 % 4 != 1 {
        return (n | 1) == 3;
    }
    let witnesses = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
    let s = (n - 1).trailing_zeros() as u64;
    let d = n >> s;
    for a in witnesses {
        let mut p = mod_pow_non_const(a % n, d, n);
        let mut i = s;
        while p != 1 && p != n - 1 && a % n != 0 && i > 0 {
            p = p * p % n;
            i -= 1;
        }
        if p != n - 1 && i != s {
            return false;
        }
    }
    true
}

/// O(n^1/4) expected
fn pollard(n: usize) -> usize {
    let mut x = 0usize;
    let mut y = 0usize;
    let mut t = 30usize;
    let mut prd = 2usize;
    let mut i = 1usize;
    loop {
        if t % 40 != 0 || gcd(prd, n) == 1 {
            if x == y {
                i += 1;
                x = i;
                y = (x * x % n + i) % n;
            }
            let diff = if x > y { x - y } else { y - x };
            let q = prd * diff % n;
            if q != 0 {
                prd = q;
            }
            x = (x * x % n + i) % n;
            y = (((y * y % n + i) % n) * ((y * y % n + i) % n) % n + i) % n;
            t += 1;
        } else {
            break;
        }
    }
    gcd(prd, n)
}

/// O(n^1/4 log^2 n)
pub fn factor(n: usize) -> Vec<usize> {
    if n == 1 {
        return Vec::new();
    }
    if miller_rabin(n as u64) {
        return vec![n];
    }
    let x = pollard(n);
    let mut left = factor(x);
    let right = factor(n / x);
    left.extend(right);
    left
}

/// O(n^1/4 log^2 n)
pub fn factor_mult(n: usize) -> Vec<(usize, u32)> {
    let mut fs = factor(n);
    counting_sort(&mut fs, n + 1);
    let mut f = vec![(fs[0], 1)];
    let mut f_len = 1;
    let mut cp = fs[0];
    for i in 1..fs.len() {
        if fs[i] == cp {
            f[f_len - 1].1 += 1;
        } else {
            cp = fs[i];
            f.push((fs[i], 1));
            f_len += 1;
        }
    }
    f
}

/// O(n^1/4 log^2 n)
pub fn factor_dedup(n: usize) -> Vec<usize> {
    let mut fs = factor(n);
    counting_sort_dedup(&mut fs, n + 1);
    fs
}

/// O(n^1/4 log^2 n)
pub fn divisors(n: usize) -> (Vec<usize>, Vec<(usize, u32)>) {
    if n == 0 {
        return (Vec::new(), Vec::new());
    } else if n == 1 {
        return (vec![1], vec![(1, 1)]);
    }
    let prime_factors = factor_mult(n);
    let mut result = vec![1];
    for &(prime, power) in &prime_factors {
        let current_len = result.len();
        let mut prime_power = prime;
        for _ in 1..=power {
            for i in 0..current_len {
                result.push(result[i] * prime_power);
            }
            prime_power *= prime;
        }
    }
    result.sort_unstable();
    (result, prime_factors)
}

// TODO: fast prime counting
// https://codeforces.com/blog/entry/91632
// https://usaco.guide/adv/multiplicative?lang=cpp
pub fn pi(n: usize) -> usize {
    1
}

// TODO: divisor lattice and multiple lattice as graphs

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small_primes() {
        let small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
        for &p in &small_primes {
            assert!(miller_rabin(p), "{} should be prime", p);
        }
    }

    #[test]
    fn test_small_composites() {
        let small_composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25];
        for &c in &small_composites {
            assert!(!miller_rabin(c), "{} should be composite", c);
        }
    }

    #[test]
    fn test_edge_cases() {
        assert!(!miller_rabin(0));
        assert!(!miller_rabin(1));
        assert!(miller_rabin(2));
        assert!(miller_rabin(3));
    }

    #[test]
    fn test_large_primes() {
        // Some known large primes
        assert!(miller_rabin(982451653));
        assert!(miller_rabin(1000000007));
        assert!(miller_rabin(1000000009));
    }

    #[test]
    fn test_large_composites() {
        // Some large composite numbers
        assert!(!miller_rabin(1000000008));
        assert!(!miller_rabin(1000000010));
        assert!(!miller_rabin(982451654));
    }
}
