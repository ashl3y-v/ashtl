use super::ops::mod_pow_non_const;

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
