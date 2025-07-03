use crate::alg::gcd::euclidean;

pub fn crt(mut a: i128, mut m: i128, mut b: i128, mut n: i128) -> i128 {
    if n > m {
        (a, b, m, n) = (b, a, n, m);
    }
    let (g, x, _) = euclidean(m, n);
    let diff = b - a;
    debug_assert!(
        diff % g == 0,
        "CRT has no solution for given (a,m) and (b,n)"
    );
    let k = diff / g;
    let n_g = n / g;
    let mut u = x * k % n_g;
    if u < 0 {
        u += n_g;
    }
    let raw = a + m * u;
    let lcm = m / g * n;
    let mut ret = raw % lcm;
    if ret < 0 {
        ret += lcm;
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_euclidean_basic() {
        let (g, s, t) = euclidean(30, 12);
        assert_eq!(g, 6);
        assert_eq!(s * 30 + t * 12, g);
    }

    #[test]
    fn test_euclidean_negative() {
        let (g, s, t) = euclidean(-25, 10);
        assert_eq!(g, 5);
        assert_eq!(s * -25 + t * 10, g);
    }

    #[test]
    fn test_crt_coprime() {
        let x = crt(2, 5, 3, 7);
        assert_eq!(x, 17);
    }

    #[test]
    fn test_crt_non_coprime() {
        let x = crt(1, 6, 5, 8);
        assert_eq!(x, 13);
    }

    #[test]
    #[should_panic(expected = "CRT has no solution")]
    fn test_crt_no_solution() {
        let _ = crt(1, 6, 2, 8);
    }

    #[test]
    fn test_crt_swapped_order() {
        let x1 = crt(2, 5, 3, 7);
        let x2 = crt(3, 7, 2, 5);
        assert_eq!(x1, x2);
    }
}
