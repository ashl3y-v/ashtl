/// fibonacci(185) largest which doesn't overflow
pub fn fibonacci(n: u64) -> u128 {
    let mut f0: u128 = 0;
    let mut f1: u128 = 1;
    let mut mask = 1u64 << (63 - n.leading_zeros());
    while mask != 0 {
        let t = f1 << 1;
        let c = f0 * (t - f0);
        let d = f0 * f0 + f1 * f1;
        f0 = c;
        f1 = d;
        if (n & mask) != 0 {
            let e = f0 + f1;
            f0 = f1;
            f1 = e;
        }
        mask >>= 1;
    }
    f0
}

pub fn fibonacci_mod<const M: u64>(n: u64) -> u128 {
    let mut f0: i128 = 0;
    let mut f1: i128 = 1;
    let mut mask = 1u64 << (63 - n.leading_zeros());
    while mask != 0 {
        let t = f1 << 1;
        let c = f0 * (t - f0);
        let d = f0 * f0 + f1 * f1;
        f0 = c;
        f1 = d;
        if (n & mask) != 0 {
            let e = f0 + f1;
            f0 = f1;
            f1 = e;
        }
        f0 %= M as i128;
        f1 %= M as i128;
        mask >>= 1;
    }
    f0.rem_euclid(M as i128) as u128
}
