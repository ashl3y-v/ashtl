pub fn hilbert(mut x: u64, mut y: u64, k: u64) -> u64 {
    let mut d = 0;
    let mut s = k >> 1;
    while s != 0 {
        let (rx, ry) = ((x & s != 0) as u64, (y & s != 0) as u64);
        d <<= 2;
        d |= (3 * rx) ^ ry;
        let mut mask = (ry ^ 1).wrapping_neg();
        x ^= y & mask;
        y ^= x & mask;
        x ^= y & mask;
        mask &= rx.wrapping_neg();
        x ^= mask;
        y ^= mask;
        s >>= 1;
    }
    d
}
