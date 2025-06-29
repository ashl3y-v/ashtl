#[inline]
pub fn m_reduce<const N: u64>(ab: u128) -> u64 {
    const fn n_inv(n: u64) -> u64 {
        let mut inv: u64 = 1;
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
        inv = inv.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(inv)));
        inv.wrapping_neg()
    }
    let n_inv = n_inv(N);

    (ab + ((ab as u64).wrapping_mul(n_inv) as u128).wrapping_mul(N as u128) >> 64) as u64
}

#[inline]
pub fn m_transform<const N: u64>(x: u64) -> u64 {
    const fn r2(n: u64) -> u64 {
        ((1u128 << 64) % (n as u128)) as u64
    }
    let r2 = r2(N);

    m_reduce::<N>(x as u128 * r2 as u128)
}

#[inline]
pub fn m_mul<const N: u64>(a: u64, b: u64) -> u64 {
    m_reduce::<N>(a as u128 * b as u128)
}

#[inline]
pub fn m_sub<const N: u64>(a: u64, b: u64) -> u64 {
    if a < b { a + N - b } else { a - b }
}

#[inline]
pub fn m_add<const N: u64>(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= N { s - N } else { s }
}
