use super::{
    ops::{mod_pow, mod_pow_non_const},
    prime::factor,
};
use rand::Rng;

pub fn primitive_root(m: u64, rng: &mut impl Rng) -> u64 {
    if m <= 1 {
        return 0;
    }
    if m == 2 {
        return 1;
    }
    if m == 3 {
        return 2;
    }
    let f = factor(m as usize - 1);
    let mut g;
    'a: loop {
        g = rng.random_range(2..m);
        for &q in &f {
            if mod_pow_non_const(g, (m - 1) / q as u64, m) == 1 {
                continue 'a;
            }
        }
        break g;
    }
}

pub const fn find_primitive_root<const M: u64>() -> u64 {
    if M <= 1 {
        return 0;
    }
    if M == 2 {
        return 1;
    }
    if M == 3 {
        return 2;
    }
    let phi = M - 1;
    let mut factors = [0u64; 16];
    let mut factor_count = 0;
    let mut remaining = phi;
    if remaining % 2 == 0 {
        factors[factor_count] = 2;
        factor_count += 1;
        while remaining % 2 == 0 {
            remaining /= 2;
        }
    }
    let mut factor = 3;
    while factor * factor <= remaining && factor_count < 16 {
        if remaining % factor == 0 {
            factors[factor_count] = factor;
            factor_count += 1;
            while remaining % factor == 0 {
                remaining /= factor;
            }
        }
        factor += 2;
    }
    if remaining > 1 && factor_count < 16 {
        factors[factor_count] = remaining;
        factor_count += 1;
    }
    let mut candidate = 2;
    while candidate < M {
        let mut is_primitive = true;
        let mut i = 0;
        while i < factor_count {
            let exp = phi / factors[i];
            if mod_pow::<M>(candidate, exp) == 1 {
                is_primitive = false;
                break;
            }
            i += 1;
        }
        if is_primitive {
            return candidate;
        }
        candidate += 1;
    }
    0
}

#[inline]
pub const fn find_ntt_root<const M: u64>() -> u64 {
    let root = find_primitive_root::<M>();
    mod_pow::<M>(root, M >> (M - 1).trailing_zeros())
}
