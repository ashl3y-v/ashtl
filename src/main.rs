use ashtl::{
    alg::{
        lattice, mult, ntt,
        ops::{self, inverse_euclidean, mod_fact, mod_pow},
        poly::{Poly, Poly2},
        prime, primitive, special, young,
    },
    ds::{knapsack, set},
    grph::color,
    lin::mat::Mat,
};
use rand::{Rng, seq::SliceRandom};
use std::{collections::HashSet, time::Instant};

// const M: u64 = (119 << 23) + 1;
// const M: u64 = (7 << 26) + 1;
const M: u64 = (15 << 27) + 1;
// const M: u64 = ((1_u128 << 63) - 25) as u64;

fn main() -> std::io::Result<()> {
    let mut rng = rand::rng();
    // println!("{}", ntt::find_ntt_prime(1 << 22, M >> 2));
    // put everyone's phones in my thing
    // get rid of stuff taking mut self and n
    // make stuff use truncate_deg instead of doing stuff up to deg
    // ntt faster
    // println!("{}", find_ntt_prime(1 << 27, M << 2));

    let inv = |a: i64| inverse_euclidean::<M, _>(a);
    let inv_u = |a: i64| inverse_euclidean::<M, _>(a).rem_euclid(M as i64) as u64;

    // schedule:
    // bivariate extensions of fundamental operations https://maspypy.github.io/library/poly/2d/fps_inv_2d.hpp
    // https://robert1003.github.io/2020/01/31/cdq-divide-and-conquer.html
    // half-gcd
    // hungarian
    // dominator tree
    // mcmf
    // transposed bostan mori
    let n = 1 << 20;
    let m = 1 << 5;
    let i = 1 << 23;
    let k = 3;
    let q = 2;

    let mut coeff = Vec::with_capacity(n);
    for _ in 0..n {
        coeff.push(rng.random_range(M >> 4..M) as i64);
    }
    let mut a = Poly::<M>::new(coeff);
    let mut coeff = Vec::with_capacity(m);
    for _ in 0..m {
        coeff.push(rng.random_range(M >> 4..M) as i64);
    }

    let primes = mult::sieve_primes(n).0;

    Ok(())
}
