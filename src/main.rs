use ashtl::alg::{
    gcd::{gcd, lcm},
    lattice,
    ops::inverse_euclidean,
    poly::Poly,
    sieve::sieve_primes,
};
use rand::Rng;
use std::time::Instant;

// const M: u64 = (119 << 23) + 1;
const M: u64 = (15 << 27) + 1;

fn binuzz(a: u64, b: u64) -> u64 {
    if b & a == b { 1 } else { 0 }
}

fn main() -> std::io::Result<()> {
    // println!("{}", find_ntt_prime(1 << 8, 1000));
    let mut rng = rand::rng();
    let n = 1 << 20;
    let k = 20;
    let i = 70;
    let d = 2;
    let z = 3;
    let q = 3;
    let inv = |a: i64| inverse_euclidean::<M>(a.rem_euclid(M as i64) as u64) as i64;
    // let mut coeff = Vec::with_capacity(n);
    // for _ in 0..n {
    //     coeff.push(rng.random_range(M >> 8..M >> 4) as i64);
    // }
    // let mut a = Poly::<M>::new(coeff);
    // let mut b = a.clone();
    // let mut coeff = Vec::with_capacity(n);
    // let mut coeff1 = Vec::with_capacity(n);
    // for _ in 0..n {
    //     coeff.push(rng.random_range(M >> 4..M) as i64);
    // }
    // for _ in 0..n << 3 {
    //     coeff1.push(rng.random_range(M >> 4..M) as i64);
    // }
    // let mut a = Poly::<M>::new(coeff);
    // let mut b = a.clone();

    // for i in 5..=10 {
    //     let k = i;
    //     let n = 1 << i;
    //     println!("{}", n);
    //     let mut rng = rand::rng();
    //     let mut coeff = Vec::with_capacity(n);
    //     for _ in 0..n {
    //         coeff.push(rng.random_range(M >> 4..M) as i64);
    //     }
    //     let mut a = Poly::<M>::new(coeff);
    //     let mut b = a.clone();
    //     let mut a1 = a.clone();
    //     let mut b1 = a.clone();
    //     let mut a2 = a.clone();
    //     let mut b2 = a.clone();
    //     let timer = Instant::now();
    //     let mut c = a.mul_naive(&b);
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut e = a * b;
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut c = a1.mul_naive(&b1);
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut e = a2 * b2;
    //     println!("{:?}", timer.elapsed());
    //     c = c.pos_normalize().truncate_deg();
    //     e = e.pos_normalize().truncate_deg();
    //     assert_eq!(c, e);
    // }

    Ok(())
}
