use ashtl::alg::{
    ops::{inverse_euclidean, inverses_n_div},
    poly::Poly,
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
    let n = 1 << 2;
    let k = 7;
    let i = 3;
    let d = 2;
    let z = 3;
    let q = 3;
    let inv = |a: i64| inverse_euclidean::<M>(a.rem_euclid(M as i64) as u64) as i64;
    let mut coeff = Vec::with_capacity(n);
    let mut coeff1 = Vec::with_capacity(n);
    for _ in 0..n {
        coeff.push(rng.random_range(M >> 4..M) as i64);
    }
    for _ in 0..n << 3 {
        coeff1.push(rng.random_range(M >> 4..M) as i64);
    }
    let mut a = Poly::<M>::new(coeff);
    let mut b = Poly::<M>::new(coeff1);
    let timer = Instant::now();
    let mut c = a.clone().pow_mod(k, b.clone());
    println!("{:?}", timer.elapsed());
    let mut d = a.clone().pow(k, c.len()) % b.clone();
    c.coeff.truncate(d.coeff.len());
    assert_eq!(c.pos_normalize(), d.pos_normalize());

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
