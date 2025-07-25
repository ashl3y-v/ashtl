use ashtl::{
    alg::{
        gcd::{gcd, lcm},
        lattice,
        ntt::find_ntt_prime,
        ops::{self, inverse_euclidean, inverses_n_div, mod_pow, mod_sqrt},
        poly::Poly,
        prime::{self, miller_rabin},
        sieve::{self, sieve_primes},
        special::{fibonacci_mod, jacobi},
        zsqrt::ZSqrt,
    },
    grph::color::{self, k_col},
    lin::mat::Mat,
};
use rand::Rng;
use std::time::Instant;

// const M: u64 = (119 << 23) + 1;
const M: u64 = (15 << 27) + 1;
// const M: u64 = ((1_u128 << 63) - 25) as u64;

fn main() -> std::io::Result<()> {
    // put everyone's phones in my thing
    // println!("{}", find_ntt_prime(1 << 27, M << 2));
    let mut rng = rand::rng();
    let inv = |a: i64| inverse_euclidean::<M, _>(a);
    let inv_u = |a: i64| inverse_euclidean::<M, _>(a).rem_euclid(M as i64) as u64;
    // let invs = inverses_n_div::<M>(n << 1);
    let n = 1 << 8;
    let m = 1 << 9;
    let k = M as usize - 1;
    let i = 7;
    let n = 17;

    let mut a = Poly::<M>::new(vec![0; 1 << n]);
    a.coeff[0] = 1;
    let mut coeff = Vec::with_capacity(n);
    for _ in 0..1 << n {
        coeff.push(rng.random_range(M >> 4..M) as i64);
    }
    coeff[0] = 1;
    let mut a = Poly::<M>::new(coeff);
    let timer = Instant::now();
    let mut b = a.clone().sps_pow_bin(k).pos_normalize();
    println!("{:?}", timer.elapsed());
    let timer = Instant::now();
    let mut c = a.clone().sps_pow(k).pos_normalize();
    println!("{:?}", timer.elapsed());
    assert_eq!(b, c);

    // for i in 5..=12 {
    //     let k = i;
    //     let n = 1 << i;
    //     println!("{}", n);
    //     let mut rng = rand::rng();
    //     let mut coeff = Vec::with_capacity(n);
    //     for _ in 0..n {
    //         coeff.push(rng.random_range(M >> 4..M) as i64);
    //     }
    //     let mut a = Poly::<M>::new(coeff);
    //     a[0] = 1;
    //     let timer = Instant::now();
    //     let mut b = a.clone().sqrt(n).unwrap();
    //     println!("sqrt {:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut c = a.clone().pow(inv_u(2) as usize, n);
    //     println!("pow {:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut b = a.clone().sqrt(n).unwrap();
    //     println!("sqrt {:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let mut c = a.clone().pow(inv_u(2) as usize, n);
    //     println!("pow {:?}", timer.elapsed());
    //     b = b.pos_normalize().truncate_deg();
    //     c = c.pos_normalize().truncate_deg();
    //     assert_eq!(b, c);
    // }

    // for k in 3..=20 {
    //         let a = 1 << k;
    //         let mut min = (u32::MAX, u32::MAX);
    //         for b in [16_u32, 32, 64, 128] {
    //             let mut c = 0;
    //             let mut d = a / b;
    //             while d > 1 {
    //                 c += d;
    //                 d = (d + b - 1) / b;
    //             }
    //             c += 1;
    //             c *= b;
    //             if c < min.1 {
    //                 min = (b, c);
    //             }
    //         }
    //         println!("{} {:?}", a, (min.0, min.1 >> 3));
    //     }

    Ok(())
}
