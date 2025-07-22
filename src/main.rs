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
    lin::mat::Mat,
};
use rand::Rng;
use std::time::Instant;

// const M: u64 = (119 << 23) + 1;
const M: u64 = (15 << 27) + 1;
// const M: u64 = ((1_u128 << 63) - 25) as u64;

fn main() -> std::io::Result<()> {
    // put everyone's phones in my thing
    // bridge tree down to O((n+m)α(n))
    // println!("{}", find_ntt_prime(1 << 27, M << 2));
    let mut rng = rand::rng();
    let n = 1 << 4;
    let k = 100;
    let inv = |a: i64| inverse_euclidean::<M, _>(a);
    // let invs = inverses_n_div::<M>(n << 1);

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
