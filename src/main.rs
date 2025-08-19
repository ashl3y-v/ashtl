use ashtl::{
    alg::{
        lattice, mult, ntt,
        ops::{self, inverse_euclidean, mod_pow},
        poly::{Poly, Poly2},
        primitive, special,
    },
    ds::{knapsack, set},
    grph::color,
};
use rand::Rng;
use std::{collections::HashSet, time::Instant};

// const M: u64 = (119 << 23) + 1;
// const M: u64 = (7 << 26) + 1;
const M: u64 = (15 << 27) + 1;
// const M: u64 = ((1_u128 << 63) - 25) as u64;

fn main() -> std::io::Result<()> {
    let mut rng = rand::rng();
    // println!("{}", find_ntt_prime(1 << 27, M << 20));
    // put everyone's phones in my thing
    // prufer sequences
    // get rid of stuff taking mut self and n
    // make stuff use truncate_deg instead of doing stuff up to deg
    // ntt faster
    // println!("{}", find_ntt_prime(1 << 27, M << 2));
    // gs:

    let inv = |a: i64| inverse_euclidean::<M, _>(a);
    let inv_u = |a: i64| inverse_euclidean::<M, _>(a).rem_euclid(M as i64) as u64;

    // schedule:
    // q borel -> q poch
    // relaxed convolution
    // composition special cases
    // half-gcd
    // bivariate extensions of fundamental operations https://maspypy.github.io/library/poly/2d/fps_inv_2d.hpp
    // frobenius
    // transposed bostan mori
    // mcmf
    // hungarian?
    // dominator tree?
    let n = 1 << 5;
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
    let mut b = Poly::<M>::new(coeff);

    // let b = Poly::<M>::new(vec![]);
    // let timer = Instant::now();
    // let c = a.clone().evals(&pts).neg_normalize();
    // println!("{:?}", timer.elapsed());
    // let timer = Instant::now();
    // let d = c.interp(&pts).neg_normalize();
    // println!("{:?}", timer.elapsed());
    // println!("{:?}", &c.coeff[..10]);
    // println!("{:?}", &d.coeff[..10]);
    // assert_eq!(d, a);
    // println!("{:?}", &a.neg_normalize().coeff[..10]);

    // let timer = Instant::now();
    // println!("{:?}", timer.elapsed());
    // let a = Poly::<M>::new(vec![0, 1]);
    // let b = Poly::<M>::new(vec![1, -1, -1]);
    // let timer = Instant::now();
    // let b = a.clone().comp_inv();
    // println!("{:?}", timer.elapsed());
    // let c = b.comp(&a, n).neg_normalize();
    // println!("{:?}", c);
    // assert_eq!(c.coeff[0], 0);
    // assert_eq!(c.coeff[1], 1);
    // println!(
    //     "{:?}",
    //     c.coeff.iter().skip(2).position(|&i| i != 0).map(|i| i + 2)
    // );
    // let timer = Instant::now();
    // println!("{:?}", timer.elapsed());
    // let a = Poly::<M>::new(vec![1, 2, 3, 4]);
    // let b = Poly::<M>::new(vec![7, 3, 2, 1]);
    //sum_{i=k}^n a_i c^i i! 1/(k-i)! 1/k! c^-k
    // let mut d = a.comp_naive(&b, n).mod_xn(n);
    // let mut d = a.comp_naive(&b, n << 1).mod_xn(n << 1);
    // let timer = Instant::now();
    // let mut c = a.resize(n << 1).comp(b);
    // println!("{:?}", timer.elapsed());
    // println!("{} {} {}", n, c.len(), d.len());
    // (c, d) = (c.neg_normalize(), d.neg_normalize());
    // assert_eq!(c, d);
    // println!("{:?}\n{:?}", c, d);
    // assert_eq!(c, d);

    // let mut coeff = Vec::with_capacity(n);
    // for _ in 0..n {
    //     coeff.push(rng.random_range(M >> 4..M) as i64);
    // }
    // coeff[0] = 1;
    // let mut a = Poly::<M>::new(coeff);
    // let mut coeff = Vec::with_capacity(n);
    // for _ in 0..n {
    //     coeff.push(rng.random_range(M >> 4..M) as i64);
    // }
    // coeff[0] = 1;
    // let mut a = Poly::<M>::new(coeff);
    // let mut b = a.clone();
    // let timer = Instant::now();
    // a = a.clone().mul_neg_self().even(n);
    // println!("{:?}", timer.elapsed());
    // let timer = Instant::now();
    // b = b.mul_neg_self_even();
    // println!("{:?}", timer.elapsed());
    // a = a.pos_normalize();
    // b = b.pos_normalize();
    // println!("{:?}", a);
    // println!("{:?}", b);
    // assert_eq!(a, b);

    // let z = Poly::<M>::stirling1(n);
    // let x = z.clone().reverse().neg_normalize();
    // let y = x.clone().elem_symm_to_pow_sum().neg_normalize();
    // let a = Poly::<M>::stirling1(n).neg_normalize();
    // let b = Poly::<M>::stirling1_new(n).neg_normalize();
    // println!("a {:?}\nb {:?}", a, b);
    // println!("x {:?}", x);
    // println!("y {:?}", y);
    // println!("{} {}", b.len(), y.len());
    // assert_eq!(b, x);

    // let mut coeff = Vec::with_capacity(n);
    // for _ in 0..n {
    //     coeff.push(rng.random_range(M >> 4..M) as i64);
    // }
    // let mut a = Poly::<M>::new(coeff);
    // let timer = Instant::now();
    // let mut b = a.clone().to_fall().evals_n_fall(n).pos_normalize();
    // println!("{:?}", timer.elapsed());
    // let timer = Instant::now();
    // let c = Poly::<Mexp_ax(2,20);
    // assert_eq!(a,b);
    // // bet c = Poly::<Mexp_ax_new(2,20)a
    // // bet c = Poly::<Mexp_ax_new(2,2b)a

    // let timer = Instant::now();
    // let mut b = a.clone().sps_pow_bin(k).pos_normalize();
    // println!("{:?}", timer.elapsed());
    // let timer = Instant::now();
    // let mut c = a.clone().sps_pow(k).pos_normalize();
    // println!("{:?}", timer.elapsed());
    // assert_eq!(b, c);

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
