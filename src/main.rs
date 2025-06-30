use ashtl::{
    alg::{
        lattice::subset_convolution,
        ops::{
            inverse_euclidean, inverses, inverses_n_div, mod_fact, mod_kth_root, mod_pow,
            mod_rfact, mod_sqrt,
        },
        poly::Poly,
        sieve::{self, linear_sieve_complete},
    },
    ds::first_one::FirstOne,
    lin::mat::Mat,
    range::{
        seg_tree::SegTree,
        sparse_table::{DisjointSparseTable, SparseTable},
    },
    tree::splay::Splay,
};
use rand::Rng;
use std::{ops::RangeBounds, time::Instant};

// const M: u64 = (119 << 23) + 1;
const M: u64 = (15 << 27) + 1;

fn main() {
    let mut rng = rand::rng();
    let k = 20;
    let n = 1 << k;
    let d = 2;
    let z = 3;
    let q = 3;
    let inv = |a| inverse_euclidean::<M>(a);
    let a = Mat::<M>::from_slice(2, 2, &[1, 2, 3, 4]);
    let mut b = Mat::<M>::from_slice(2, 2, &[4, 3, 2, 1]);
    let mut c = a.diamond(&b);
    println!("{:?}", c);

    // println!("----------------");
    // let mut prev = usize::MAX;
    // for j in 0..1000 {
    //     let v = st.max_right(0, |&i| i <= j, 0, |i, v| i + v.deg_or_0());
    //     if v != prev {
    //         println!("{j}: {}", v);
    //         prev = v;
    //     }
    // }

    // for i in 5..25 {
    //     let k = i;
    //     let n = 1 << i;
    //     println!("{:?}", i);
    //     let mut rng = rand::rng();
    //     let mut coeff = Vec::with_capacity(1 << k);
    //     let mut coeff1 = Vec::with_capacity(1 << (k - 4));
    //     for _ in 0..1 << k {
    //         coeff.push(rng.random_range(M >> 4..M) as i64);
    //     }
    //     for _ in 0..1 << k - 4 {
    //         coeff1.push(rng.random_range(M >> 4..M) as i64);
    //     }
    //     let mut a = Poly::<M>::new(coeff);
    //     let mut b = Poly::<M>::new(coeff1);
    //     let timer = Instant::now();
    //     let (d0, r0) = a.div_mod(&b);
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let (d1, r1) = a.div_mod_small(&b);
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let (d0, r0) = a.div_mod(&b);
    //     println!("{:?}", timer.elapsed());
    //     let timer = Instant::now();
    //     let (d1, r1) = a.div_mod_small(&b);
    //     println!("{:?}", timer.elapsed());
    //     // println!("{:?} {:?}", d0, d1);
    //     assert_eq!(
    //         d0.pos_normalize().truncate_deg(),
    //         d1.pos_normalize().truncate_deg()
    //     );
    //     assert_eq!(
    //         r0.pos_normalize().truncate_deg(),
    //         r1.pos_normalize().truncate_deg()
    //     );
    // }
}
