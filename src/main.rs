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
    range::seg_tree::{BitSegTree, SegTree},
};
use rand::Rng;
use std::{ops::RangeBounds, time::Instant};

// const M: u64 = (119 << 23) + 1;
const M: u64 = (15 << 27) + 1;

fn main() {
    let mut rng = rand::rng();
    let k = 3;
    let n: usize = 13;
    let d = 2;
    let z = 3;
    let q = 3;
    let inv = |a| inverse_euclidean::<M>(a);

    let nodes: Vec<(i64, Option<i64>)> = vec![5, 3, 12, 0, 7, 1, 4, 10, 8, 2, 0, 3, 6, 8, 2]
        .into_iter()
        .map(|i| (i, None))
        .collect();
    let len = nodes.len();

    let pull = |p: usize, k: usize, t: &mut [(i64, _)]| {
        if let Some(l) = t[p].1 {
            t[p].0 = l * k as i64;
        } else {
            t[p].0 = t[p << 1].0 + t[p << 1 | 1].0;
        }
    };

    let push = |p: usize, k: usize, t: &mut [(i64, _)]| {
        let lazy_val = t[p].1;
        if let Some(lazy_val) = lazy_val {
            let child_k = k >> 1;
            // Apply to left child
            t[p << 1].0 = lazy_val * child_k as i64;
            t[p << 1].1 = Some(lazy_val);
            // Apply to right child
            t[p << 1 | 1].0 = lazy_val * child_k as i64;
            t[p << 1 | 1].1 = Some(lazy_val);
            // Clear parent's lazy value
            t[p].1 = None;
        }
    };

    let mut st = SegTree::<(i64, Option<i64>), _, _>::new(
        nodes,
        |p: usize, k, t: &mut [(i64, _)]| {
            t[p].0 = t[p << 1].0 + t[p << 1 | 1].0;
            t[p].1 = None;
        },
        pull,
        push,
    );

    let mut assign_range = |st: &mut SegTree<(i64, _), _, _>, l: usize, r: usize, val: i64| {
        st.update(l..r, |p, k, t| {
            t[p].0 = val * k as i64;
            t[p].1 = Some(val);
        });
    };

    let mut range_sum = |st: &mut SegTree<(i64, _), _, _>, l: usize, r: usize| {
        st.query(
            l..r,
            0i64,                     // init_l
            0i64,                     // init_r
            |acc, node| acc + node.0, // op_l
            |node, acc| node.0 + acc, // op_r
            |l, r| l + r,             // op_s
        )
    };
    for i in 0..(len << 1).ilog2() {
        println!("{}", (len << 1) >> i);
    }
    assign_range(&mut st, 2, 9, 5); // mid-block to all 5
    assign_range(&mut st, 0, 4, 2); // nested under the first
    assign_range(&mut st, 10, 13, 7); // tail block
    assign_range(&mut st, 3, 12, 0); // overwrite huge middle
    assign_range(&mut st, 1, 2, 11); // single-element tweak
    // println!("{:?}", st.t);
    for i in 0..=len {
        println!("{i}: {}", range_sum(&mut st, 0, i));
    }
    println!("----------------");
    let mut prev = usize::MAX;
    for j in 33..34 {
        let v = st.max_right(0, |&i| i < j, 0, |i, v| i + v.0);
        if v != prev {
            println!("{j}: {}", v);
            prev = v;
        }
    }

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
