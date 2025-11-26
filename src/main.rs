// SECTION: io

#[derive(Default)]
struct Scanner {
    buffer: Vec<String>,
}

impl Scanner {
    fn next<T: std::str::FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}

use ashtl::lin::mat::Mat;
use itertools::Itertools;
use rand::Rng;
use std::cmp::Ordering;
#[allow(unused_imports)]
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::io::{BufWriter, Write, stdin, stdout};
use std::mem::MaybeUninit;
use std::ops::BitXorAssign;
use std::time::Instant;
use std::{
    fmt::{Debug, Display},
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

const M: u64 = (119 << 23) + 1;

use ashtl::alg::poly::Poly;

fn main() {
    let a = Mat::<M>::from_vec(3, 3, vec![1, -1, -1, -1, 0, 3, 1, 2, -1]);
    let v = vec![3, 1, 7];
    println!(
        "{:?}",
        Mat::<M>::minp_bb(3, |v| a.apply(&v)).neg_normalize()
    );
    println!("{:?}", a.minp());

    let x = Mat::<M>::solve_bb(v, |v| a.apply(&v));
    let mut y = a.apply(&x);
    y.iter_mut().for_each(|a| *a %= M as i64);
    println!("{:?}", x);
    println!("{:?}", y);
}
