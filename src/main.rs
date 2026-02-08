// SECTION: io

#[derive(Default)]
struct Scanner {
    buffer: Vec<String>,
}

impl Scanner {
    fn next<T: FromStr>(&mut self) -> T {
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

#[allow(unused_imports)]
use std::str::FromStr;

// fn main() {
//     let mut sc = Scanner::default();
//     let n: usize = sc.next();
//     let m: u64 = sc.next();
//     if n == 1 {
//         println!("1");
//         return;
//     }
// }

use rand::Rng;
use rand::seq::SliceRandom;
use std::cmp::{max, min};
use std::time::Instant;

use ashtl::grph::matching::blossom;

fn main() {}

// TODO ORDER:
// weighted blossom
// m √n blossom
// matroid intersection
// floor sum
// O(log^2 n) dynamic connectivity https://loj.ac/s/2497274
// ----------------------------------------------------------------------
// Persistent Range Affine Range Sum
// Range Linear Add Range Min
// Deque Operate All Composite
// hampath heuristic
// top tree
// min ham cycle
// hafnian
// faster mod ops
// slope trick utils
// st numbering
// mod linear shit
// dynamic rerooting tree dp
// ----------------------------------------------------------------------
// larsch
// monge algos
// knapsack cases
// cc2
// 2ecc
// pfaffian
// fix splay tree
// axiotis tzamos may be wrong
// trie
// online z
// level ancestor
// line tree
// contour queries
// hash on tree
// tree iso
// 3ecc
// max clique
// max coclique
// convex polygon contains point
// redo CDQ, CDQ pow
// p recursive algos
// tutte polynomial
// sum of 2 squares
// sum of 3 squares
// gomory hu proof
// dyanmic wavelet matrix
// whatever this is https://judge.yosupo.jp/submission/138316
