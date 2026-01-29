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
use std::cmp::Ordering;
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::io::{BufRead, BufWriter, Read, Write, stdin, stdout};
use std::str::FromStr;
use std::time::Instant;
use std::{
    fmt::{Debug, Display},
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

const M: u64 = (119 << 23) + 1;

use std::io;

use rand::prelude::*;

use ashtl::grph::cc::scc_incremental;
use ashtl::grph::color::*;

fn main() {
    // Setup:
    // 1. Form SCC {0, 1}
    // 2. Form SCC {2, 3}
    // 3. Add edges 1->2 and 3->0 to merge {0,1} and {2,3} into {0,1,2,3}
    let n = 4;
    let edges = vec![
        (0, 1),
        (1, 0), // 0,1 form SCC A
        (2, 3),
        (3, 2), // 2,3 form SCC B
        (1, 2), // Connect A -> B (No merge yet)
        (3, 0), // Connect B -> A (Merge all!)
    ];
    let res = scc_incremental(n, edges.clone());
    println!("{:?}", res);
}

// TODO ORDER:
// rerooting
// top tree
// ETT
// faster mod ops
// dominator tree
// floor sum
// slope trick utils
// cost scaling mcmf
// axiotis tzamos may be wrong
// dynamic rerooting tree dp
// incremental msf
// https://judge.yosupo.jp/problem/dynamic_graph_vertex_add_component_sum
// st numbering
// cc2
// larsch
// mod linear shit
// knapsack cases
// monge algos
// trie
// online z
// level ancestor
// line tree
// contour queries
// hash on tree
// improve lct
// tree iso
// weighted blossom
// m √n blossom
// improve 2cc
// 2ecc
// 3ecc
// max clique
// max coclique
// hampath heuristic
// min ham cycle
// convex polygon contains point
// dsu potential
// persistent dsu
// matroid intersection
// hafnian
// redo CDQ, CDQ pow
// p recursive algos
// tutte polynomial
// sum of 2 squares
// sum of 3 squares
// gomory hu proof
// dyanmic wavelet matrix
// pfaffian
