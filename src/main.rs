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

#[allow(unused_imports)]
use std::cmp::Ordering;
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::io::{BufRead, BufWriter, Read, Write, stdin, stdout};
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

use ashtl::grph::min_cut::*;

fn main() {}

// TODO ORDER:
// persistent segtree
// sparse segtree
// wavelet
// li chao
// cost scaling mcmf
// capacity scaling mcmf
// dominator tree
// rerooting
// larsch
// xor segtree
// edge coloring
// faster mod ops
// floor sum
// mod linear shit
// slope trick
// top tree
// knapsack cases
// monge algos
// trie
// online z
// dynamic tree dp
// ETT
// level ancestor
// line tree
// contour queries
// hash on tree
// improve lct
// tree iso
// xor DST
// weighted blossom
// m √n blossom
// incremental scc
// improve 2cc
// 2ecc
// 3ecc
// max clique
// max coclique
// toposort min inversions
// hampath heuristic
// min ham cycle
// sorting vectors by angle (all pairs)
// convex polygon contains point
// dsu potential
// matroid intersection
// hafnian
// redo CDQ, CDQ pow
// p recursive algos
// tutte polynomial
// sum of 2 squares
// sum of 3 squares
