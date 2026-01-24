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

use ashtl::geo::angle::*;
use ashtl::geo::point::*;
use ashtl::tree::wavelet::*;

fn main() {}

// TODO ORDER:
// edge coloring
// faster mod ops
// dominator tree
// floor sum
// slope trick utils
// https://judge.yosupo.jp/problem/dynamic_graph_vertex_add_component_sum
// cost scaling mcmf
// rerooting
// larsch
// mod linear shit
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
// convex polygon contains point
// dsu potential
// matroid intersection
// hafnian
// redo CDQ, CDQ pow
// p recursive algos
// tutte polynomial
// sum of 2 squares
// sum of 3 squares
// gomory hu proof
// dyanmic wavelet matrix
