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
use std::io::{BufRead, BufWriter, Write, stdin, stdout};
use std::time::Instant;
use std::{
    fmt::{Debug, Display},
    ops::{
        Add, AddAssign, Bound, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Neg, RangeBounds,
        Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

const M: u64 = (119 << 23) + 1;

use ashtl::string::palindrome::Eertree;
use ashtl::string::suffix_array::SuffixArray;
use ashtl::string::suffix_automaton::SuffixAutomaton;
use ashtl::string::suffix_tree::SuffixTree;
use std::io;

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock().lines();
    let mut out = io::BufWriter::new(io::stdout());

    if let Some(Ok(line)) = input.next() {
        let s = line.trim();
        if s.is_empty() {
            return;
        }
        let s_old = s.clone();
        let s = s.as_bytes();

        let mut tree = Eertree::new(5);
        let mut last_node = 0;
        for _ in 0..5 {
            last_node = tree.add('a');
        }
        // Should have: 'a', 'aa', 'aaa', 'aaaa', 'aaaaa' (nodes 3-7)
        // Total: nodes 1, 2, 3, 4, 5, 6, 7, 8 = 8 nodes, sz = 8
        println!("{:?}", tree);

        //     for (i, &val) in sa.sa.iter().enumerate() {
        //         if i > 0 {
        //             write!(out, " ").ok();
        //         }
        //         write!(out, "{}", val).ok();
        //     }
        //     writeln!(out).ok();
    }
}
