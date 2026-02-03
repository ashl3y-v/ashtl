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

fn main() {
    let mut sc = Scanner::default();
    let n: usize = sc.next();
    let m: u64 = sc.next();
    if n == 1 {
        println!("1");
        return;
    }
}

// TODO ORDER:
// ----------------------------------------------------------------------
// dominator tree
// matroid intersection
// weighted blossom
// m √n blossom
// O(log^2 n) dynamic connectivity https://loj.ac/s/2497274
// AM tree https://arxiv.org/pdf/2504.04619v1 https://judge.yosupo.jp/submission/345113
// incremental msf
// top tree
// https://judge.yosupo.jp/problem/dynamic_graph_vertex_add_component_sum
// min ham cycle
// hafnian
// hampath heuristic
// dsu potential
// persistent dsu
// faster mod ops
// slope trick utils
// st numbering
// floor sum
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
