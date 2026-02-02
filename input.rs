#[allow(unused_imports)]
use std::cmp::{max, min};
use std::{
    io::{BufWriter, Write, stdin, stdout},
    ops::Index,
};

const M: u64 = (119 << 23) + 1;
// const M: u64 = (15 << 27) + 1;

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
            stdin().read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}

fn main() {
    let mut scan = Scanner::default();
    let out = &mut BufWriter::new(stdout());

    let n: usize = scan.next();
    let u: usize = scan.next();
    let b = Poly::<M>::new(vec![]);
    for i in 0..n {}
}
