use crate::grph::flow::PushRelabel;
use std::ops::{AddAssign, SubAssign};

/// O(n^3 √m)
pub fn gomory_hu<F: Copy + Default + PartialOrd + AddAssign + SubAssign>(
    n: usize,
    es: &[(usize, usize, F)],
) -> (Vec<(usize, usize, F)>, Vec<usize>) {
    let mut tree = Vec::with_capacity(n - 1);
    let mut p = vec![0; n];
    let mut d = PushRelabel::<F>::new(n);
    for &(u, v, c) in es {
        d.add_edge(u, v, c, c);
    }
    for i in 1..n {
        tree.push((i, p[i], d.reset().calc(i, p[i])));
        for j in i + 1..n {
            if p[j] == p[i] && d.left_of_min_cut(j) {
                p[j] = i;
            }
        }
    }
    (tree, p)
}
