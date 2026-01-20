use crate::{
    alg::fps::{E, Poly},
    ds::bit_vec::BitVec,
};
use rand::Rng;

pub fn wildcard_match<const M: u64>(s: &str, t: &str, wild: char, rng: &mut impl Rng) -> BitVec {
    let n = s.len();
    let m = t.len();
    if n < m {
        return BitVec::new(0, false);
    }
    let shift = rng.random_range(0..M as E);
    let mut mi = E::MAX;
    for c in s.chars().chain(t.chars()) {
        if c != wild {
            if (c as E) < mi {
                mi = c as E;
            }
        }
    }
    let to_e = |c: char| -> E {
        if c == wild {
            0
        } else {
            c as E - mi + 1 + shift
        }
    };
    let f: Vec<E> = s.chars().map(to_e).collect();
    let g: Vec<E> = t.chars().map(to_e).collect();
    let mut f1 = Poly::<M>::new(Vec::with_capacity(f.len()));
    let mut f2 = Poly::<M>::new(Vec::with_capacity(f.len()));
    let mut f3 = Poly::<M>::new(Vec::with_capacity(f.len()));
    for x in f {
        f1.coeff.push(x);
        let x2 = x * x % M as E;
        f2.coeff.push(x2);
        let x3 = x2 * x % M as E;
        f3.coeff.push(x3);
    }
    let mut g1 = Poly::new(Vec::with_capacity(g.len()));
    let mut g2 = Poly::new(Vec::with_capacity(g.len()));
    let mut g3 = Poly::new(Vec::with_capacity(g.len()));
    for x in g {
        g1.coeff.push(x);
        let x2 = x * x % M as E;
        g2.coeff.push(x2);
        let x3 = x2 * x % M as E;
        g3.coeff.push(x3);
    }
    g1.coeff.reverse();
    g2.coeff.reverse();
    g3.coeff.reverse();
    let a = f1 * g3;
    let b = f2 * g2;
    let c = f3 * g1;
    let mut res = BitVec::new(n - m + 1, false);
    for i in (m - 1)..n {
        let val_a = if i < a.coeff.len() { a.coeff[i] } else { 0 };
        let val_b = if i < b.coeff.len() { b.coeff[i] } else { 0 };
        let val_c = if i < c.coeff.len() { c.coeff[i] } else { 0 };
        let val = val_a - 2 * val_b + val_c;
        res.set(i - (m - 1), val == 0);
    }
    res
}
