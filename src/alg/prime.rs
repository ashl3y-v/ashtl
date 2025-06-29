use crate::ds::sort::{counting_sort, counting_sort_dedup};

use super::{gcd::gcd, miller_rabin::miller_rabin};

fn pollard(n: usize) -> usize {
    let mut x = 0usize;
    let mut y = 0usize;
    let mut t = 30usize;
    let mut prd = 2usize;
    let mut i = 1usize;
    loop {
        if t % 40 != 0 || gcd(prd, n) == 1 {
            if x == y {
                i += 1;
                x = i;
                y = (x * x % n + i) % n;
            }
            let diff = if x > y { x - y } else { y - x };
            let q = prd * diff % n;
            if q != 0 {
                prd = q;
            }
            x = (x * x % n + i) % n;
            y = (((y * y % n + i) % n) * ((y * y % n + i) % n) % n + i) % n;
            t += 1;
        } else {
            break;
        }
    }
    gcd(prd, n)
}

pub fn factor(n: usize) -> Vec<usize> {
    if n == 1 {
        return Vec::new();
    }
    if miller_rabin(n as u64) {
        return vec![n];
    }
    let x = pollard(n);
    let mut left = factor(x);
    let right = factor(n / x);
    left.extend(right);
    left
}

pub fn factor_mult(n: usize) -> Vec<(usize, u32)> {
    let mut fs = factor(n);
    counting_sort(&mut fs, n + 1);
    let mut f = vec![(fs[0], 1)];
    let mut f_len = 1;
    let mut cp = fs[0];
    for i in 1..fs.len() {
        if fs[i] == cp {
            f[f_len - 1].1 += 1;
        } else {
            cp = fs[i];
            f.push((fs[i], 1));
            f_len += 1;
        }
    }
    f
}

pub fn factor_dedup(n: usize) -> Vec<usize> {
    let mut fs = factor(n);
    counting_sort_dedup(&mut fs, n + 1);
    fs
}
