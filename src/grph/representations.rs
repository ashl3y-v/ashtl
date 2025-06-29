#[inline]
pub fn edges_to_csr_undir(n: usize, es: &[[usize; 2]]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 1];

    for &[x, _] in es {
        d[x] += 1;
    }
    for i in 1..=n {
        d[i] += d[i - 1];
    }
    for &[x, y] in es {
        d[x] -= 1;
        g[d[x]] = y;
    }

    (g, d)
}

#[inline]
pub fn edges_to_csr_undir_one_based(n: usize, es: &[[usize; 2]]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 2];

    for &[x, _] in es {
        d[x] += 1;
    }
    for i in 2..=n + 1 {
        d[i] += d[i - 1];
    }
    for &[x, y] in es {
        d[x] -= 1;
        g[d[x]] = y;
    }

    (g, d)
}
