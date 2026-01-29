use std::ops::BitXorAssign;

#[inline]
pub fn edges_to_csr_undir(n: usize, es: &[(usize, usize)]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 1];
    for &(x, _) in es {
        d[x] += 1;
    }
    for i in 1..=n {
        d[i] += d[i - 1];
    }
    for &(x, y) in es {
        d[x] -= 1;
        g[d[x]] = y;
    }
    (g, d)
}

#[inline]
pub fn edges_to_csr_undir_one_based(n: usize, es: &[(usize, usize)]) -> (Vec<usize>, Vec<usize>) {
    let mut g = vec![0; es.len()];
    let mut d = vec![0; n + 2];
    for &(x, _) in es {
        d[x] += 1;
    }
    for i in 2..=n + 1 {
        d[i] += d[i - 1];
    }
    for &(x, y) in es {
        d[x] -= 1;
        g[d[x]] = y;
    }
    (g, d)
}

pub fn es_to_xor<T: Copy + Default + BitXorAssign, E>(
    n: usize,
    es: impl Iterator<Item = E>,
    mut to: impl FnMut(&E) -> (usize, usize, T),
) -> (Vec<usize>, Vec<usize>, Vec<T>) {
    let (mut d, mut p, mut w) = (vec![0; n], vec![0; n], vec![T::default(); n]);
    for e in es {
        let (u, v, c) = to(&e);
        d[u] += 1;
        d[v] += 1;
        p[u] ^= v;
        p[v] ^= u;
        w[u] ^= c;
        w[v] ^= c;
    }
    d[0] = usize::MAX;
    (p, d, w)
}
