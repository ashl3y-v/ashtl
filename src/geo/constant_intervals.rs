/// O(k log(n/k))
pub fn constant_intervals<F, G, T>(l: usize, r: usize, f: F, mut g: G)
where
    F: Fn(usize) -> T,
    G: FnMut(usize, usize, T),
    T: PartialEq + Copy,
{
    fn rec<F, G, T>(l: usize, r: usize, f: &F, g: &mut G, i: &mut usize, p: &mut T, q: T)
    where
        F: Fn(usize) -> T,
        G: FnMut(usize, usize, T),
        T: PartialEq + Copy,
    {
        if *p == q {
            return;
        } else if l == r {
            g(*i, r, *p);
            *i = r;
            *p = q;
        } else {
            let mid = (l + r) >> 1;
            let fm = f(mid);
            rec(l, mid, f, g, i, p, fm);
            rec(mid + 1, r, f, g, i, p, q);
        }
    }
    if r <= l {
        return;
    }
    let mut i = l;
    let mut p = f(i);
    let q = f(r - 1);
    rec(l, r - 1, &f, &mut g, &mut i, &mut p, q);
    g(i, r, q);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_intervals() {
        let v = vec![1, 1, 2, 2, 2, 3];
        let mut runs = Vec::new();
        constant_intervals(
            0,
            v.len(),
            |x| v[x],
            |lo, hi, val| {
                runs.push((lo, hi, val));
            },
        );
        assert_eq!(runs, vec![(0, 2, 1), (2, 5, 2), (5, 6, 3)]);
    }
}
