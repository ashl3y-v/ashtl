/// O(k log(n/k)), where k is number of constant intervals
pub fn constant_intervals<F, G, T>(from: usize, to: usize, f: F, mut g: G)
where
    F: Fn(usize) -> T,
    G: FnMut(usize, usize, T),
    T: PartialEq + Copy,
{
    if to <= from {
        return;
    }
    let mut i = from;
    let mut p = f(i);
    let q = f(to - 1);
    rec(from, to - 1, &f, &mut g, &mut i, &mut p, q);
    g(i, to, q);
}

fn rec<F, G, T>(from: usize, to: usize, f: &F, g: &mut G, i: &mut usize, p: &mut T, q: T)
where
    F: Fn(usize) -> T,
    G: FnMut(usize, usize, T),
    T: PartialEq + Copy,
{
    if *p == q {
        return;
    }
    if from == to {
        g(*i, to, *p);
        *i = to;
        *p = q;
    } else {
        let mid = (from + to) >> 1;
        let fm = f(mid);
        rec(from, mid, f, g, i, p, fm);
        rec(mid + 1, to, f, g, i, p, q);
    }
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
