pub fn cartesian<T: PartialOrd>(a: &[T]) -> Vec<usize> {
    let n = a.len();
    let mut p = vec![usize::MAX; n];
    let mut stk = Vec::with_capacity(n);
    for i in 0..n {
        let mut last = usize::MAX;
        while let Some(&l) = stk.last() {
            if a[l] < a[i] {
                break;
            }
            last = l;
            stk.pop();
        }
        if let Some(&l) = stk.last() {
            p[i] = l;
        }
        if last != usize::MAX {
            p[last] = i;
        }
        stk.push(i);
    }
    p
}

// TODO: add building cartesian treap from tree

#[cfg(test)]
mod tests {
    use super::cartesian;

    fn basic() {
        let a = vec![6, 9, 2, 4, 7, 8, 5, 8, 3, 7];
        let p = cartesian(&a);
        assert_eq!(p, [2, 0, 18446744073709551615, 8, 6, 4, 3, 6, 2, 8]);
    }
}
