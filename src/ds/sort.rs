use crate::ds::bit_vec::BitVec;

/// counting sort O(n + k) time O(k) space
/// k must be a strict upper bound
pub fn counting_sort(a: &mut [usize], k: usize) -> &mut [usize] {
    let mut counts = vec![0; k];
    for &x in &*a {
        counts[x] += 1;
    }
    let mut i = 0;
    for v in 0..k {
        let c = counts[v];
        for _ in 0..c {
            a[i] = v;
            i += 1;
        }
    }
    a
}

/// counting sort with dedup O(n + k) time O(k) space
/// k must be a strict upper bound
pub fn counting_sort_dedup(a: &mut [usize], k: usize) -> usize {
    let mut seen = BitVec::new(k, false);
    for &x in &*a {
        seen.set(x, true);
    }
    let mut i = 0;
    for v in 0..k {
        if seen[v] {
            a[i] = v;
            i += 1;
        }
    }
    i
}

// counting sort by key O(n + k) time O(k) space
pub fn counting_sort_by_key<T: Clone, F: Fn(&T) -> usize>(
    a: &mut [T],
    k: usize,
    key: F,
) -> &mut [T] {
    let n = a.len();
    if n == 0 || k == 0 {
        return a;
    }
    let mut counts = vec![0; k];
    for x in a.iter() {
        counts[key(x)] += 1;
    }
    let mut start = vec![0; k];
    for i in 1..k {
        start[i] = start[i - 1] + counts[i - 1];
    }
    let end: Vec<usize> = start.iter().zip(&counts).map(|(&s, &c)| s + c).collect();
    let mut positions = start.clone();
    let mut i = 0;
    while i < n {
        let b = key(&a[i]);
        if i >= start[b] && i < end[b] {
            if positions[b] == i {
                positions[b] += 1;
            }
            i += 1;
        } else {
            a.swap(i, positions[b]);
            positions[b] += 1;
        }
    }
    a
}

/// counting sort deduped by key O(n + k) time O(k) space
pub fn counting_sort_dedup_by_key<T: Clone, F: Fn(&T) -> usize>(
    a: &mut [T],
    k: usize,
    key: F,
) -> usize {
    let mut repr: Vec<Option<T>> = vec![None; k];
    for x in a.iter() {
        let v = key(x);
        if v < k {
            if repr[v].is_none() {
                repr[v] = Some(x.clone());
            }
        }
    }
    let mut i = 0;
    for item in repr.into_iter().flatten() {
        a[i] = item;
        i += 1;
    }
    i
}
