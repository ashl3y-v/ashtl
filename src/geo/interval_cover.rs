/// O(n log n)
pub fn interval_cover<T: Copy + PartialOrd>(goal: (T, T), intervals: &[(T, T)]) -> Vec<usize> {
    let (g_x, g_y) = goal;
    let mut s: Vec<usize> = (0..intervals.len()).collect();
    s.sort_unstable_by(|&a, &b| intervals[a].partial_cmp(&intervals[b]).unwrap());
    let mut result = Vec::new();
    let mut cur = g_x;
    let mut at = 0;
    let n = intervals.len();
    while cur < g_y {
        let mut mx_y = cur;
        let mut mx_i = None;
        while at < n && intervals[s[at]].0 <= cur {
            let (_, end) = intervals[s[at]];
            if end > mx_y {
                mx_y = end;
                mx_i = Some(s[at]);
            }
            at += 1;
        }
        if let Some(idx) = mx_i {
            result.push(idx);
            cur = mx_y;
        } else {
            return Vec::new();
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::interval_cover;

    #[test]
    fn test_interval_cover_simple() {
        let intervals = vec![(1, 4), (2, 5), (3, 6)];
        let result = interval_cover((1, 6), &intervals);
        assert_eq!(result, vec![0, 2]);
    }

    #[test]
    fn test_interval_cover_failure() {
        let intervals = vec![(0, 1), (2, 3)];
        let result = interval_cover((0, 3), &intervals);
        assert!(result.is_empty());
    }

    #[test]
    fn test_interval_cover_exact() {
        let intervals = vec![(0, 2), (2, 4), (1, 3)];
        let result = interval_cover((0, 4), &intervals);
        assert_eq!(result, vec![0, 1]);
    }
}
