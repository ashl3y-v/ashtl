/// O(n)
/// preconditions: a nonempty
/// ∀ y ∈ T, f(., y) monotonic
pub fn max_subarray<T: Clone>(
    a: &[T],
    mut f: impl FnMut(T, &T) -> T,
    mut cmp: impl FnMut(&T, &T) -> bool,
) -> T {
    debug_assert!(!a.is_empty());
    let mut current_max = a[0].clone();
    let mut global_max = a[0].clone();
    for x in &a[1..] {
        let e = f(current_max, x);
        current_max = if cmp(&e, &x) { x.clone() } else { e };
        global_max = if cmp(&global_max, &current_max) {
            current_max.clone()
        } else {
            global_max
        };
    }
    global_max
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_positive() {
        let data = [1, 2, 3, 4];
        assert_eq!(max_subarray(&data, |a, b| a + b, |a, b| a < b), 10);
    }

    #[test]
    fn mixed_values() {
        let data = [-2, 1, -3, 4, -1, 2, 1, -5, 4];
        assert_eq!(max_subarray(&data, |a, b| a + b, |a, b| a < b), 6);
    }

    #[test]
    fn all_negative() {
        let data = [-5, -2, -8, -1, -3];
        assert_eq!(max_subarray(&data, |a, b| a + b, |a, b| a < b), -1);
    }
}
