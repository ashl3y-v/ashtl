use std::collections::VecDeque;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MonotoneStack<T, F: FnMut(&T, &T) -> bool> {
    pub stk: Vec<(T, T)>,
    pub min: Option<T>,
    pub cmp: F,
}

impl<T: Clone, F: FnMut(&T, &T) -> bool> MonotoneStack<T, F> {
    pub fn new(cmp: F) -> Self {
        Self {
            stk: Vec::new(),
            min: None,
            cmp,
        }
    }

    pub fn with_capacity(n: usize, cmp: F) -> Self {
        Self {
            stk: Vec::with_capacity(n),
            min: None,
            cmp,
        }
    }

    pub fn push(&mut self, value: T) -> &mut Self {
        let new_min = if self.min.is_none() || (self.cmp)(&value, self.min.as_ref().unwrap()) {
            self.min = Some(value.clone());
            value.clone()
        } else {
            self.min.clone().unwrap()
        };
        self.stk.push((value, new_min));
        self
    }

    pub fn pop(&mut self) -> Option<T> {
        self.stk.pop().map(|v| v.0)
    }

    pub fn min(&self) -> Option<T> {
        self.stk.last().map(|v| v.1.clone())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MonotoneQueue<T, F: FnMut(&T, &T) -> bool> {
    pub q: VecDeque<T>,
    pub cmp: F,
}

impl<T: PartialEq, F: FnMut(&T, &T) -> bool> MonotoneQueue<T, F> {
    pub fn new(cmp: F) -> Self {
        Self {
            q: VecDeque::new(),
            cmp,
        }
    }

    pub fn with_capacity(n: usize, cmp: F) -> Self {
        Self {
            q: VecDeque::with_capacity(n),
            cmp,
        }
    }

    pub fn push_back(&mut self, value: T) -> &mut Self {
        while !self.q.is_empty() && (self.cmp)(&value, self.q.back().unwrap()) {
            self.q.pop_back();
        }
        self.q.push_back(value);
        self
    }

    pub fn pop_front(&mut self, value: &T) -> &mut Self {
        if !self.q.is_empty() && self.q.front().unwrap() == value {
            self.q.pop_front();
        }
        self
    }

    pub fn min(&self) -> Option<&T> {
        self.q.front()
    }
}

/// O(n)
pub fn min_len_k_subarrays<T: Clone + PartialEq, F: FnMut(&T, &T) -> bool>(
    a: &[T],
    cmp: F,
    k: usize,
) -> Vec<T> {
    let n = a.len();
    if k == 0 || n < k {
        return Vec::new();
    }
    let mut mq = MonotoneQueue::with_capacity(k, cmp);
    let mut result = Vec::with_capacity(n - k + 1);
    for i in 0..k {
        mq.push_back(a[i].clone());
    }
    if let Some(m) = mq.min() {
        result.push(m.clone());
    }
    for i in k..n {
        mq.pop_front(&a[i - k]);
        mq.push_back(a[i].clone());
        if let Some(m) = mq.min() {
            result.push(m.clone());
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn test_empty_and_small() {
        let v: Vec<i32> = vec![];
        assert_eq!(min_len_k_subarrays(&v, |a, b| a < b, 3), vec![]);
        let v = vec![7];
        assert_eq!(min_len_k_subarrays(&v, |a, b| a < b, 1), vec![7]);
        assert_eq!(min_len_k_subarrays(&v, |a, b| a < b, 2), vec![]);
    }

    #[test]
    fn test_simple_numeric() {
        let v = vec![2, 1, 3, 4, 0, 5];
        let got = min_len_k_subarrays(&v, |a, b| a < b, 3);
        assert_eq!(got, vec![1, 1, 0, 0]);

        let v = vec![5, 5, 5, 5];
        let got = min_len_k_subarrays(&v, |a, b| a < b, 2);
        assert_eq!(got, vec![5, 5, 5]);
    }

    #[test]
    fn test_increasing_and_decreasing() {
        let inc = vec![1, 2, 3, 4, 5];
        assert_eq!(min_len_k_subarrays(&inc, |a, b| a < b, 2), vec![1, 2, 3, 4]);
        let dec = vec![5, 4, 3, 2, 1];
        assert_eq!(min_len_k_subarrays(&dec, |a, b| a < b, 3), vec![3, 2, 1]);
    }

    #[test]
    fn test_k_equals_one() {
        let v = vec![9, 8, 7];
        assert_eq!(min_len_k_subarrays(&v, |a, b| a < b, 1), v);
    }

    #[test]
    fn test_random_against_naive() {
        let mut rng = rand::rng();
        for _ in 0..50 {
            let n = 50;
            let k = rng.random_range(1..=n);
            let v: Vec<u32> = (0..n).map(|_| rng.random_range(0..1000)).collect();
            let got = min_len_k_subarrays(&v, |a, b| a < b, k);
            let mut want = Vec::new();
            for i in 0..=n - k {
                let m = v[i..i + k].iter().min().unwrap();
                want.push(*m);
            }
            assert_eq!(got, want);
        }
    }
}
