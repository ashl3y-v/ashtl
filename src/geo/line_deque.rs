use std::{
    collections::VecDeque,
    ops::{Add, Mul, Sub},
};

/// Line Deque for CHT O(n + q)
pub struct LineDeque<T> {
    pub lines: VecDeque<(T, T)>,
}

impl<T> LineDeque<T>
where
    T: Copy + PartialOrd + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    pub fn new() -> Self {
        LineDeque {
            lines: VecDeque::new(),
        }
    }

    /// preconditions: `x` non-decreasing between calls
    pub fn query_front(&mut self, x: T) -> T {
        while self.lines.len() >= 2 {
            let l0 = &self.lines[0];
            let l1 = &self.lines[1];
            if l1.0 - l0.0 >= (l0.1 - l1.1) * x {
                self.lines.pop_front();
            } else {
                break;
            }
        }
        self.lines
            .front()
            .map(|&(b, m)| m * x + b)
            .expect("LineDeque empty")
    }

    /// preconditions: `x` non-increasing between calls
    pub fn query_back(&mut self, x: T) -> T {
        while self.lines.len() >= 2 {
            let n = self.lines.len();
            let l0 = &self.lines[n - 1];
            let l1 = &self.lines[n - 2];
            if l0.0 - l1.0 <= (l1.1 - l0.1) * x {
                self.lines.pop_back();
            } else {
                break;
            }
        }
        self.lines
            .back()
            .map(|&(b, m)| m * x + b)
            .expect("LineDeque empty")
    }

    /// preconditions: `line.1` non-decreasing
    pub fn push_back(&mut self, line: (T, T)) -> &mut Self {
        while self.lines.len() >= 2 {
            let n = self.lines.len();
            let l0 = &self.lines[n - 1];
            let l1 = &self.lines[n - 2];
            if (l0.0 - l1.0) * (l0.1 - line.1) >= (line.0 - l0.0) * (l1.1 - l0.1) {
                self.lines.pop_back();
            } else {
                break;
            }
        }
        self.lines.push_back(line);
        self
    }

    /// preconditions: `line.1` non-increasing
    pub fn push_front(&mut self, line: (T, T)) -> &mut Self {
        while self.lines.len() >= 2 {
            let l0 = &self.lines[0];
            let l1 = &self.lines[1];
            if (l0.0 - line.0) * (l0.1 - l1.1) >= (l1.0 - l0.0) * (line.1 - l0.1) {
                self.lines.pop_front();
            } else {
                break;
            }
        }
        self.lines.push_front(line);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // bring Line and LineDeque into scope
    type Dq = LineDeque<i64>;

    #[test]
    #[should_panic]
    fn test_empty_deque() {
        let mut dq = Dq::new();
        dq.query_front(0);
    }

    #[test]
    fn test_single_line() {
        let mut dq = Dq::new();
        dq.push_back((7, 3));
        // query_front / query_back both just return m*x+b
        assert_eq!(dq.query_front(0), 7); // 3*0+7
        assert_eq!(dq.query_front(5), 3 * 5 + 7);
        assert_eq!(dq.query_back(10), 3 * 10 + 7);
    }

    #[test]
    fn test_push_back_and_query_back() {
        // lines: y=5 (m=0,b=5), then y= x (m=1,b=0)
        let mut dq = Dq::new();
        dq.push_back((5, 0)).push_back((0, 1));

        // query_back expects x non-increasing
        let r1 = dq.query_back(10);
        // max(5, 1*10+0) = 10
        assert_eq!(r1, 10);

        // now x drops to 1
        let r2 = dq.query_back(1);
        // now line2 is dominated: max(5,1) = 5
        assert_eq!(r2, 5);

        // subsequent queries still return 5
        let r3 = dq.query_back(0);
        assert_eq!(r3, 5);

        // after the pop, only one line remains
        assert_eq!(dq.lines.len(), 1);
        assert_eq!(dq.lines[0].1, 0);
        assert_eq!(dq.lines[0].0, 5);
    }

    #[test]
    fn test_push_front_and_query_front() {
        // lines: y = 2x (m=2, b=0), then y = x+5 (m=1,b=5)
        // push_front requires line.1 non-increasing, so we insert m=2 first, then m=1
        let mut dq = Dq::new();
        dq.push_front((0, 2)).push_front((5, 1));

        // query_front with x non-decreasing
        let r0 = dq.query_front(0);
        // at x=0: max(0,5) = 5
        assert_eq!(r0, 5);

        let r5 = dq.query_front(5);
        // at x=5: max(2*5, 1*5+5) = max(10,10) = 10
        assert_eq!(r5, 10);

        let r10 = dq.query_front(10);
        // at x=10: max(20, 15) = 20, and the (1,5) line should have been popped
        assert_eq!(r10, 20);

        // confirm that only the (2,0) line remains once we go past x=5
        assert_eq!(dq.lines.len(), 1);
        assert_eq!(dq.lines[0].1, 2);
        assert_eq!(dq.lines[0].0, 0);
    }

    #[test]
    fn test_mixed_insert_and_query() {
        // build hull for y = m x + b with slopes [3,1,0]
        // and then query at x = [1,4,7]
        let mut dq = Dq::new();
        dq.push_back((5, 0)).push_back((0, 1)).push_back((-4, 3)); // y=3x-4

        // query_back with x non-increasing:
        // first x=7: max(5,7,17)=17
        assert_eq!(dq.query_back(7), 17);
        // x=4: max(5,4,8)=8
        assert_eq!(dq.query_back(4), 8);
        // x=1: max(5,1,-1)=5
        assert_eq!(dq.query_back(1), 5);
    }
}
