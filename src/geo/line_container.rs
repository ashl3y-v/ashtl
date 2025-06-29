use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::{Add, BitXor, Div, Mul, Rem, Sub};

#[derive(Debug, Clone)]
struct Line<T: Copy> {
    m: T,
    b: T,
    p: Cell<T>,
    query: bool,
}

impl<T> Line<T>
where
    T: Copy
        + Default
        + PartialEq
        + PartialOrd
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitXor<Output = T>
        + From<bool>,
{
    fn eval(&self, x: T) -> T {
        self.m * x + self.b
    }

    fn div_floor(a: T, b: T) -> T {
        a / b - T::from((a ^ b) < T::default() && a % b != T::default())
    }

    fn intersect(&self, other: &Line<T>) -> T {
        Self::div_floor(other.b - self.b, self.m - other.m)
    }
}

impl<T: Copy + PartialEq> PartialEq for Line<T> {
    fn eq(&self, other: &Self) -> bool {
        self.m == other.m
    }
}

impl<T: Copy + PartialEq> Eq for Line<T> {}

impl<T: Copy + Ord> Ord for Line<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.query || other.query {
            self.p.cmp(&other.p)
        } else {
            self.m.cmp(&other.m)
        }
    }
}

impl<T: Copy + PartialOrd> PartialOrd for Line<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.query || other.query {
            self.p.partial_cmp(&other.p)
        } else {
            self.m.partial_cmp(&other.m)
        }
    }
}

#[derive(Debug)]
pub struct LineContainer<T: Copy> {
    hull: BTreeSet<Line<T>>,
}

impl<T> LineContainer<T>
where
    T: Copy
        + Default
        + Ord
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + BitXor<Output = T>
        + From<bool>,
{
    pub fn new() -> Self {
        LineContainer {
            hull: BTreeSet::new(),
        }
    }

    pub fn insert(&mut self, m: T, b: T, max: T) -> &mut Self {
        let line = Line {
            m,
            b,
            p: Cell::new(max),
            query: false,
        };
        if let Some(same_m) = self.hull.take(&line) {
            if line.b <= same_m.b {
                self.hull.insert(same_m);
                return self;
            }
        }
        let mut to_remove = vec![];
        let mut pref = self.hull.range(..&line).rev();
        let mut suf = self.hull.range(&line..);
        let nr = suf.next();
        let nl = pref.next();
        if let Some(mut nr) = nr {
            if let Some(nl) = nl {
                if (nr.b - line.b) * (nl.m - line.m) <= (line.b - nl.b) * (line.m - nr.m) {
                    return self;
                }
            }
            let mut line_p = line.intersect(nr);
            while let Some(nnr) = suf.next() {
                if nr.p.get() <= line_p {
                    to_remove.push(nr.clone());
                } else {
                    break;
                }
                nr = nnr;
                line_p = line.intersect(nr);
            }
            line.p.set(line_p);
        }
        if let Some(mut nl) = nl {
            let mut nl_p = nl.intersect(&line);
            while let Some(nnl) = pref.next() {
                if nl_p <= nnl.p.get() {
                    to_remove.push(nl.clone());
                } else {
                    break;
                }
                nl = nnl;
                nl_p = nl.intersect(&line);
            }
            nl.p.set(nl_p);
        }
        for l in to_remove {
            self.hull.remove(&l);
        }
        self.hull.insert(line);
        self
    }

    pub fn query(&self, x: T) -> T {
        let q = Line {
            m: T::default(),
            b: T::default(),
            p: Cell::new(x),
            query: true,
        };
        self.hull
            .range(&q..)
            .next()
            .map(|l| l.eval(x))
            .unwrap_or_default()
    }

    pub fn is_empty(&self) -> bool {
        self.hull.is_empty()
    }

    pub fn len(&self) -> usize {
        self.hull.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_container() {
        let cht = LineContainer::new();
        assert_eq!(cht.query(0), 0);
        assert!(cht.is_empty());
        assert_eq!(cht.len(), 0);
    }

    #[test]
    fn test_single_line() {
        let mut cht = LineContainer::new();
        cht.insert(2, 5, i32::MAX); // y = 2x + 5

        assert!(!cht.is_empty());
        assert_eq!(cht.len(), 1);
        assert_eq!(cht.query(0), 5);
        assert_eq!(cht.query(1), 7);
        assert_eq!(cht.query(-1), 3);
    }

    #[test]
    fn test_two_non_intersecting_lines() {
        let mut cht = LineContainer::new();
        cht.insert(1, 0, i32::MAX); // y = x
        cht.insert(2, -5, i32::MAX); // y = 2x - 5

        // At x = 0: line1 = 0, line2 = -5, max = 0
        assert_eq!(cht.query(0), 0);

        // At x = 10: line1 = 10, line2 = 15, max = 15
        assert_eq!(cht.query(10), 15);

        // At x = -10: line1 = -10, line2 = -25, max = -10
        assert_eq!(cht.query(-10), -10);
    }

    #[test]
    fn test_parallel_lines() {
        let mut cht = LineContainer::new();
        cht.insert(1, 5, i32::MAX); // y = x + 5
        cht.insert(1, 3, i32::MAX); // y = x + 3 (should be ignored as it's worse)

        assert_eq!(cht.len(), 1);
        assert_eq!(cht.query(0), 5);
        assert_eq!(cht.query(10), 15);

        // Add a better parallel line
        cht.insert(1, 7, i32::MAX); // y = x + 7
        assert_eq!(cht.len(), 1);
        assert_eq!(cht.query(0), 7);
        assert_eq!(cht.query(10), 17);
    }

    #[test]
    fn test_convex_hull_maintenance() {
        let mut cht = LineContainer::new();

        // Add lines that form a proper convex hull
        cht.insert(-1, 10, i32::MAX); // y = -x + 10
        cht.insert(0, 5, i32::MAX); // y = 5
        cht.insert(1, 0, i32::MAX); // y = x

        // Test queries at different points
        assert_eq!(cht.query(-10), 20); // -x + 10 is best
        assert_eq!(cht.query(0), 10); // max(-0 + 10, 5, 0) = 10
        assert_eq!(cht.query(10), 10); // x is best
    }

    #[test]
    fn test_decreasing_slopes() {
        let mut cht = LineContainer::new();

        // Add lines with decreasing slopes (typical for CHT)
        cht.insert(5, 0, i32::MAX); // y = 5x
        cht.insert(3, 10, i32::MAX); // y = 3x + 10
        cht.insert(1, 15, i32::MAX); // y = x + 15

        // Test various query points
        assert_eq!(cht.query(-5), 10); // 3x + 10 should be best at x = -5
        assert_eq!(cht.query(0), 15); // x + 15 should be best at x = 0
        assert_eq!(cht.query(10), 50); // 5x should be best at x = 10
    }

    #[test]
    fn test_negative_coordinates() {
        let mut cht = LineContainer::new();
        cht.insert(-2, -3, i32::MAX); // y = -2x - 3
        cht.insert(-1, 5, i32::MAX); // y = -x + 5

        assert_eq!(cht.query(-10), 17); // -2*(-10) - 3 = 17
        assert_eq!(cht.query(0), 5); // max(-3, 5) = 5
        assert_eq!(cht.query(10), -5); // max(-23, -5) = -5
    }

    #[test]
    fn test_large_numbers() {
        let mut cht = LineContainer::<i64>::new();
        cht.insert(1000000, 2000000, i64::MAX);
        cht.insert(500000, 3000000, i64::MAX);

        let result1 = cht.query(1000);
        let result2 = cht.query(5000);

        // Verify that calculations don't overflow and maintain correctness
        assert_eq!(
            result1,
            std::cmp::max(1000000 * 1000 + 2000000, 500000 * 1000 + 3000000)
        );
        assert_eq!(
            result2,
            std::cmp::max(1000000 * 5000 + 2000000, 500000 * 5000 + 3000000)
        );
    }

    #[test]
    fn test_identical_lines() {
        let mut cht = LineContainer::new();
        cht.insert(2, 3, i32::MAX);
        cht.insert(2, 3, i32::MAX); // Identical line

        assert_eq!(cht.len(), 1); // Should still have only one line
        assert_eq!(cht.query(5), 13);
    }
}
