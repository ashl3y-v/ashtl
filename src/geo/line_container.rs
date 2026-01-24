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
