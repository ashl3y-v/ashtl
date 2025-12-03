use std::collections::VecDeque;

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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScanStack<T, F: FnMut(&T, &T) -> T> {
    pub vs: Vec<T>,
    pub ss: Vec<T>,
    pub f: F,
}

impl<T, F: FnMut(&T, &T) -> T> ScanStack<T, F> {
    pub fn new(f: F) -> Self {
        Self {
            vs: Vec::new(),
            ss: Vec::new(),
            f,
        }
    }

    pub fn with_capacity(n: usize, f: F) -> Self {
        Self {
            vs: Vec::with_capacity(n),
            ss: Vec::with_capacity(n - 1),
            f,
        }
    }

    pub fn push(&mut self, value: T) -> &mut Self {
        if let Some(m) = self.ss.last() {
            let m = (self.f)(m, &value);
            self.vs.push(value);
            self.ss.push(m);
        } else if let Some(v) = self.vs.last() {
            let m = (self.f)(v, &value);
            self.vs.push(value);
            self.ss.push(m);
        } else {
            self.vs.push(value);
        }
        self
    }

    pub fn pop(&mut self) -> Option<T> {
        self.ss.pop();
        self.vs.pop()
    }

    pub fn last(&self) -> Option<&T> {
        self.vs.last()
    }

    pub fn query(&self) -> Option<&T> {
        if let Some(m) = self.ss.last() {
            Some(m)
        } else if let Some(v) = self.vs.last() {
            Some(v)
        } else {
            None
        }
    }
}

// https://codeforces.com/blog/entry/122003
/// Amortized O(1) if f is O(1)
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScanDeque<T, F: FnMut(&T, &T) -> T> {
    pub l: ScanStack<T, F>,
    pub r: ScanStack<T, F>,
    pub t: ScanStack<T, F>,
}

impl<T: Clone, F: Clone + FnMut(&T, &T) -> T> ScanDeque<T, F> {
    pub fn new(f: F) -> Self {
        Self {
            l: ScanStack::new(f.clone()),
            r: ScanStack::new(f.clone()),
            t: ScanStack::new(f),
        }
    }

    pub fn with_capacity(n: usize, f: F) -> Self {
        Self {
            l: ScanStack::with_capacity(n, f.clone()),
            r: ScanStack::with_capacity(n, f.clone()),
            t: ScanStack::with_capacity(n, f),
        }
    }

    pub fn rebalance(&mut self) {
        let mut fl = false;
        if self.r.vs.is_empty() {
            fl = true;
            self.swap();
        }
        let sz = self.r.vs.len() >> 1;
        for _ in 0..sz {
            self.t.push(self.r.pop().unwrap());
        }
        while !self.r.vs.is_empty() {
            self.l.push(self.r.pop().unwrap());
        }
        while !self.t.vs.is_empty() {
            self.r.push(self.t.pop().unwrap());
        }
        if fl {
            self.swap();
        }
    }

    pub fn query(&mut self) -> Option<T> {
        if self.l.vs.is_empty() {
            self.r.query().cloned()
        } else if self.r.vs.is_empty() {
            self.l.query().cloned()
        } else {
            Some((self.t.f)(self.l.query().unwrap(), self.r.query().unwrap()))
        }
    }

    pub fn is_empty(&self) -> bool {
        self.l.vs.is_empty() && self.r.vs.is_empty()
    }

    pub fn len(&self) -> usize {
        self.l.vs.len() + self.r.vs.len()
    }

    pub fn push_front(&mut self, value: T) -> &mut Self {
        self.l.push(value);
        self
    }

    pub fn push_back(&mut self, value: T) -> &mut Self {
        self.r.push(value);
        self
    }

    pub fn pop_front(&mut self) -> Option<T> {
        if self.l.vs.is_empty() {
            self.rebalance();
        }
        self.l.pop()
    }

    pub fn pop_back(&mut self) -> Option<T> {
        if self.r.vs.is_empty() {
            self.rebalance();
        }
        self.r.pop()
    }

    pub fn front(&mut self) -> Option<&T> {
        if self.l.vs.is_empty() {
            self.rebalance();
        }
        self.l.last()
    }

    pub fn back(&mut self) -> Option<&T> {
        if self.r.vs.is_empty() {
            self.rebalance();
        }
        self.r.last()
    }

    pub fn swap(&mut self) -> &mut Self {
        std::mem::swap(&mut self.l, &mut self.r);
        self
    }
}
