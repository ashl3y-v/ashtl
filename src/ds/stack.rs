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
