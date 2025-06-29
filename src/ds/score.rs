use std::cmp::Ordering;

#[derive(Copy, Clone, Debug)]
pub struct MinScore<T, K>(pub T, pub K);

impl<T: PartialOrd, K> PartialEq for MinScore<T, K> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<T: PartialOrd, K> Eq for MinScore<T, K> {}

impl<T: PartialOrd, K> PartialOrd for MinScore<T, K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: PartialOrd, K> Ord for MinScore<T, K> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let a = &self.0;
        let b = &other.0;
        if a == b {
            Ordering::Equal
        } else if a < b {
            Ordering::Greater
        } else if a > b {
            Ordering::Less
        } else if a != a && b != b {
            Ordering::Equal
        } else if a != a {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MaxScore<T, K>(pub T, pub K);

impl<T: PartialOrd, K> PartialEq for MaxScore<T, K> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<T: PartialOrd, K> Eq for MaxScore<T, K> {}

impl<T: PartialOrd, K> PartialOrd for MaxScore<T, K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: PartialOrd, K> Ord for MaxScore<T, K> {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = &self.0;
        let b = &other.0;
        if a == b {
            Ordering::Equal
        } else if a < b {
            Ordering::Less
        } else if a > b {
            Ordering::Greater
        } else if a != a && b != b {
            Ordering::Equal
        } else if a != a {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}
