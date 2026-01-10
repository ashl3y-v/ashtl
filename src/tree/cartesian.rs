#[derive(Debug, Clone)]
pub struct CartesianTree<T> {
    pub n: usize,
    pub a: Vec<T>,
    pub range: Vec<(usize, usize)>,
    pub lch: Vec<usize>,
    pub rch: Vec<usize>,
    pub par: Vec<usize>,
    pub root: usize,
    pub is_min: bool,
}

impl<T> CartesianTree<T>
where
    T: Copy + Ord,
{
    pub fn new(a: &[T]) -> Self {
        Self::with_direction(a, true)
    }

    pub fn with_direction(a: &[T], is_min: bool) -> Self {
        let n = a.len();
        let mut range = vec![(0, 0); n];
        let mut lch = vec![usize::MAX; n];
        let mut rch = vec![usize::MAX; n];
        let mut par = vec![usize::MAX; n];
        if n == 1 {
            return CartesianTree {
                n,
                a: a.to_vec(),
                range: vec![(0, 1)],
                lch,
                rch,
                par,
                root: 0,
                is_min,
            };
        }
        let is_sm = |i: usize, j: usize| -> bool {
            if is_min {
                a[i] < a[j] || (a[i] == a[j] && i < j)
            } else {
                a[i] > a[j] || (a[i] == a[j] && i < j)
            }
        };
        let mut st: Vec<usize> = Vec::with_capacity(n);
        for i in 0..n {
            while let Some(&last) = st.last() {
                if is_sm(i, last) {
                    lch[i] = last;
                    par[last] = i;
                    st.pop();
                } else {
                    break;
                }
            }
            range[i].0 = if let Some(&last) = st.last() {
                last + 1
            } else {
                0
            };
            st.push(i);
        }
        st.clear();
        let mut root = 0;
        for i in (0..n).rev() {
            while let Some(&last) = st.last() {
                if is_sm(i, last) {
                    rch[i] = last;
                    par[last] = i;
                    st.pop();
                } else {
                    break;
                }
            }
            range[i].1 = if let Some(&last) = st.last() { last } else { n };
            st.push(i);
            if par[i] == usize::MAX {
                root = i;
            }
        }
        CartesianTree {
            n,
            a: a.to_vec(),
            range,
            lch,
            rch,
            par,
            root,
            is_min,
        }
    }

    pub fn range(&self, i: usize) -> (usize, usize, T) {
        let (l, r) = self.range[i];
        (l, r, self.a[i])
    }
}
