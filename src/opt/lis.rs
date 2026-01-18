pub fn lis<const MODE: u8, T: Clone + PartialOrd>(s: &[T]) -> Vec<usize> {
    if s.is_empty() {
        return Vec::new();
    };
    let n = s.len();
    let mut prev = vec![0; n];
    let mut res = Vec::with_capacity(n);
    for i in 0..n {
        let it = res.partition_point(|&(x, _)| {
            if MODE == 0 {
                x < &s[i]
            } else if MODE == 1 {
                x <= &s[i]
            } else if MODE == 2 {
                x > &s[i]
            } else {
                x >= &s[i]
            }
        });
        if it == res.len() {
            res.push((&s[i], i))
        } else {
            res[it] = (&s[i], i);
        }
        prev[i] = if it == 0 { 0 } else { res[it - 1].1 };
    }
    let mut l = res.len();
    let mut cur = res.last().unwrap().1;
    let mut ans = vec![0; l];
    while l != 0 {
        l -= 1;
        ans[l] = cur;
        cur = prev[cur]
    }
    ans
}

pub fn lis_len<const MODE: u8, T: Clone + PartialOrd>(s: &[T]) -> usize {
    if s.is_empty() {
        return 0;
    };
    let n = s.len();
    let mut res = Vec::with_capacity(n);
    for i in 0..n {
        let it = res.partition_point(|&x| {
            if MODE == 0 {
                x < &s[i]
            } else if MODE == 1 {
                x <= &s[i]
            } else if MODE == 2 {
                x > &s[i]
            } else {
                x >= &s[i]
            }
        });
        if it == res.len() {
            res.push(&s[i])
        } else {
            res[it] = &s[i];
        }
    }
    res.len()
}
