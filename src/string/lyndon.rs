/// O(n)
pub fn duval(s: &str) -> Vec<usize> {
    let n = s.len();
    let s: Vec<char> = s.chars().collect();
    let mut fac = Vec::new();
    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        let mut k = i;
        while j < n && s[k] <= s[j] {
            if s[k] < s[j] {
                k = i;
            } else {
                k += 1;
            }
            j += 1;
        }
        while i <= k {
            fac.push(i);
            i += j - k;
        }
    }
    fac.push(n);
    fac
}

/// O(n)
pub fn min_cyclic_shift(s: &str) -> String {
    let s: Vec<char> = s.chars().collect();
    let n = s.len();
    let doub: Vec<char> = s.iter().chain(s.iter()).copied().collect();
    let mut i = 0;
    let mut ans = 0;
    while i < n {
        ans = i;
        let mut j = i + 1;
        let mut k = i;
        while j < doub.len() && doub[k] <= doub[j] {
            if doub[k] < doub[j] {
                k = i;
            } else {
                k += 1;
            }
            j += 1;
        }
        while i <= k {
            i += j - k;
        }
    }
    doub[ans..ans + n].iter().collect()
}
