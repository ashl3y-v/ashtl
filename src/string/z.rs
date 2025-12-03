// TODO: online z algorithm
// https://maspypy.github.io/library/string/online_z_algorithm.hpp

pub fn z(s: &str) -> Vec<usize> {
    let n = s.len();
    let s = s.chars().collect::<Vec<_>>();
    let mut z = vec![0; n];
    let (mut l, mut r) = (0, 0);
    for i in 1..n {
        if i < r {
            z[i] = (r - i).min(z[i - l]);
        }
        while i + z[i] < n && s[z[i]] == s[i + z[i]] {
            z[i] += 1;
        }
        if i + z[i] > r {
            l = i;
            r = i + z[i];
        }
    }
    z
}

pub fn z_occurrences(s: &str, t: &str) -> impl Iterator<Item = usize> {
    let (ns, nt) = (s.len(), t.len());
    let n = ns + 1 + nt;
    let s = s.chars().collect::<Vec<_>>();
    let t = t.chars().collect::<Vec<_>>();
    let get = |i| if i < ns { s[i] } else { t[i - 1 - ns] };
    let mut z = vec![0; n];
    let (mut l, mut r) = (0, 0);
    for i in 1..n {
        if i < r {
            z[i] = (r - i).min(z[i - l]);
        }
        while i + z[i] < n && z[i] != ns && i + z[i] != ns && get(z[i]) == get(i + z[i]) {
            z[i] += 1;
        }
        if i + z[i] > r {
            l = i;
            r = i + z[i];
        }
    }
    (0..nt).filter(move |&i| z[i + ns + 1] == ns)
}
