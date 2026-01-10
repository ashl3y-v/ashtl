// TODO: suffix array
// https://maspypy.github.io/library/string/suffix_array.hpp
// https://judge.yosupo.jp/submission/296441

pub mod sa {
    fn get_types(s: &[usize], ty: &mut [u8]) {
        let n = s.len() - 1;
        ty[n] = 1;
        for i in (0..n).rev() {
            if s[i] < s[i + 1] {
                ty[i] = 1;
            } else if s[i] > s[i + 1] {
                ty[i] = 0;
            } else {
                ty[i] = ty[i + 1];
            }
        }
    }

    fn lms_equal(s: &[usize], ty: &[u8], mut x: usize, mut y: usize) -> bool {
        if s[x] != s[y] {
            return false;
        }
        loop {
            x += 1;
            y += 1;
            if s[x] != s[y] || ty[x] != ty[y] {
                return false;
            }
            if ty[x] == 2 {
                return true;
            }
        }
    }

    fn induced_sort(s: &[usize], sa: &mut [usize], ty: &[u8], lms: &[usize], m: usize) {
        let n = s.len();
        let mut cnt = vec![0; m + 1];
        for &x in s {
            cnt[x] += 1;
        }
        let mut bucket_ends = vec![0; m + 1];
        let mut bkt = vec![0; m + 1];
        let mut sum = 0;
        for i in 0..=m {
            bkt[i] = sum;
            sum += cnt[i];
            bucket_ends[i] = sum;
        }
        sa.fill(0);
        let mut bkt_p = bucket_ends.clone();
        for &idx in lms.iter().rev() {
            let ch = s[idx];
            bkt_p[ch] -= 1;
            sa[bkt_p[ch]] = idx;
        }
        for i in 0..n {
            let idx = sa[i];
            if idx > 0 {
                let prev = idx - 1;
                if ty[prev] == 0 {
                    let ch = s[prev];
                    sa[bkt[ch]] = prev;
                    bkt[ch] += 1;
                }
            }
        }
        let mut bkt = bucket_ends;
        for i in (0..n).rev() {
            let idx = sa[i];
            if idx > 0 {
                let prev = idx - 1;
                if ty[prev] >= 1 {
                    let ch = s[prev];
                    bkt[ch] -= 1;
                    sa[bkt[ch]] = prev;
                }
            }
        }
    }

    pub fn sa_is(s: &[usize], sa: &mut [usize], m: usize) {
        let n = s.len();
        let mut ty = vec![0u8; n];
        get_types(s, &mut ty);
        let mut lms = Vec::with_capacity(n / 2);
        for i in 1..n {
            if ty[i] == 1 && ty[i - 1] == 0 {
                ty[i] = 2;
                lms.push(i);
            }
        }
        induced_sort(s, sa, &ty, &lms, m);
        let mut sorted_lms = Vec::with_capacity(lms.len());
        for &idx in sa.iter() {
            if ty[idx] == 2 {
                sorted_lms.push(idx);
            }
        }
        let mut reduced_s = vec![0; lms.len()];
        let mut map_pos = vec![0; n];
        if !sorted_lms.is_empty() {
            reduced_s[0] = 0;
            for i in 0..sorted_lms.len() {
                let curr = sorted_lms[i];
                map_pos[curr] = i;
            }
        }
        let mut actual_reduced_s = Vec::with_capacity(lms.len());
        let mut current_name = 0;
        let mut names = vec![0; n];
        if !sorted_lms.is_empty() {
            names[sorted_lms[0]] = 0;
            for i in 1..sorted_lms.len() {
                let prev = sorted_lms[i - 1];
                let curr = sorted_lms[i];
                if !lms_equal(s, &ty, prev, curr) {
                    current_name += 1;
                }
                names[curr] = current_name;
            }
        }
        for &idx in &lms {
            actual_reduced_s.push(names[idx]);
        }
        let mut reduced_sa = vec![0; actual_reduced_s.len()];
        if current_name + 1 < lms.len() {
            sa_is(&actual_reduced_s, &mut reduced_sa, current_name);
        } else {
            for (i, &x) in actual_reduced_s.iter().enumerate() {
                reduced_sa[x] = i;
            }
        }
        let mut lms_remapped = Vec::with_capacity(lms.len());
        for &idx in &reduced_sa {
            lms_remapped.push(lms[idx]);
        }
        induced_sort(s, sa, &ty, &lms_remapped, m);
    }

    pub fn suffix_sort(raw_s: &[u8]) -> Vec<usize> {
        let n = raw_s.len();
        let mut s = Vec::with_capacity(n + 1);
        let min_val = *raw_s.iter().min().unwrap_or(&0);
        let max_val = *raw_s.iter().max().unwrap_or(&0);
        for &c in raw_s {
            s.push((c - min_val + 1) as usize);
        }
        s.push(0);
        let m = (max_val - min_val + 2) as usize;
        let mut sa = vec![0; n + 1];
        sa_is(&s, &mut sa, m);
        sa[1..].into()
    }
}

// TODO: kasai's algorithm
// https://codeforces.com/blog/entry/12796?#comment-175287
// https://judge.yosupo.jp/submission/52302

// TODO: suffix tree
// https://maspypy.github.io/library/string/suffix_tree.hpp

// TODO: suffix automaton
// https://maspypy.github.io/library/string/suffix_automaton.hpp
