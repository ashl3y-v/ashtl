// TODO: Hu-Tucker proof https://epubs.siam.org/doi/epdf/10.1137/0125012

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::ds::heap::PairingHeap;

/// O(n log n)
pub fn hu_tucker(w: &[i64]) -> i64 {
    let n = w.len();
    if n <= 1 {
        return 0;
    }
    const INF: i64 = i64::MAX / 2;
    let mut heaps: Vec<PairingHeap<i64>> = (0..n - 1).map(|_| PairingHeap::new()).collect();
    let mut left: Vec<i32> = (0..n as i32).map(|i| i - 1).collect();
    let mut right: Vec<i32> = (0..n as i32).map(|i| i + 1).collect();
    let mut cs: Vec<i64> = (0..n - 1).map(|i| w[i] + w[i + 1]).collect();
    let mut w: Vec<i64> = w.to_vec();
    let mut pq: BinaryHeap<Reverse<(i64, usize)>> = BinaryHeap::new();
    for i in 0..n - 1 {
        pq.push(Reverse((cs[i], i)));
    }
    let mut ret = 0i64;
    for _ in 0..n - 1 {
        let (c, mut i) = loop {
            let Reverse((c, i)) = pq.pop().unwrap();
            if right[i] != -1 && cs[i] == c {
                break (c, i);
            }
        };
        let ri = right[i] as usize;
        let (merge_l, merge_r) = if w[i] + w[ri] == c {
            (true, true)
        } else {
            let top = heaps[i].pop().unwrap();
            if w[i] + top == c {
                (true, false)
            } else if top + w[ri] == c {
                (false, true)
            } else {
                heaps[i].pop();
                (false, false)
            }
        };
        ret += c;
        heaps[i].push(c);
        if merge_l {
            w[i] = INF;
        }
        if merge_r {
            w[ri] = INF;
        }
        if merge_l && i > 0 {
            let j = left[i] as usize;
            let heap_i = std::mem::replace(&mut heaps[i], PairingHeap::new());
            heaps[j].meld(heap_i);
            right[j] = right[i];
            right[i] = -1;
            left[right[j] as usize] = j as i32;
            i = j;
        }
        let ri = right[i] as usize;
        if merge_r && ri < n - 1 {
            let heap_ri = std::mem::replace(&mut heaps[ri], PairingHeap::new());
            heaps[i].meld(heap_ri);
            right[i] = right[ri];
            right[ri] = -1;
            left[right[i] as usize] = i as i32;
        }
        let ri = right[i] as usize;
        cs[i] = w[i] + w[ri];
        if !heaps[i].is_empty() {
            let top = heaps[i].pop().unwrap();
            cs[i] = cs[i].min(w[i].min(w[ri]) + top);
            if let Some(second) = heaps[i].top() {
                cs[i] = cs[i].min(top + second);
            }
            heaps[i].push(top);
        }
        pq.push(Reverse((cs[i], i)));
    }
    ret
}
