use std::cell::RefCell;

use crate::ds::dsu::DSU;
use crate::range::seg_tree::SegTree;

pub fn topo_sort(adj: &[Vec<usize>]) -> Vec<usize> {
    let n = adj.len();
    let mut q = Vec::with_capacity(n);
    let mut indeg = vec![0; n];
    adj.iter().flatten().for_each(|&x| indeg[x] += 1);
    (0..n).filter(|&i| indeg[i] == 0).for_each(|i| q.push(i));
    let mut j = 0;
    while j < q.len() {
        for &x in &adj[q[j]] {
            indeg[x] -= 1;
            if indeg[x] == 0 {
                q.push(x);
            }
        }
        j += 1;
    }
    q
}

/// O(n log n)
pub fn optimal_product_on_tree<T, Op, Comp>(
    par: &[usize],
    data: Vec<T>,
    op: Op,
    cmp: Comp,
) -> (Vec<usize>, T)
where
    T: Copy,
    Op: Fn(T, T) -> T,
    Comp: Fn(T, T) -> bool,
{
    let n = data.len();
    let root = par
        .iter()
        .position(|&p| p == usize::MAX)
        .expect("Tree must have a root with parent usize::MAX");
    let mut dsu = DSU::new(n);
    let mut head: Vec<usize> = (0..n).collect();
    let mut tail: Vec<usize> = (0..n).collect();
    let mut nxt: Vec<usize> = vec![usize::MAX; n];
    let data_cell = RefCell::new(data);
    let mut leaves = vec![usize::MAX; n];
    for i in 0..n {
        if i != root {
            leaves[i] = i;
        }
    }
    let merge_logic = |t: &mut [usize], i: usize, l: usize, r: usize, d: &Vec<T>| {
        if l == usize::MAX {
            t[i] = r;
        } else if r == usize::MAX {
            t[i] = l;
        } else {
            if cmp(d[l], d[r]) {
                t[i] = l;
            } else {
                t[i] = r;
            }
        }
    };
    let init = |i: usize, t: &mut [usize]| {
        merge_logic(t, i, t[2 * i], t[2 * i + 1], &data_cell.borrow());
    };
    let pull = |i: usize, t: &mut [usize]| {
        merge_logic(t, i, t[2 * i], t[2 * i + 1], &data_cell.borrow());
    };
    let mut seg = SegTree::new(leaves, init, pull);
    for _ in 0..(n - 1) {
        let v = seg.t[1];
        if v == usize::MAX {
            break;
        }
        let u_orig = par[head[v]];
        let p = dsu.find(u_orig);
        {
            let mut d = data_cell.borrow_mut();
            d[p] = op(d[p], d[v]);
        }
        nxt[tail[p]] = head[v];
        tail[p] = tail[v];
        let (new_root, _) = dsu.union(p, v);
        if new_root != p {
            head[new_root] = head[p];
            tail[new_root] = tail[p];
            {
                let mut d = data_cell.borrow_mut();
                d[new_root] = d[p];
            }
        }
        seg.set(v, usize::MAX);
        if new_root != dsu.find(root) {
            seg.set(new_root, new_root);
        } else {
            seg.set(new_root, usize::MAX);
        }
    }
    let final_root = dsu.find(root);
    let final_data = data_cell.borrow()[final_root];
    let mut order = Vec::with_capacity(n);
    let mut curr = head[final_root];
    while curr != usize::MAX {
        order.push(curr);
        curr = nxt[curr];
    }
    (order, final_data)
}
