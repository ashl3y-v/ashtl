use super::point::Point;
use crate::ds::bit_vec::BitVec;
use std::ops::{Add, Div, Mul, Sub, SubAssign};

pub fn center<T>(mut pts: Vec<Point<T>>) -> (Vec<Point<T>>, Point<T>)
where
    T: Copy
        + Default
        + PartialOrd
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + SubAssign,
{
    let mut n = pts.len();
    let mut i = 0;
    for j in 1..n {
        if pts[j] < pts[i] {
            i = j;
        }
    }
    pts.rotate_left(i + 1);
    let t = pts.pop().unwrap();
    n -= 1;
    for i in 0..n {
        pts[i] -= t;
    }
    (pts, t)
}

// TODO: check if convex polygon contains point
// https://cp-algorithms.com/geometry/point-in-convex-polygon.html

/// O(log n)
/// Assumes points are in counterclockwise order starting at (0,0) (omitted)
pub fn contains_point<T>(pts: &[Point<T>], pt: Point<T>) -> bool
where
    T: Clone + Default + PartialOrd + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    unimplemented!()
}

/// O(n)
pub fn antipodal<T>(pts: &[Point<T>]) -> Vec<(usize, usize)>
where
    T: Clone + Default + PartialOrd + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    let m = pts.len();
    if m == 1 {
        return Vec::new();
    } else if m == 2 {
        return vec![(0, 1)];
    }
    let mut ans = Vec::new();
    let mut seen = BitVec::new(m, false);
    let mut j = 1;
    for i in 0..m {
        let ni = (i + 1) % m;
        let mut nj = (j + 1) % m;
        let v = pts[ni].clone() - pts[i].clone();
        while nj != i && v.cross(&(pts[nj].clone() - pts[j].clone())) > T::default() {
            j = (j + 1) % m;
            nj = (j + 1) % m;
        }
        if seen[i] {
            continue;
        }
        seen.set(i, true);
        ans.push((i, j));
        ans.push((ni, j));
        if v.cross(&(pts[nj].clone() - pts[j].clone())) == T::default() {
            ans.push((i, nj));
            ans.push((ni, nj));
            seen.set(j, true);
        }
    }
    ans
}

/// O(n)
pub fn diameter<T>(pts: &[Point<T>]) -> Option<(T, (usize, usize))>
where
    T: Clone + Default + PartialOrd + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    let m = pts.len();
    if m == 1 {
        return Some((T::default(), (0, 0)));
    }
    let mut ans = {
        let d = pts[1].clone() - pts[0].clone();
        (d.dot(&d), (0, 1))
    };
    if m == 2 {
        return Some(ans);
    }
    let mut j = 1;
    for i in 0..m {
        let ni = (i + 1) % m;
        let mut nj = (j + 1) % m;
        while nj != i
            && (pts[ni].clone() - pts[i].clone()).cross(&(pts[nj].clone() - pts[j].clone()))
                > T::default()
        {
            j = (j + 1) % m;
            nj = (j + 1) % m;
        }
        let diff = pts[i].clone() - pts[j].clone();
        let d2 = diff.dot(&diff);
        if d2 > ans.0 {
            ans = (d2, (i, j));
        }
    }
    Some(ans)
}

/// O(n)
/// Note returns squared width as a rational.
pub fn width<T>(pts: &[Point<T>]) -> ((T, T), (usize, usize))
where
    T: Copy
        + Default
        + PartialOrd
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>,
{
    let m = pts.len();
    let mut ans = (None, (0, 0));
    let mut seen = BitVec::new(m, false);
    let mut j = 1;
    for i in 0..m {
        let ni = (i + 1) % m;
        let mut nj = (j + 1) % m;
        let v = pts[ni].clone() - pts[i].clone();
        while nj != i && v.cross(&(pts[nj].clone() - pts[j].clone())) > T::default() {
            j = (j + 1) % m;
            nj = (j + 1) % m;
        }
        if seen[i] {
            continue;
        }
        let mut chmin = |num: T, den: T, idx: (usize, usize)| {
            let is_better = match ans.0 {
                None => true,
                Some((best_num, best_den)) => num * best_den < best_num * den,
            };
            if is_better {
                ans = (Some((num, den)), idx);
            }
        };
        if v.cross(&(pts[nj].clone() - pts[j].clone())) == T::default() {
            let edge_sq = v.dot(&v);
            let cross = v.cross(&(pts[j] - pts[i]));
            chmin(cross * cross, edge_sq, (i, j));
            seen.set(j, true);
        } else {
            let edge_sq = v.dot(&v);
            let vec_to_j = pts[j] - pts[i];
            let proj = vec_to_j.dot(&v);
            if proj <= T::default() {
                chmin(vec_to_j.dot(&vec_to_j) * edge_sq, edge_sq, (i, j));
            } else if proj >= edge_sq {
                let vec_to_j_ni = pts[j] - pts[ni];
                chmin(vec_to_j_ni.dot(&vec_to_j_ni) * edge_sq, edge_sq, (i, j));
            } else {
                chmin(v.cross(&vec_to_j) * v.cross(&vec_to_j), edge_sq, (i, j));
            }
        }
    }
    (ans.0.unwrap(), ans.1)
}
