use rand::Rng;

/// O(d! m)
pub fn seidel(
    c: &Vec<f64>,
    mat: &Vec<Vec<f64>>,
    bounds: &Vec<(f64, f64)>,
    rng: &mut impl Rng,
) -> Option<Vec<f64>> {
    let d = c.len();
    const EPS: f64 = 1e-9;
    let eps_eq = |a: f64, b: f64| (a - b).abs() <= EPS;
    if d == 1 {
        debug_assert_eq!(c.len(), 1);
        let mut low = bounds[0].0;
        let mut high = bounds[0].1;
        for row in mat {
            let a = row[0];
            let b = row[1];
            if eps_eq(a, 0.0) {
                if b < -EPS {
                    return None;
                }
            } else if a > 0.0 {
                let limit = b / a;
                if limit < high {
                    high = limit;
                }
            } else {
                let limit = b / a;
                if limit > low {
                    low = limit;
                }
            }
        }
        if high < low - EPS {
            return None;
        } else if c[0] > 0.0 {
            return Some(vec![high]);
        } else {
            return Some(vec![low]);
        }
    } else if mat.is_empty() {
        let mut res = vec![0.0; d];
        for i in 0..d {
            if c[i] > 0.0 {
                res[i] = bounds[i].1;
            } else {
                res[i] = bounds[i].0;
            }
        }
        return Some(res);
    }
    let rmi = rng.random_range(0..mat.len());
    let a = &mat[rmi];
    let mut next_mat = Vec::with_capacity(mat.len() - 1);
    for (i, row) in mat.iter().enumerate() {
        if i != rmi {
            next_mat.push(row.clone());
        }
    }
    let v_opt = seidel(c, &next_mat, bounds, rng);
    if v_opt.is_none() {
        return None;
    }
    let v = v_opt.unwrap();
    let mut val = 0.0;
    for i in 0..d {
        val += a[i] * v[i];
    }
    if val <= a[d] + EPS {
        return Some(v);
    }
    let mut k = usize::MAX;
    let mut max_coeff = 0.0;
    for i in 0..d {
        if a[i].abs() > max_coeff {
            max_coeff = a[i].abs();
            k = i;
        }
    }
    if k == usize::MAX || max_coeff <= EPS {
        return None;
    }
    let mut bar_c = Vec::with_capacity(d - 1);
    for i in 0..d {
        if i == k {
            continue;
        }
        bar_c.push(c[i] - c[k] * a[i] / a[k]);
    }
    let mut bar_mat = Vec::with_capacity(next_mat.len() + 2);
    for row in &next_mat {
        let mut new_row = Vec::with_capacity(d);
        let ratio = row[k] / a[k];
        for i in 0..d {
            if i == k {
                continue;
            }
            new_row.push(row[i] - ratio * a[i]);
        }
        new_row.push(row[d] - ratio * a[d]);
        bar_mat.push(new_row);
    }
    let mut row_high = Vec::with_capacity(d);
    let rhs = if a[k] > 0.0 {
        a[k] * bounds[k].1 - a[d]
    } else {
        a[d] - a[k] * bounds[k].1
    };
    for i in 0..d {
        if i == k {
            continue;
        }
        if a[k] > 0.0 {
            row_high.push(-a[i]);
        } else {
            row_high.push(a[i]);
        }
    }
    row_high.push(rhs);
    bar_mat.push(row_high);
    let mut row_low = Vec::with_capacity(d);
    let rhs = if a[k] > 0.0 {
        a[d] - a[k] * bounds[k].0
    } else {
        a[k] * bounds[k].0 - a[d]
    };
    for i in 0..d {
        if i == k {
            continue;
        }
        if a[k] > 0.0 {
            row_low.push(a[i]);
        } else {
            row_low.push(-a[i]);
        }
    }
    row_low.push(rhs);
    bar_mat.push(row_low);
    let mut next_bounds = Vec::with_capacity(d - 1);
    for i in 0..d {
        if i == k {
            continue;
        }
        next_bounds.push(bounds[i]);
    }
    let v_bar_opt = seidel(&bar_c, &bar_mat, &next_bounds, rng);
    if let Some(mut v_bar) = v_bar_opt {
        let mut sum_ax = 0.0;
        let mut idx = 0;
        for i in 0..d {
            if i == k {
                continue;
            }
            sum_ax += a[i] * v_bar[idx];
            idx += 1;
        }
        let val_k = (a[d] - sum_ax) / a[k];
        v_bar.insert(k, val_k);
        return Some(v_bar);
    }
    None
}
