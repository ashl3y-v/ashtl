pub fn smawk<F>(row_size: usize, col_size: usize, mut select: F) -> Vec<usize>
where
    F: FnMut(usize, usize, usize) -> bool,
{
    fn solve<F>(row: Vec<usize>, col: &[usize], select: &mut F) -> Vec<usize>
    where
        F: FnMut(usize, usize, usize) -> bool,
    {
        let n = row.len();
        if n == 0 {
            return vec![];
        }
        let mut c2: Vec<usize> = Vec::with_capacity(n);
        for &i in col {
            while let Some(&last) = c2.last()
                && select(row[c2.len() - 1], last, i)
            {
                c2.pop();
            }
            if c2.len() < n {
                c2.push(i);
            }
        }
        let mut r2 = Vec::with_capacity(n / 2);
        for i in (1..n).step_by(2) {
            r2.push(row[i]);
        }
        let a2 = solve(r2, &c2, select);
        let mut ans = vec![0; n];
        for i in 0..a2.len() {
            ans[i * 2 + 1] = a2[i];
        }
        let mut j = 0;
        for i in (0..n).step_by(2) {
            ans[i] = c2[j];
            let end = if i + 1 == n {
                *c2.last().unwrap()
            } else {
                ans[i + 1]
            };
            while c2[j] != end {
                j += 1;
                if select(row[i], ans[i], c2[j]) {
                    ans[i] = c2[j];
                }
            }
        }
        ans
    }
    let row: Vec<usize> = (0..row_size).collect();
    let col: Vec<usize> = (0..col_size).collect();
    solve(row, &col, &mut select)
}
