pub fn prufer(adj: &Vec<Vec<usize>>) -> Vec<usize> {
    let n = adj.len();
    if n < 2 {
        return vec![];
    }
    fn dfs(v: usize, adj: &Vec<Vec<usize>>, p: &mut Vec<usize>) {
        for &u in &adj[v] {
            if p[v] != u {
                p[u] = v;
                dfs(u, adj, p);
            }
        }
    }
    let mut p: Vec<usize> = vec![usize::MAX; n];
    dfs(n - 1, adj, &mut p);
    let mut degree: Vec<usize> = vec![0; n];
    let mut ptr = usize::MAX;
    for i in 0..n {
        degree[i] = adj[i].len();
        if ptr == usize::MAX && degree[i] == 1 {
            ptr = i;
        }
    }
    let mut code = vec![0; n - 2];
    let mut leaf = ptr;
    for i in 0..n - 2 {
        let nxt = p[leaf];
        code[i] = nxt;
        degree[nxt] -= 1;
        if degree[nxt] == 1 && nxt < ptr {
            leaf = nxt;
        } else {
            ptr += 1;
            while ptr < n && degree[ptr] != 1 {
                ptr += 1;
            }
            leaf = ptr;
        }
    }
    code
}

pub fn prufer_inv(code: &[usize]) -> Vec<(usize, usize)> {
    let n = code.len() + 2;
    let mut degree = vec![1; n];
    for &i in code {
        degree[i] += 1;
    }
    let mut ptr = 0;
    while ptr < n && degree[ptr] != 1 {
        ptr += 1;
    }
    let mut leaf = ptr;
    let mut edges = Vec::with_capacity(n - 1);
    for &v in code {
        edges.push((leaf, v));
        degree[v] -= 1;
        if degree[v] == 1 && v < ptr {
            leaf = v;
        } else {
            ptr += 1;
            while ptr < n && degree[ptr] != 1 {
                ptr += 1;
            }
            leaf = ptr;
        }
    }
    edges.push((leaf, n - 1));
    edges
}
