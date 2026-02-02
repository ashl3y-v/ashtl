use std::ops::{Add, Sub};

use crate::ds::bit_vec::BitVec;

pub struct TreeLaplacian {
    v: usize,
    adj: Vec<Vec<(usize, usize)>>,
    edge_count: usize,
}

impl TreeLaplacian {
    pub fn new(n: usize) -> Self {
        Self {
            v: n,
            adj: vec![vec![]; n],
            edge_count: 0,
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize) {
        let e = self.edge_count;
        self.adj[u].push((v, e));
        self.adj[v].push((u, e));
        self.edge_count += 1;
    }

    pub fn calc<T>(&self, b: &[T]) -> Option<Vec<T>>
    where
        T: Copy + Default + Add<Output = T> + Sub<Output = T> + PartialEq,
    {
        let mut visited = BitVec::new(self.v, false);
        let mut edge_solutions = vec![T::default(); self.edge_count];
        for i in 0..self.v {
            if !visited[i] {
                let bal = self.dfs(i, &mut visited, b, &mut edge_solutions);
                if bal != T::default() {
                    return None;
                }
            }
        }
        Some(edge_solutions)
    }

    fn dfs<T>(&self, u: usize, visited: &mut BitVec, b: &[T], edge_solutions: &mut [T]) -> T
    where
        T: Default + Copy + Add<Output = T> + Sub<Output = T>,
    {
        visited.set(u, true);
        let mut sum = b[u];
        for &(v, eid) in &self.adj[u] {
            if visited[v] {
                continue;
            }
            let ch_sum = self.dfs(v, visited, b, edge_solutions);
            edge_solutions[eid] = ch_sum;
            sum = sum + ch_sum;
        }
        sum
    }
}
