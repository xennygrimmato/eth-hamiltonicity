//! Regular (multi)graphs as flat adjacency lists, and generators: random d-regular, cycles, tori,
//! named cubic graphs. Cayley graphs live in `groups`.

use rand::{rngs::SmallRng, seq::SliceRandom, Rng, SeedableRng};
use std::collections::{HashSet, VecDeque};

/// A d-regular graph; the neighbours of v are adj[v*d .. (v+1)*d]. Every undirected edge appears
/// twice (once from each end). Loops would appear twice at the same vertex; generators avoid them.
#[derive(Clone, Debug)]
pub struct Graph {
    pub n: usize,
    pub d: usize,
    pub adj: Vec<u32>,
    pub name: String,
}

impl Graph {
    pub fn from_edges(n: usize, edges: &[(usize, usize)], name: &str) -> Graph {
        let mut lists = vec![vec![]; n];
        for &(u, v) in edges {
            lists[u].push(v as u32);
            lists[v].push(u as u32);
        }
        let d = lists[0].len();
        assert!(lists.iter().all(|l| l.len() == d), "graph {name} is not regular");
        Graph { n, d, adj: lists.concat(), name: name.to_string() }
    }

    #[inline]
    pub fn nb(&self, v: usize) -> &[u32] {
        &self.adj[v * self.d..(v + 1) * self.d]
    }

    /// Undirected edges u <= v, with multiplicity.
    pub fn edges(&self) -> Vec<(usize, usize)> {
        let mut e = vec![];
        for v in 0..self.n {
            for &w in self.nb(v) {
                if (v as u32) < w {
                    e.push((v, w as usize));
                }
            }
        }
        e
    }

    /// Check that adjacency is symmetric as a multiset.
    pub fn is_symmetric(&self) -> bool {
        let mut cnt = std::collections::HashMap::new();
        for v in 0..self.n {
            for &w in self.nb(v) {
                *cnt.entry((v as u32, w)).or_insert(0i32) += 1;
            }
        }
        cnt.iter().all(|(&(a, b), &c)| cnt.get(&(b, a)) == Some(&c))
    }

    pub fn is_simple(&self) -> bool {
        (0..self.n).all(|v| {
            let mut s = HashSet::new();
            self.nb(v).iter().all(|&w| w as usize != v && s.insert(w))
        })
    }

    pub fn bfs(&self, src: usize) -> Vec<u32> {
        let mut dist = vec![u32::MAX; self.n];
        dist[src] = 0;
        let mut q = VecDeque::from([src]);
        while let Some(v) = q.pop_front() {
            for &w in self.nb(v) {
                if dist[w as usize] == u32::MAX {
                    dist[w as usize] = dist[v] + 1;
                    q.push_back(w as usize);
                }
            }
        }
        dist
    }

    pub fn is_connected(&self) -> bool {
        self.bfs(0).iter().all(|&x| x != u32::MAX)
    }

    /// Ball of radius r around v (vertices in BFS order).
    pub fn ball(&self, v: usize, r: u32, mark: &mut Vec<u32>, stamp: u32) -> Vec<u32> {
        let mut out = vec![v as u32];
        mark[v] = stamp;
        let mut start = 0;
        for _ in 0..r {
            let end = out.len();
            for i in start..end {
                let x = out[i] as usize;
                for &w in self.nb(x) {
                    if mark[w as usize] != stamp {
                        mark[w as usize] = stamp;
                        out.push(w);
                    }
                }
            }
            start = end;
        }
        out
    }

    /// Text format: first line "n d name", then one line per undirected edge "u v".
    pub fn to_text(&self) -> String {
        let mut s = format!("{} {} {}\n", self.n, self.d, self.name);
        for (u, v) in self.edges() {
            s += &format!("{u} {v}\n");
        }
        s
    }
}

/// Random d-regular simple connected graph. Configuration model; for d <= 6 plain rejection, for larger
/// d the pairing is repaired by random double-edge switches that remove loops and multi-edges (this is
/// the standard McKay–Wormald-style repair and is close to, but not exactly, uniform).
pub fn random_regular(n: usize, d: usize, seed: u64) -> Graph {
    assert!(n * d % 2 == 0 && d < n);
    let mut rng = SmallRng::seed_from_u64(seed ^ 0x9e37_79b9_7f4a_7c15);
    let name = format!("rr{d}_n{n}_s{seed}");
    loop {
        let mut pts: Vec<usize> = (0..n * d).map(|i| i / d).collect();
        pts.shuffle(&mut rng);
        let mut e: Vec<(usize, usize)> = pts.chunks(2).map(|c| (c[0].min(c[1]), c[0].max(c[1]))).collect();
        let bad = |e: &[(usize, usize)]| -> Vec<usize> {
            let mut seen = HashSet::new();
            let mut b = vec![];
            for (i, &(u, v)) in e.iter().enumerate() {
                if u == v || !seen.insert((u, v)) {
                    b.push(i);
                }
            }
            b
        };
        if d <= 6 {
            if !bad(&e).is_empty() {
                continue;
            }
        } else {
            let mut tries = 0;
            loop {
                let b = bad(&e);
                if b.is_empty() {
                    break;
                }
                tries += 1;
                if tries > 100_000 {
                    break;
                }
                let mut set: HashSet<(usize, usize)> = e.iter().cloned().collect();
                for &i in &b {
                    let j = rng.gen_range(0..e.len());
                    if i == j {
                        continue;
                    }
                    let (a, bb) = e[i];
                    let (c, dd) = e[j];
                    let (x1, x2) = if rng.gen::<bool>() { ((a, c), (bb, dd)) } else { ((a, dd), (bb, c)) };
                    let n1 = (x1.0.min(x1.1), x1.0.max(x1.1));
                    let n2 = (x2.0.min(x2.1), x2.0.max(x2.1));
                    if n1.0 == n1.1 || n2.0 == n2.1 || set.contains(&n1) || set.contains(&n2) || n1 == n2 {
                        continue;
                    }
                    e[i] = n1;
                    e[j] = n2;
                    set.insert(n1);
                    set.insert(n2);
                }
            }
            if !bad(&e).is_empty() {
                continue;
            }
        }
        let g = Graph::from_edges(n, &e, &name);
        if g.is_connected() {
            return g;
        }
    }
}

pub fn cycle(n: usize) -> Graph {
    let e: Vec<_> = (0..n).map(|i| (i, (i + 1) % n)).collect();
    Graph::from_edges(n, &e, &format!("cycle{n}"))
}

/// a x b torus (4-regular).
pub fn torus(a: usize, b: usize) -> Graph {
    let id = |i: usize, j: usize| (i % a) * b + (j % b);
    let mut e = vec![];
    for i in 0..a {
        for j in 0..b {
            e.push((id(i, j), id(i + 1, j)));
            e.push((id(i, j), id(i, j + 1)));
        }
    }
    Graph::from_edges(a * b, &e, &format!("torus{a}x{b}"))
}

pub fn lcf(n: usize, pat: &[i64], name: &str) -> Graph {
    let mut s = HashSet::new();
    for i in 0..n {
        let j = (i + 1) % n;
        s.insert((i.min(j), i.max(j)));
        let k = ((i as i64 + pat[i % pat.len()]).rem_euclid(n as i64)) as usize;
        s.insert((i.min(k), i.max(k)));
    }
    let mut e: Vec<_> = s.into_iter().collect();
    e.sort();
    Graph::from_edges(n, &e, name)
}

pub fn named(name: &str) -> Option<Graph> {
    Some(match name {
        "petersen" => {
            let mut e: Vec<(usize, usize)> = (0..5).map(|i| (i, (i + 1) % 5)).collect();
            e.extend((0..5).map(|i| (5 + i, 5 + (i + 2) % 5)));
            e.extend((0..5).map(|i| (i, i + 5)));
            Graph::from_edges(10, &e, "petersen")
        }
        "k33" => {
            let e: Vec<_> = (0..3).flat_map(|i| (0..3).map(move |j| (i, 3 + j))).collect();
            Graph::from_edges(6, &e, "k33")
        }
        "cube" => {
            let e: Vec<_> = (0..8usize)
                .flat_map(|i| (0..3).map(move |b| (i, i ^ (1 << b))))
                .filter(|&(i, j)| i < j)
                .collect();
            Graph::from_edges(8, &e, "cube")
        }
        "heawood" => lcf(14, &[5, -5], "heawood"),
        "pappus" => lcf(18, &[5, 7, -7, 7, -7, -5], "pappus"),
        "mcgee" => lcf(24, &[12, 7, -7], "mcgee"),
        "tutte-coxeter" => lcf(30, &[-13, -9, 7, -7, 9, 13], "tutte-coxeter"),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn generators() {
        for (n, d) in [(16, 3), (64, 4), (128, 6), (200, 12), (300, 16)] {
            let g = random_regular(n, d, 7);
            assert!(g.is_simple() && g.is_symmetric() && g.is_connected());
            assert_eq!(g.adj.len(), n * d);
        }
        for nm in ["petersen", "heawood", "pappus", "mcgee", "tutte-coxeter", "k33", "cube"] {
            let g = named(nm).unwrap();
            assert_eq!(g.d, 3, "{nm}");
            assert!(g.is_simple());
        }
        assert!(torus(5, 6).is_simple());
    }
}
