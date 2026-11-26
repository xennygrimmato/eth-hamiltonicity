//! CAT(0) model spaces for small configurations: l2 products of metric trees (lines are trees),
//! Euclidean point sets, and Euclidean cones over metric graphs (CAT(0) when the graph has
//! girth >= 2*pi). Each comes with a parallel multistart minimiser of a ratio of linear forms in
//! the distances of n labelled points placed in the space.

use crate::metric::{npairs, pair_index, pairs, Metric};
use crate::opt::{dot, minimize_box};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rayon::prelude::*;

/// All binary tree topologies with leaves 0..n-1 (internal nodes n..2n-3), as edge lists.
/// Every tree metric on n points is the leaf metric of one of these with lengths >= 0.
pub fn binary_trees(n: usize) -> Vec<Vec<(usize, usize)>> {
    assert!(n >= 3);
    let mut trees = vec![vec![(0, n), (1, n), (2, n)]];
    for leaf in 3..n {
        let mut next = vec![];
        for t in &trees {
            let newnode = n + leaf - 2;
            for e in 0..t.len() {
                let (a, b) = t[e];
                let mut t2 = t.clone();
                t2[e] = (a, newnode);
                t2.push((newnode, b));
                t2.push((leaf, newnode));
                next.push(t2);
            }
        }
        trees = next;
    }
    trees
}

/// Path incidence: for each leaf pair (storage order) the list of edge indices on its path.
pub fn path_incidence(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
    let nv = edges.iter().map(|&(a, b)| a.max(b)).max().unwrap() + 1;
    let mut adj = vec![vec![]; nv];
    for (k, &(a, b)) in edges.iter().enumerate() {
        adj[a].push((b, k));
        adj[b].push((a, k));
    }
    pairs(n)
        .into_iter()
        .map(|(i, j)| {
            // DFS from i to j
            let mut stack = vec![(i, usize::MAX, vec![])];
            while let Some((v, parent, path)) = stack.pop() {
                if v == j {
                    return path;
                }
                for &(w, k) in &adj[v] {
                    if w != parent {
                        let mut p2 = path.clone();
                        p2.push(k);
                        stack.push((w, v, p2));
                    }
                }
            }
            unreachable!()
        })
        .collect()
}

/// A product of trees: factor t has topology `inc[t]` (path incidence) and lengths block t.
#[derive(Clone, Debug)]
pub struct TreeProduct {
    pub n: usize,
    pub inc: Vec<Vec<Vec<usize>>>,
    pub nedges: Vec<usize>,
}

impl TreeProduct {
    pub fn new(n: usize, topologies: &[Vec<(usize, usize)>]) -> Self {
        TreeProduct {
            n,
            inc: topologies.iter().map(|t| path_incidence(n, t)).collect(),
            nedges: topologies.iter().map(|t| t.len()).collect(),
        }
    }
    pub fn nparams(&self) -> usize {
        self.nedges.iter().sum()
    }
    /// Squared distances per factor.
    pub fn metric(&self, len: &[f64]) -> Metric {
        let mut d2 = vec![0.0; npairs(self.n)];
        let mut off = 0;
        for (t, inc) in self.inc.iter().enumerate() {
            for (p, path) in inc.iter().enumerate() {
                let s: f64 = path.iter().map(|&k| len[off + k]).sum();
                d2[p] += s * s;
            }
            off += self.nedges[t];
        }
        Metric::new(self.n, d2.into_iter().map(f64::sqrt).collect())
    }
    /// ratio N.d/D.d and gradient wrt lengths.
    pub fn ratio_grad(&self, len: &[f64], num: &[f64], den: &[f64], g: &mut [f64]) -> f64 {
        let np = npairs(self.n);
        let mut fac = vec![vec![0.0; np]; self.inc.len()];
        let mut d2 = vec![0.0; np];
        let mut off = 0;
        for (t, inc) in self.inc.iter().enumerate() {
            for (p, path) in inc.iter().enumerate() {
                let s: f64 = path.iter().map(|&k| len[off + k]).sum();
                fac[t][p] = s;
                d2[p] += s * s;
            }
            off += self.nedges[t];
        }
        let d: Vec<f64> = d2.iter().map(|x| (x + 1e-30).sqrt()).collect();
        let a = dot(num, &d);
        let b = dot(den, &d);
        let r = a / b;
        // dR/dd_p = (num_p - r den_p)/b ; dd_p/dlen = fac_t,p / d_p on path edges
        for x in g.iter_mut() {
            *x = 0.0;
        }
        let mut off = 0;
        for (t, inc) in self.inc.iter().enumerate() {
            for (p, path) in inc.iter().enumerate() {
                let w = (num[p] - r * den[p]) / b * fac[t][p] / d[p];
                for &k in path {
                    g[off + k] += w;
                }
            }
            off += self.nedges[t];
        }
        r
    }
}

#[derive(Clone, Debug)]
pub struct ModelResult {
    pub value: f64,
    pub params: Vec<f64>,
    pub metric: Metric,
    pub label: String,
}

/// Minimise N.d/D.d over n points in a product of `k` trees, over all unordered tuples of the
/// binary topologies, with `starts` random starts each. Returns results sorted by value.
pub fn min_ratio_tree_products(n: usize, k: usize, num: &[f64], den: &[f64], starts: usize, iters: usize, seed: u64)
    -> Vec<ModelResult> {
    let tops = binary_trees(n);
    let nt = tops.len();
    let mut tuples: Vec<Vec<usize>> = vec![vec![]];
    for _ in 0..k {
        let mut next = vec![];
        for t in &tuples {
            let lo = *t.last().unwrap_or(&0);
            for c in lo..nt {
                let mut t2 = t.clone();
                t2.push(c);
                next.push(t2);
            }
        }
        tuples = next;
    }
    let mut res: Vec<ModelResult> = tuples
        .par_iter()
        .enumerate()
        .map(|(ti, tup)| {
            let topo: Vec<Vec<(usize, usize)>> = tup.iter().map(|&c| tops[c].clone()).collect();
            let tp = TreeProduct::new(n, &topo);
            let np = tp.nparams();
            let mut rng = SmallRng::seed_from_u64(seed ^ (ti as u64).wrapping_mul(0x9E3779B97F4A7C15));
            let lo = vec![0.0; np];
            let hi = vec![f64::INFINITY; np];
            let mut best: Option<ModelResult> = None;
            for _ in 0..starts {
                let x0: Vec<f64> = (0..np).map(|_| rng.gen::<f64>() * if rng.gen::<f64>() < 0.3 { 0.0 } else { 1.0 }).collect();
                let (x, _) = minimize_box(
                    |x, g| {
                        let r = tp.ratio_grad(x, num, den, g);
                        // keep scale fixed softly: penalise (sum x - 1)^2
                        let s: f64 = x.iter().sum::<f64>() - 1.0;
                        for gi in g.iter_mut() {
                            *gi += 2.0 * s;
                        }
                        r + s * s
                    },
                    &x0,
                    &lo,
                    &hi,
                    iters,
                    1e-13,
                );
                let m = tp.metric(&x);
                let v = m.ratio(num, den);
                if v.is_finite() && best.as_ref().map_or(true, |b| v < b.value) {
                    best = Some(ModelResult { value: v, params: x, metric: m, label: format!("trees {:?}", tup) });
                }
            }
            best.unwrap()
        })
        .collect();
    res.sort_by(|a, b| a.value.partial_cmp(&b.value).unwrap());
    res
}

/// Minimise N.d/D.d over n points in R^dim.
pub fn min_ratio_euclidean(n: usize, dim: usize, num: &[f64], den: &[f64], starts: usize, iters: usize, seed: u64)
    -> Vec<ModelResult> {
    let mut res: Vec<ModelResult> = (0..starts)
        .into_par_iter()
        .map(|s| {
            let mut rng = SmallRng::seed_from_u64(seed.wrapping_add(s as u64 * 7919));
            let x0: Vec<f64> = (0..n * dim).map(|_| rng.gen::<f64>() * 2.0 - 1.0).collect();
            let np = n * dim;
            let lo = vec![f64::NEG_INFINITY; np];
            let hi = vec![f64::INFINITY; np];
            let pr = pairs(n);
            let (x, _) = minimize_box(
                |x, g| {
                    let d: Vec<f64> = pr
                        .iter()
                        .map(|&(i, j)| {
                            ((0..dim).map(|c| (x[i * dim + c] - x[j * dim + c]).powi(2)).sum::<f64>() + 1e-30).sqrt()
                        })
                        .collect();
                    let a = dot(num, &d);
                    let b = dot(den, &d);
                    let r = a / b;
                    for gi in g.iter_mut() {
                        *gi = 0.0;
                    }
                    for (p, &(i, j)) in pr.iter().enumerate() {
                        let w = (num[p] - r * den[p]) / b / d[p];
                        for c in 0..dim {
                            let t = w * (x[i * dim + c] - x[j * dim + c]);
                            g[i * dim + c] += t;
                            g[j * dim + c] -= t;
                        }
                    }
                    // scale: penalise (b-1)^2
                    let s = b - 1.0;
                    for (p, &(i, j)) in pr.iter().enumerate() {
                        let w = 2.0 * s * den[p] / d[p];
                        for c in 0..dim {
                            let t = w * (x[i * dim + c] - x[j * dim + c]);
                            g[i * dim + c] += t;
                            g[j * dim + c] -= t;
                        }
                    }
                    r + s * s
                },
                &x0,
                &lo,
                &hi,
                iters,
                1e-13,
            );
            let pts: Vec<Vec<f64>> = (0..n).map(|i| x[i * dim..(i + 1) * dim].to_vec()).collect();
            let m = Metric::euclidean(&pts);
            ModelResult { value: m.ratio(num, den), params: x, metric: m, label: format!("R^{}", dim) }
        })
        .collect();
    res.sort_by(|a, b| a.value.partial_cmp(&b.value).unwrap());
    res
}

/// Euclidean cone over a metric graph G (vertices 0..nv-1, edges with lengths).
/// A point is (edge e, position t in [0,1] along it, radius r >= 0). Cone distance:
/// d^2 = r1^2 + r2^2 - 2 r1 r2 cos(min(dG, pi)). CAT(0) iff G is CAT(1) (girth >= 2 pi for graphs).
#[derive(Clone, Debug)]
pub struct GraphCone {
    pub nv: usize,
    pub edges: Vec<(usize, usize, f64)>,
    pub vdist: Vec<Vec<f64>>,
}

impl GraphCone {
    pub fn new(nv: usize, edges: Vec<(usize, usize, f64)>) -> Self {
        let vdist = crate::metric::all_pairs_shortest(nv, &edges);
        GraphCone { nv, edges, vdist }
    }
    /// Graph distance between points (e1,t1) and (e2,t2).
    pub fn gdist(&self, e1: usize, t1: f64, e2: usize, t2: f64) -> f64 {
        let (a1, b1, l1) = self.edges[e1];
        let (a2, b2, l2) = self.edges[e2];
        if e1 == e2 {
            let direct = (t1 - t2).abs() * l1;
            let around = l1 * (t1.min(t2)) + l1 * (1.0 - t1.max(t2)) + self.vdist[a1][b1];
            return direct.min(around);
        }
        let ends1 = [(a1, t1 * l1), (b1, (1.0 - t1) * l1)];
        let ends2 = [(a2, t2 * l2), (b2, (1.0 - t2) * l2)];
        let mut best = f64::INFINITY;
        for &(x, dx) in &ends1 {
            for &(y, dy) in &ends2 {
                best = best.min(dx + self.vdist[x][y] + dy);
            }
        }
        best
    }
    pub fn dist(&self, p: (usize, f64, f64), q: (usize, f64, f64)) -> f64 {
        let ang = self.gdist(p.0, p.1, q.0, q.1).min(std::f64::consts::PI);
        (p.2 * p.2 + q.2 * q.2 - 2.0 * p.2 * q.2 * ang.cos()).max(0.0).sqrt()
    }
    pub fn metric(&self, pts: &[(usize, f64, f64)]) -> Metric {
        Metric::from_fn(pts.len(), |i, j| self.dist(pts[i], pts[j]))
    }
    /// Girth (shortest cycle length) of the metric graph.
    pub fn girth(&self) -> f64 {
        let mut best = f64::INFINITY;
        for (k, &(a, b, l)) in self.edges.iter().enumerate() {
            let rest: Vec<(usize, usize, f64)> =
                self.edges.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, e)| *e).collect();
            let d = crate::metric::all_pairs_shortest(self.nv, &rest);
            best = best.min(d[a][b] + l);
        }
        best
    }
}

/// Minimise the ratio over n points in the cone over G, optionally times R^line_dim (l2 product).
/// Discrete choice of edges by random sampling; continuous (t, r, line coords) by finite-difference
/// projected gradient.
pub fn min_ratio_graph_cone(cone: &GraphCone, n: usize, line_dim: usize, num: &[f64], den: &[f64], starts: usize,
    iters: usize, seed: u64) -> Vec<ModelResult> {
    let ne = cone.edges.len();
    let mut res: Vec<ModelResult> = (0..starts)
        .into_par_iter()
        .map(|s| {
            let mut rng = SmallRng::seed_from_u64(seed.wrapping_add(s as u64 * 104729));
            let es: Vec<usize> = (0..n).map(|_| rng.gen_range(0..ne)).collect();
            let per = 2 + line_dim;
            let np = n * per;
            let mut lo = vec![0.0; np];
            let mut hi = vec![f64::INFINITY; np];
            for i in 0..n {
                hi[i * per] = 1.0;
                for c in 0..line_dim {
                    lo[i * per + 2 + c] = f64::NEG_INFINITY;
                }
            }
            let x0: Vec<f64> = (0..np)
                .map(|k| if k % per == 0 { rng.gen::<f64>() } else if k % per == 1 { rng.gen::<f64>() + 0.1 } else { rng.gen::<f64>() - 0.5 })
                .collect();
            let eval = |x: &[f64]| -> Metric {
                let pts: Vec<(usize, f64, f64)> = (0..n).map(|i| (es[i], x[i * per], x[i * per + 1])).collect();
                let mc = cone.metric(&pts);
                if line_dim == 0 {
                    return mc;
                }
                Metric::from_fn(n, |i, j| {
                    let l2: f64 = (0..line_dim).map(|c| (x[i * per + 2 + c] - x[j * per + 2 + c]).powi(2)).sum();
                    (mc.get(i, j).powi(2) + l2).sqrt()
                })
            };
            let f = |x: &[f64]| -> f64 {
                let m = eval(x);
                let b = dot(den, &m.d);
                m.ratio(num, den) + (b - 1.0).powi(2)
            };
            let (x, _) = minimize_box(
                |x, g| {
                    let f0 = f(x);
                    let mut xp = x.to_vec();
                    for k in 0..x.len() {
                        let h = 1e-7;
                        xp[k] = x[k] + h;
                        let fp = f(&xp);
                        xp[k] = x[k] - h;
                        let fm = f(&xp);
                        xp[k] = x[k];
                        g[k] = (fp - fm) / (2.0 * h);
                    }
                    f0
                },
                &x0,
                &lo,
                &hi,
                iters,
                1e-11,
            );
            let m = eval(&x);
            ModelResult { value: m.ratio(num, den), params: x, metric: m, label: format!("cone edges {:?}", es) }
        })
        .collect();
    res.sort_by(|a, b| a.value.partial_cmp(&b.value).unwrap());
    res
}

/// The Heawood graph (incidence graph of the Fano plane): points 0..7, lines 7..14.
pub fn heawood_edges(len: f64) -> Vec<(usize, usize, f64)> {
    let lines = [[0, 1, 3], [1, 2, 4], [2, 3, 5], [3, 4, 6], [4, 5, 0], [5, 6, 1], [6, 0, 2]];
    let mut e = vec![];
    for (l, pts) in lines.iter().enumerate() {
        for &p in pts {
            e.push((p, 7 + l, len));
        }
    }
    e
}

/// Index helper re-exported for convenience.
pub fn pidx(n: usize, i: usize, j: usize) -> usize {
    pair_index(n, i, j)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn count_trees() {
        assert_eq!(binary_trees(4).len(), 3);
        assert_eq!(binary_trees(5).len(), 15);
        assert_eq!(binary_trees(6).len(), 105);
    }
    #[test]
    fn heawood_girth() {
        let c = GraphCone::new(14, heawood_edges(std::f64::consts::PI / 3.0));
        assert!((c.girth() - 2.0 * std::f64::consts::PI).abs() < 1e-12);
    }
}
