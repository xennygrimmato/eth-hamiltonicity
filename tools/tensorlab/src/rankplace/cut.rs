//! beta_cut(G) = max over cuts S of E_pairs delta_S / E_edges delta_S = (2 s (n-s) / n^2) / (e(S) / m),
//! m = nd/2. Exact by Gray-code enumeration for n <= 30 (parallel), otherwise lower bounds from spectral
//! and BFS sweeps followed by simulated annealing on single-vertex flips. Upper bound: 1/(1-lambda_2).

use super::graph::Graph;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use rayon::prelude::*;

#[inline]
pub fn cut_ratio(n: usize, d: usize, s: usize, e: usize) -> f64 {
    if e == 0 {
        return 0.0;
    }
    let m = (n * d) as f64 / 2.0;
    (2.0 * s as f64 * (n - s) as f64 / (n * n) as f64) / (e as f64 / m)
}

pub fn cut_size(g: &Graph, side: &[bool]) -> usize {
    let mut e = 0;
    for v in 0..g.n {
        for &w in g.nb(v) {
            if side[v] != side[w as usize] {
                e += 1;
            }
        }
    }
    e / 2
}

#[derive(Clone, Debug)]
pub struct CutResult {
    pub ratio: f64,
    pub side: Vec<bool>,
    pub exact: bool,
}

/// Exact maximum, n <= 30.
pub fn beta_cut_exact(g: &Graph) -> CutResult {
    let n = g.n;
    assert!(n <= 32 && n >= 2);
    let free = n - 1; // vertex n-1 always outside S
    let t = free.min(6);
    let low = free - t;
    let best = (0u64..(1u64 << t))
        .into_par_iter()
        .map(|pre| {
            let mut mask: u64 = pre << low;
            let in_s = |mask: u64, v: usize| (mask >> v) & 1 == 1;
            let side: Vec<bool> = (0..n).map(|v| in_s(mask, v)).collect();
            let mut e = cut_size(g, &side) as i64;
            let mut s = mask.count_ones() as usize;
            let mut best = (0.0f64, 0u64);
            let eval = |mask: u64, s: usize, e: i64, best: &mut (f64, u64)| {
                if s > 0 {
                    let r = cut_ratio(n, g.d, s, e as usize);
                    if r > best.0 {
                        *best = (r, mask);
                    }
                }
            };
            eval(mask, s, e, &mut best);
            for i in 1u64..(1u64 << low) {
                let v = i.trailing_zeros() as usize;
                let sv = in_s(mask, v);
                for &w in g.nb(v) {
                    if in_s(mask, w as usize) == sv {
                        e += 1;
                    } else {
                        e -= 1;
                    }
                }
                mask ^= 1u64 << v;
                if sv {
                    s -= 1
                } else {
                    s += 1
                }
                eval(mask, s, e, &mut best);
            }
            best
        })
        .reduce(|| (0.0, 0), |a, b| if b.0 > a.0 { b } else { a });
    CutResult { ratio: best.0, side: (0..n).map(|v| (best.1 >> v) & 1 == 1).collect(), exact: true }
}

/// Best prefix of a vertex order.
pub fn sweep(g: &Graph, order: &[usize]) -> (f64, usize) {
    let n = g.n;
    let mut side = vec![false; n];
    let mut e: i64 = 0;
    let mut best = (0.0, 0);
    for (i, &v) in order.iter().enumerate().take(n - 1) {
        for &w in g.nb(v) {
            if side[w as usize] {
                e -= 1
            } else {
                e += 1
            }
        }
        side[v] = true;
        let r = cut_ratio(n, g.d, i + 1, e as usize);
        if r > best.0 {
            best = (r, i + 1);
        }
    }
    best
}

fn sa_cut(g: &Graph, side: Vec<bool>, iters: u64, seed: u64) -> (f64, Vec<bool>) {
    sa_cut_t(g, side, iters, 0.03, 1e-4, seed)
}

/// Annealing on single-vertex flips, objective ln(cut ratio), geometric schedule t0 -> t1.
pub fn sa_cut_t(g: &Graph, mut side: Vec<bool>, iters: u64, t0: f64, t1: f64, seed: u64) -> (f64, Vec<bool>) {
    let n = g.n;
    let mut rng = SmallRng::seed_from_u64(seed);
    let mut s = side.iter().filter(|&&b| b).count();
    let mut e = cut_size(g, &side) as i64;
    let val = |s: usize, e: i64| if s == 0 || s == n || e == 0 { f64::NEG_INFINITY } else { cut_ratio(n, g.d, s, e as usize).ln() };
    let mut cur = val(s, e);
    let mut best = (cur, side.clone());
    for it in 0..iters {
        let t = t0 * (t1 / t0).powf(it as f64 / iters as f64);
        let v = rng.gen_range(0..n);
        let mut de = 0i64;
        for &w in g.nb(v) {
            if side[w as usize] == side[v] {
                de += 1
            } else {
                de -= 1
            }
        }
        let ns = if side[v] { s - 1 } else { s + 1 };
        let nv = val(ns, e + de);
        if nv.is_finite() && (nv >= cur || rng.gen::<f64>() < ((nv - cur) / t).exp()) {
            side[v] = !side[v];
            s = ns;
            e += de;
            cur = nv;
            if cur > best.0 {
                best = (cur, side.clone());
            }
        }
    }
    (best.0.exp(), best.1)
}

/// Lower bound on beta_cut for large graphs: spectral sweep, BFS-ball sweeps, then annealing.
pub fn beta_cut_heuristic(g: &Graph, fiedler: Option<&[f64]>, chains: usize, iters: u64, seed: u64) -> CutResult {
    let n = g.n;
    let mut starts: Vec<(f64, Vec<bool>)> = vec![];
    let to_side = |order: &[usize], k: usize| {
        let mut s = vec![false; n];
        for &v in &order[..k] {
            s[v] = true;
        }
        s
    };
    if let Some(f) = fiedler {
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by(|&a, &b| f[a].partial_cmp(&f[b]).unwrap());
        let (r, k) = sweep(g, &order);
        starts.push((r, to_side(&order, k)));
    }
    let mut rng = SmallRng::seed_from_u64(seed);
    for _ in 0..8.min(n) {
        let root = rng.gen_range(0..n);
        let dist = g.bfs(root);
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by_key(|&v| dist[v]);
        let (r, k) = sweep(g, &order);
        starts.push((r, to_side(&order, k)));
    }
    starts.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    let res: Vec<(f64, Vec<bool>)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let init = if c % 2 == 0 {
                starts[c / 2 % starts.len()].1.clone()
            } else {
                let mut r = SmallRng::seed_from_u64(seed + 77 * c as u64);
                (0..n).map(|_| r.gen::<bool>()).collect()
            };
            sa_cut(g, init, iters, seed + c as u64)
        })
        .collect();
    let mut best = starts[0].clone();
    for r in res {
        if r.0 > best.0 {
            best = r;
        }
    }
    CutResult { ratio: best.0, side: best.1, exact: false }
}

/// Exact for n <= 32 (Gray code over 2^(n-1) subsets), else the heuristic with 50000 n flips per chain
/// (capped at 2e8), 8 chains. The heuristic value is a lower bound; tuning on random cubic graphs (n = 512)
/// showed it still creeping up by ~2% when the budget is quadrupled.
pub fn beta_cut(g: &Graph, fiedler: Option<&[f64]>) -> CutResult {
    if g.n <= 32 {
        beta_cut_exact(g)
    } else {
        let iters = (50_000 * g.n as u64).clamp(1_000_000, 200_000_000);
        beta_cut_heuristic(g, fiedler, 8, iters, 12345)
    }
}

/// Polish a given cut by low-temperature annealing (used on cuts read off placements).
pub fn polish(g: &Graph, side: Vec<bool>, iters: u64, seed: u64) -> (f64, Vec<bool>) {
    let s0 = side.iter().filter(|&&b| b).count();
    let r0 = if s0 == 0 || s0 == g.n { 0.0 } else { cut_ratio(g.n, g.d, s0, cut_size(g, &side)) };
    let (r, s) = sa_cut_t(g, side.clone(), iters, 0.003, 1e-5, seed);
    if r >= r0 {
        (r, s)
    } else {
        (r0, side)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rankplace::graph::*;
    #[test]
    fn exact_vs_heuristic() {
        // notes §3: Petersen 1.5, Heawood 1.714..., Pappus 2.0
        let p = beta_cut_exact(&named("petersen").unwrap());
        assert!((p.ratio - 1.5).abs() < 1e-12, "{}", p.ratio);
        let h = beta_cut_exact(&named("heawood").unwrap());
        assert!((h.ratio - 12.0 / 7.0).abs() < 1e-12, "{}", h.ratio);
        let pa = beta_cut_exact(&named("pappus").unwrap());
        assert!((pa.ratio - 2.0).abs() < 1e-12, "{}", pa.ratio);
        let g = random_regular(22, 3, 4);
        let ex = beta_cut_exact(&g);
        let he = beta_cut_heuristic(&g, None, 4, 200_000, 1);
        assert!((ex.ratio - he.ratio).abs() < 1e-9, "{} {}", ex.ratio, he.ratio);
        assert!((cut_ratio(g.n, g.d, ex.side.iter().filter(|&&b| b).count(), cut_size(&g, &ex.side)) - ex.ratio).abs() < 1e-12);
    }
}

/// Several good, mostly distinct cuts (annealing with different seeds; the first is the best known).
pub fn good_cuts(g: &Graph, best: &CutResult, k: usize, seed: u64) -> Vec<Vec<bool>> {
    let iters = (10_000 * g.n as u64).clamp(100_000, 50_000_000);
    let mut out = vec![best.side.clone()];
    let res: Vec<(f64, Vec<bool>)> = (0..(2 * k) as u64)
        .into_par_iter()
        .map(|c| {
            let mut r = SmallRng::seed_from_u64(seed + 1000 * c);
            let init: Vec<bool> = (0..g.n).map(|_| r.gen::<bool>()).collect();
            sa_cut(g, init, iters, seed + 31 * c)
        })
        .collect();
    let mut res = res;
    res.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    for (_, s) in res {
        let comp: Vec<bool> = s.iter().map(|&b| !b).collect();
        if out.iter().all(|o| *o != s && *o != comp) {
            out.push(s);
        }
        if out.len() >= k {
            break;
        }
    }
    out
}

/// Cuts read off a placement: S_{x,y} = {v : y^T f(v) x = 1}. Since Pr_{x,y}[y^T M x = 1] = (1 - 2^{-rk M})/2,
/// the metric 1 - 2^{-D_f} is an average of these cut metrics, so the best S_{x,y} has cut ratio at least
/// E_pairs(1-2^{-D}) / E_edges(1-2^{-D}). Tries all (x, y) for mu <= 6, else `samples` random pairs.
pub fn cuts_from_placement(g: &Graph, mu: usize, f: &[u64], samples: usize, seed: u64) -> CutResult {
    let mut pairs = vec![];
    if mu <= 6 {
        for x in 1u8..(1u8 << mu) {
            for y in 1u8..(1u8 << mu) {
                pairs.push((x, y));
            }
        }
    } else {
        let mut rng = SmallRng::seed_from_u64(seed);
        for _ in 0..samples {
            pairs.push((super::f2::random_vec(&mut rng, mu), super::f2::random_vec(&mut rng, mu)));
        }
    }
    let best = pairs
        .par_iter()
        .map(|&(x, y)| {
            let side: Vec<bool> = f
                .iter()
                .map(|&a| {
                    let mut b = 0u32;
                    for i in 0..mu {
                        if (y >> i) & 1 == 1 {
                            b ^= ((((a >> (8 * i)) & 0xFF) as u8) & x).count_ones() & 1;
                        }
                    }
                    b == 1
                })
                .collect();
            let s = side.iter().filter(|&&b| b).count();
            let r = if s == 0 || s == g.n { 0.0 } else { cut_ratio(g.n, g.d, s, cut_size(g, &side)) };
            (r, side)
        })
        .reduce(|| (0.0, vec![]), |a, b| if b.0 > a.0 { b } else { a });
    CutResult { ratio: best.0, side: best.1, exact: false }
}
