//! Simulated annealing over placements f: V -> Mat_mu(F_2), mu <= 8, with exact incremental updates.
//!
//! Totals kept: pdir = sum over ordered pairs (u, v) of D_f(u, v) (so E_pairs D = pdir / n^2) and
//! edir = sum over v and the d neighbour slots of v of D_f(v, w) (so E_edges D = edir / (n d)); per-vertex
//! row sums row[v] = sum_w D(v, w) and edge sums esum[v] = sum_{w ~ v} D(v, w). A single-vertex move
//! costs n rank evaluations if rejected and 2n if accepted; a ball move (an isometry T of Mat_mu applied
//! to all f(w), w in a BFS ball B) costs 2|B|(n - |B|), since pairs and edges inside B do not change.
//!
//! Objectives: the ratio itself (annealed in log scale), the Lagrangian E_pairs D - gamma E_edges D,
//! or E_pairs D alone (for the gradient-bounded variant, where every edge must keep D <= r).

use super::f2;
use super::graph::Graph;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use rayon::prelude::*;
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
pub enum Objective {
    Ratio,
    Lagrange(f64),
    Pairs,
}

#[derive(Clone, Debug)]
pub struct Opts {
    pub iters: u64,
    /// temperatures in units of 1/n (geometric schedule t0 -> t1 within each cycle)
    pub t0: f64,
    pub t1: f64,
    pub cycles: usize,
    pub max_edge_rank: Option<u32>,
    /// probabilities of: bit flip, add rank one, copy neighbour + rank <= 2, ball move,
    /// add rank <= 2, random matrix
    pub p_moves: [f64; 6],
    pub ball_radius_max: u32,
    pub seed: u64,
}

impl Default for Opts {
    fn default() -> Self {
        Opts {
            iters: 200_000,
            t0: 1.0,
            t1: 0.005,
            cycles: 1,
            max_edge_rank: None,
            p_moves: [0.25, 0.35, 0.2, 0.02, 0.16, 0.02],
            ball_radius_max: 2,
            seed: 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ChainResult {
    pub value: f64,
    pub ratio: f64,
    pub epairs: f64,
    pub eedges: f64,
    pub f: Vec<u64>,
    pub accepted: u64,
    pub secs: f64,
    /// index into the `inits` list of run_chains (0 for a direct call of anneal)
    pub init: usize,
}

/// (pdir, edir) from scratch, in parallel.
pub fn totals(g: &Graph, f: &[u64]) -> (i64, i64) {
    let p: i64 = (0..g.n)
        .into_par_iter()
        .map(|u| {
            let a = f[u];
            f.iter().map(|&b| f2::rank(a ^ b) as i64).sum::<i64>()
        })
        .sum();
    let e: i64 = (0..g.n)
        .into_par_iter()
        .map(|u| g.nb(u).iter().map(|&w| f2::rank(f[u] ^ f[w as usize]) as i64).sum::<i64>())
        .sum();
    (p, e)
}

pub fn ratio_of(g: &Graph, pdir: i64, edir: i64) -> f64 {
    let n = g.n as f64;
    (pdir as f64 / (n * n)) / (edir as f64 / (n * g.d as f64))
}

/// Ratio, E_pairs, E_edges of a placement.
pub fn evaluate(g: &Graph, f: &[u64]) -> (f64, f64, f64) {
    let (p, e) = totals(g, f);
    let n = g.n as f64;
    (ratio_of(g, p, e), p as f64 / (n * n), e as f64 / (n * g.d as f64))
}

pub fn max_edge_rank(g: &Graph, f: &[u64]) -> u32 {
    (0..g.n).map(|u| g.nb(u).iter().map(|&w| f2::rank(f[u] ^ f[w as usize])).max().unwrap_or(0)).max().unwrap()
}

#[inline]
fn value(obj: Objective, n: usize, d: usize, pdir: i64, edir: i64) -> f64 {
    let nn = (n * n) as f64;
    match obj {
        Objective::Ratio => {
            if edir <= 0 || pdir <= 0 {
                f64::NEG_INFINITY
            } else {
                (pdir as f64).ln() - (edir as f64).ln()
            }
        }
        Objective::Lagrange(gm) => pdir as f64 / nn - gm * edir as f64 / (n * d) as f64,
        Objective::Pairs => pdir as f64 / nn,
    }
}

struct State<'a> {
    g: &'a Graph,
    #[allow(dead_code)]
    mu: usize,
    f: Vec<u64>,
    row: Vec<i64>,
    esum: Vec<i64>,
    pdir: i64,
    edir: i64,
    buf: Vec<u8>,
    buf2: Vec<u8>,
    delta: Vec<i32>,
    mark: Vec<u32>,
    stamp: u32,
}

impl<'a> State<'a> {
    fn new(g: &'a Graph, mu: usize, f: Vec<u64>) -> State<'a> {
        let n = g.n;
        let row: Vec<i64> = (0..n).map(|u| f.iter().map(|&b| f2::rank(f[u] ^ b) as i64).sum()).collect();
        let esum: Vec<i64> = (0..n).map(|u| g.nb(u).iter().map(|&w| f2::rank(f[u] ^ f[w as usize]) as i64).sum()).collect();
        let pdir = row.iter().sum();
        let edir = esum.iter().sum();
        State { g, mu, f, row, esum, pdir, edir, buf: vec![0; n], buf2: vec![0; n], delta: vec![0; n], mark: vec![0; n], stamp: 0 }
    }

    /// Evaluate replacing f[v] by b: returns (new pdir, new edir, new row[v], new esum[v]) or None if
    /// an edge would exceed the rank bound.
    fn try_vertex(&mut self, v: usize, b: u64, maxr: Option<u32>) -> Option<(i64, i64, i64, i64)> {
        let g = self.g;
        let mut ne = 0i64;
        for &w in g.nb(v) {
            let r = f2::rank(b ^ self.f[w as usize]);
            if let Some(m) = maxr {
                if r > m {
                    return None;
                }
            }
            ne += r as i64;
        }
        // the w = v slot gives rank(b ^ a), removed afterwards
        let mut nr = f2::ranks_against(b, &self.f, &mut self.buf);
        nr -= self.buf[v] as i64;
        self.buf[v] = 0;
        Some((self.pdir + 2 * (nr - self.row[v]), self.edir + 2 * (ne - self.esum[v]), nr, ne))
    }

    fn accept_vertex(&mut self, v: usize, b: u64, np: i64, ne_tot: i64, nr: i64, ne: i64) {
        let a = self.f[v];
        f2::ranks_against(a, &self.f, &mut self.buf2);
        for ((rw, &bw), &ow) in self.row.iter_mut().zip(self.buf.iter()).zip(self.buf2.iter()) {
            *rw += bw as i64 - ow as i64;
        }
        // the w = v term above added 0 - rank(a ^ a) = 0
        for &w in self.g.nb(v) {
            let w = w as usize;
            self.esum[w] += f2::rank(b ^ self.f[w]) as i64 - f2::rank(a ^ self.f[w]) as i64;
        }
        self.row[v] = nr;
        self.esum[v] = ne;
        self.f[v] = b;
        self.pdir = np;
        self.edir = ne_tot;
    }

    /// Ball move: apply the isometry t to f on the ball B. Returns the ball and new totals, with per-vertex
    /// row deltas in self.delta, or None (constraint).
    fn try_ball(&mut self, ball: &[u32], t: &dyn Fn(u64) -> u64, maxr: Option<u32>) -> Option<(i64, i64)> {
        let g = self.g;
        let st = self.stamp;
        // edges crossing the boundary
        let mut de = 0i64;
        for &w in ball {
            let w = w as usize;
            let tw = t(self.f[w]);
            for &u in g.nb(w) {
                let u = u as usize;
                if self.mark[u] != st {
                    let r = f2::rank(tw ^ self.f[u]);
                    if let Some(m) = maxr {
                        if r > m {
                            return None;
                        }
                    }
                    de += r as i64 - f2::rank(self.f[w] ^ self.f[u]) as i64;
                }
            }
        }
        let mut dp = 0i64;
        for &w in ball {
            let w = w as usize;
            let (fw, tw) = (self.f[w], t(self.f[w]));
            f2::ranks_against(tw, &self.f, &mut self.buf);
            f2::ranks_against(fw, &self.f, &mut self.buf2);
            let mut dw = 0i32;
            for u in 0..g.n {
                let x = (self.buf[u] as i32 - self.buf2[u] as i32) * (self.mark[u] != st) as i32;
                dw += x;
                self.delta[u] += x;
            }
            self.delta[w] = dw;
            dp += dw as i64;
        }
        Some((self.pdir + 2 * dp, self.edir + 2 * de))
    }

    fn finish_ball(&mut self, ball: &[u32], t: &dyn Fn(u64) -> u64, accept: bool, np: i64, ne: i64) {
        let g = self.g;
        let st = self.stamp;
        if accept {
            for &w in ball {
                let w = w as usize;
                let tw = t(self.f[w]);
                for &u in g.nb(w) {
                    let u = u as usize;
                    if self.mark[u] != st {
                        let x = f2::rank(tw ^ self.f[u]) as i64 - f2::rank(self.f[w] ^ self.f[u]) as i64;
                        self.esum[w] += x;
                        self.esum[u] += x;
                    }
                }
            }
            for &w in ball {
                let w = w as usize;
                self.f[w] = t(self.f[w]);
            }
            for u in 0..g.n {
                self.row[u] += self.delta[u] as i64;
            }
            self.pdir = np;
            self.edir = ne;
        }
        self.delta.iter_mut().for_each(|x| *x = 0);
    }
}

/// One annealing chain from the initial placement f0.
pub fn anneal(g: &Graph, mu: usize, obj: Objective, opts: &Opts, f0: Vec<u64>) -> ChainResult {
    let start = Instant::now();
    let n = g.n;
    let mask = f2::block_mask(mu);
    assert!(f0.len() == n && f0.iter().all(|&a| a & !mask == 0));
    if let Some(r) = opts.max_edge_rank {
        assert!(max_edge_rank(g, &f0) <= r, "initial placement violates the edge bound");
    }
    let mut rng = SmallRng::seed_from_u64(opts.seed);
    let mut st = State::new(g, mu, f0);
    let mut cur = value(obj, n, g.d, st.pdir, st.edir);
    // best placement, stored lazily: while at_best the current state is the best one, and it is copied
    // only when an accepted move leaves it without improving
    let mut best = (cur, st.f.clone(), st.pdir, st.edir);
    let mut at_best = false;
    let mut cum = [0.0; 6];
    let tot: f64 = opts.p_moves.iter().sum();
    let mut acc = 0.0;
    for i in 0..6 {
        acc += opts.p_moves[i] / tot;
        cum[i] = acc;
    }
    let maxr = opts.max_edge_rank;
    let mut accepted = 0u64;
    let cycles = opts.cycles.max(1);
    let per = opts.iters / cycles as u64;
    for cyc in 0..cycles {
        if cyc > 0 {
            // restart the cycle from the best placement found so far
            if at_best {
                best.1.copy_from_slice(&st.f);
                at_best = false;
            }
            st = State::new(g, mu, best.1.clone());
            cur = best.0;
        }
        for it in 0..per {
            let t = opts.t0 * (opts.t1 / opts.t0).powf(it as f64 / per as f64) / n as f64;
            let v = rng.gen_range(0..n);
            let u: f64 = rng.gen();
            let mv = cum.iter().position(|&c| u < c).unwrap_or(5);
            if mv == 3 {
                // ball move
                let rad = rng.gen_range(1..=opts.ball_radius_max.max(1));
                st.stamp += 1;
                let stamp = st.stamp;
                let ball = g.ball(v, rad, &mut st.mark, stamp);
                if ball.len() * 2 > n {
                    continue;
                }
                let rr = f2::random_rank_one(&mut rng, mu);
                let kind = rng.gen_range(0..3);
                let (i, j) = (rng.gen_range(0..mu), rng.gen_range(0..mu));
                let tf: Box<dyn Fn(u64) -> u64> = match kind {
                    0 => Box::new(move |a| a ^ rr),
                    1 if i != j => Box::new(move |a| f2::row_op(a, i, j)),
                    2 if i != j => Box::new(move |a| f2::col_op(a, i, j)),
                    _ => Box::new(move |a| a ^ rr),
                };
                // (try_ball checks the edge bound before touching the row deltas)
                if let Some((np, ne)) = st.try_ball(&ball, &*tf, maxr) {
                    let nv = value(obj, n, g.d, np, ne);
                    let ok = nv >= cur || rng.gen::<f64>() < ((nv - cur) / t).exp();
                    if ok && at_best && nv <= best.0 {
                        best.1.copy_from_slice(&st.f);
                        at_best = false;
                    }
                    st.finish_ball(&ball, &*tf, ok, np, ne);
                    if ok {
                        cur = nv;
                        accepted += 1;
                    }
                }
            } else {
                let a = st.f[v];
                let b = match mv {
                    0 => a ^ f2::unit(rng.gen_range(0..mu), rng.gen_range(0..mu)),
                    1 => a ^ f2::random_rank_one(&mut rng, mu),
                    2 => {
                        let w = g.nb(v)[rng.gen_range(0..g.d)] as usize;
                        let r = rng.gen_range(0..3);
                        st.f[w] ^ f2::random_rank_le(&mut rng, mu, r)
                    }
                    4 => a ^ f2::random_rank_le(&mut rng, mu, 2),
                    _ => f2::random_matrix(&mut rng, mu),
                };
                if b == a {
                    continue;
                }
                if let Some((np, ne_tot, nr, ne)) = st.try_vertex(v, b, maxr) {
                    let nv = value(obj, n, g.d, np, ne_tot);
                    if nv >= cur || rng.gen::<f64>() < ((nv - cur) / t).exp() {
                        if at_best && nv <= best.0 {
                            best.1.copy_from_slice(&st.f);
                            at_best = false;
                        }
                        st.accept_vertex(v, b, np, ne_tot, nr, ne);
                        cur = nv;
                        accepted += 1;
                    }
                }
            }
            if cur > best.0 {
                best.0 = cur;
                best.2 = st.pdir;
                best.3 = st.edir;
                at_best = true;
            }
        }
    }
    if at_best {
        best.1.copy_from_slice(&st.f);
    }
    let nn = (n * n) as f64;
    ChainResult {
        value: best.0,
        ratio: ratio_of(g, best.2, best.3),
        epairs: best.2 as f64 / nn,
        eedges: best.3 as f64 / (n * g.d) as f64,
        f: best.1,
        accepted,
        secs: start.elapsed().as_secs_f64(),
        init: 0,
    }
}

/// Initial placements.
#[derive(Clone, Debug)]
pub enum Init {
    /// each f(v) a sum of `rank` random rank-one matrices (rank = 0 means uniform random matrices)
    Random { rank: usize },
    /// f(v) = E_11 on the side S of a cut
    Cut(Vec<bool>),
    Given(Vec<u64>),
}

pub fn make_init(init: &Init, n: usize, mu: usize, seed: u64) -> Vec<u64> {
    let mut rng = SmallRng::seed_from_u64(seed ^ 0xabcdef);
    match init {
        Init::Random { rank } => (0..n)
            .map(|_| if *rank == 0 { f2::random_matrix(&mut rng, mu) } else { f2::random_rank_le(&mut rng, mu, *rank) })
            .collect(),
        Init::Cut(s) => s.iter().map(|&b| if b { 1u64 } else { 0 }).collect(),
        Init::Given(f) => f.clone(),
    }
}

/// Independent chains in parallel; inits[c % inits.len()] for chain c. Sorted by value, best first.
pub fn run_chains(g: &Graph, mu: usize, obj: Objective, opts: &Opts, inits: &[Init], chains: usize) -> Vec<ChainResult> {
    let mut res: Vec<ChainResult> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut o = opts.clone();
            o.seed = opts.seed.wrapping_mul(1_000_003).wrapping_add(c as u64);
            let f0 = make_init(&inits[c % inits.len()], g.n, mu, o.seed);
            let mut r = anneal(g, mu, obj, &o, f0);
            r.init = c % inits.len();
            r
        })
        .collect();
    res.sort_by(|a, b| b.value.partial_cmp(&a.value).unwrap_or(std::cmp::Ordering::Equal));
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rankplace::graph::*;
    #[test]
    fn incremental_totals_are_exact() {
        let g = random_regular(40, 4, 1);
        for (obj, maxr) in [(Objective::Ratio, None), (Objective::Lagrange(1.2), None), (Objective::Pairs, Some(2))] {
            for mu in [2, 4, 8] {
                let opts = Opts { iters: 20000, max_edge_rank: maxr, p_moves: [0.2, 0.2, 0.2, 0.3, 0.05, 0.05], ..Default::default() };
                let f0 = if maxr.is_some() { vec![0; g.n] } else { make_init(&Init::Random { rank: 1 }, g.n, mu, 3) };
                let r = anneal(&g, mu, obj, &opts, f0);
                let (ratio, ep, ee) = evaluate(&g, &r.f);
                assert!((ep - r.epairs).abs() < 1e-12 && (ee - r.eedges).abs() < 1e-12, "{obj:?} {mu}");
                if r.eedges > 0.0 {
                    assert!((ratio - r.ratio).abs() < 1e-9);
                }
                if let Some(m) = maxr {
                    assert!(max_edge_rank(&g, &r.f) <= m);
                }
            }
        }
    }
    #[test]
    fn finds_cut_value_on_petersen() {
        let g = named("petersen").unwrap();
        let res = run_chains(&g, 2, Objective::Ratio, &Opts { iters: 100_000, ..Default::default() }, &[Init::Random { rank: 1 }], 4);
        assert!(res[0].ratio >= 1.5 - 1e-9, "{}", res[0].ratio);
    }
}
