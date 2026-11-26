//! piecefloor: the price method for pieces (research/vpvnp/b2 §1, research/ports/c1d1 spec S3).
//!
//! A *design* has nodes, weighted edges (each edge has two legs, one at each end) and p merges
//! (partitions of the nodes into groups; one hub per group). A *placement* puts every leg and every
//! hub at a point of a metric space. For merge m:
//!
//!   b_m = (L - H_m) / delta_m,   L = sum_e w_e |leg_u(e) leg_v(e)|,
//!   H_m = sum_e w_e (|leg_u(e), hub_m(u)| + |leg_v(e), hub_m(v)|),  delta_m = max hub-hub distance of m.
//!
//! (delta_m = 0 gives L <= H_m by the triangle inequality, and we set b_m = 0.) A price yields one piece
//! with c_m >= b_m lambda - o(lambda) for every m at once; the adversary mixes pieces, so the floor is
//! max over convex combinations of the (clipped) b-vectors of min_m. For designs whose automorphisms act
//! transitively on the merges (all designs below) this equals max over placements of
//! **value = (sum_m max(0, b_m)) / p**, which is the quantity maximised here. LARGER is a STRONGER lower
//! bound on the cost of the best piece, i.e. a HIGHER floor for the level factor rho = value / sum_e w_e.
//!
//! Spaces: Mat_mu(F_2) with sqrt(rank(a - b)) (mu <= 8, bit-packed as in `rankplace::f2`), Euclidean
//! R^k, and l2 products of spiders (star trees with A arms; A = 3 is the tripod) with R^k.
//!
//! - [`Design`]: crossing (two wires, two merges), K4 = AG(2,2) with its three parallel classes
//!   (all six edges; each edge is internal to one merge), Delta_3 (anti-diagonal-class edges of the
//!   3 x 3 grid, merges rows / columns / diagonals, or only rows / columns).
//! - [`MatSpace`]: point tables for mu <= 3, exact leg optimisation for given hubs
//!   ([`MatSpace::best_legs`], decouples over edges), exhaustive enumeration of hub placements up to
//!   the isometry group a -> alpha a beta + c, a -> a^T ([`exhaustive_hubs`]).
//! - [`anneal_mat`]: parallel simulated annealing over full placements in Mat_mu(F_2), mu <= 8, with
//!   coordinatewise exhaustive polishing of legs (mu <= 4) and exact legs (mu <= 3).
//! - [`Model`] / [`anneal_model`]: the same objective in spider^j x R^k.

use crate::rankplace::f2;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rayon::prelude::*;
use std::collections::HashSet;

// ------------------------------------------------------------------------------------ designs

#[derive(Clone, Debug)]
pub struct Design {
    pub name: String,
    pub nnodes: usize,
    pub edges: Vec<(usize, usize)>,
    pub weights: Vec<f64>,
    /// groups[m][node] = group of node under merge m
    pub groups: Vec<Vec<usize>>,
    pub ngroups: Vec<usize>,
    hub_off: Vec<usize>,
}

impl Design {
    pub fn new(name: &str, nnodes: usize, edges: Vec<(usize, usize)>, weights: Vec<f64>, groups: Vec<Vec<usize>>) -> Self {
        let ngroups: Vec<usize> = groups.iter().map(|g| g.iter().max().unwrap() + 1).collect();
        let mut hub_off = vec![];
        let mut o = 2 * edges.len();
        for &r in &ngroups {
            hub_off.push(o);
            o += r;
        }
        Design { name: name.into(), nnodes, edges, weights, groups, ngroups, hub_off }
    }
    /// Rectangle crossing: wires x-v (weight l1) and y-u (weight l2); rows {x,y}|{u,v}, columns {x,u}|{y,v}.
    /// Nodes x,y,u,v = 0,1,2,3.
    pub fn crossing(l1: f64, l2: f64) -> Self {
        Design::new("crossing", 4, vec![(0, 3), (1, 2)], vec![l1, l2], vec![vec![0, 0, 1, 1], vec![0, 1, 0, 1]])
    }
    /// K4 = AG(2,2), all 6 edges, merges = the three parallel classes (= the three perfect matchings);
    /// node (a,b) = 2a+b, groups by the functionals a, b, a+b.
    pub fn k4() -> Self {
        let mut edges = vec![];
        for i in 0..4 {
            for j in i + 1..4 {
                edges.push((i, j));
            }
        }
        let f = |k: usize, v: usize| {
            let (a, b) = (v >> 1, v & 1);
            match k {
                0 => a,
                1 => b,
                _ => a ^ b,
            }
        };
        let groups = (0..3).map(|k| (0..4).map(|v| f(k, v)).collect()).collect();
        Design::new("K4", 4, edges, vec![1.0; 6], groups)
    }
    /// Delta_3: nodes (r,c) = 3r+c of the 3x3 grid, edges between nodes of the same anti-diagonal
    /// class (r+c mod 3) (9 edges, 18 legs), merges rows, columns, diagonals (r-c mod 3); `p` = 2 keeps
    /// rows and columns only. Edge and leg order as in research/vpvnp/b2/*.py.
    pub fn delta3(p: usize) -> Self {
        let nodes: Vec<(usize, usize)> = (0..3).flat_map(|r| (0..3).map(move |c| (r, c))).collect();
        let mut edges = vec![];
        for (i, &(r, c)) in nodes.iter().enumerate() {
            for (j, &(r2, c2)) in nodes.iter().enumerate() {
                if i < j && (r + c) % 3 == (r2 + c2) % 3 {
                    edges.push((i, j));
                }
            }
        }
        let mf = |k: usize, (r, c): (usize, usize)| match k {
            0 => r,
            1 => c,
            _ => (r + 3 - c) % 3,
        };
        let groups = (0..p).map(|k| nodes.iter().map(|&v| mf(k, v)).collect()).collect();
        Design::new(if p == 3 { "Delta3" } else { "Delta3-2merge" }, 9, edges, vec![1.0; 9], groups)
    }
    /// Full affine plane AG(2,q), q in {2,3,4,5,7}: nodes (x,y) = q*x+y, ALL C(q^2,2) edges (edges inside a
    /// merge class are internal to that merge), merges = the parallel classes listed in `classes`:
    /// class 0: lines x = c, class 1: y = c, class s >= 2: y + (s-1) x = c (GF(q) arithmetic; GF(4) as
    /// F_2[w]/(w^2+w+1)). For p = 3 at q = 4, 5 the third class is a Latin square.
    pub fn ag(q: usize, classes: &[usize]) -> Self {
        let add = |a: usize, b: usize| if q == 4 { a ^ b } else { (a + b) % q };
        let mul = |a: usize, b: usize| {
            if q == 4 {
                const T: [[usize; 4]; 4] = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]];
                T[a][b]
            } else {
                (a * b) % q
            }
        };
        let f = |s: usize, v: usize| {
            let (x, y) = (v / q, v % q);
            match s {
                0 => x,
                1 => y,
                _ => add(y, mul(s - 1, x)),
            }
        };
        let mut edges = vec![];
        for i in 0..q * q {
            for j in i + 1..q * q {
                edges.push((i, j));
            }
        }
        let groups = classes.iter().map(|&c| (0..q * q).map(|v| f(c, v)).collect()).collect();
        let ne = edges.len();
        Design::new(&format!("AG2-{}-p{}", q, classes.len()), q * q, edges, vec![1.0; ne], groups)
    }
    /// Full 3-net of a finite abelian group Q: nodes (r,c) in Q^2, all edges, merges r, c, r - c.
    pub fn group_net(qname: &str) -> Self {
        let q = QGroup::new(qname);
        let m = q.m;
        let mut edges = vec![];
        for i in 0..m * m {
            for j in i + 1..m * m {
                edges.push((i, j));
            }
        }
        let funcs = [(1, 0), (0, 1), (1, -1)];
        let groups = funcs.iter().map(|&(a, b)| (0..m * m).map(|v| q.lin(a, b, v / m, v % m)).collect()).collect();
        let ne = edges.len();
        Design::new(&format!("net-{}", qname), m * m, edges, vec![1.0; ne], groups)
    }
    pub fn by_name(name: &str) -> Option<Self> {
        if let Some(rest) = name.strip_prefix("net-") {
            return Some(Self::group_net(rest));
        }
        if let Some(rest) = name.strip_prefix("ag") {
            // agQ-P : AG(2,Q) with the first P classes
            let v: Vec<usize> = rest.split('-').map(|x| x.parse().unwrap()).collect();
            let classes: Vec<usize> = (0..v[1]).collect();
            return Some(Self::ag(v[0], &classes));
        }
        match name {
            "crossing" => Some(Self::crossing(1.0, 1.0)),
            "crossing-half" => Some(Design { name: name.into(), ..Self::crossing(1.0, 0.5) }),
            "crossing-tenth" => Some(Design { name: name.into(), ..Self::crossing(1.0, 0.1) }),
            "k4" | "K4" => Some(Self::k4()),
            "delta3" | "Delta3" => Some(Self::delta3(3)),
            "delta3-2" => Some(Self::delta3(2)),
            _ => None,
        }
    }
    pub fn p(&self) -> usize {
        self.groups.len()
    }
    pub fn nlegs(&self) -> usize {
        2 * self.edges.len()
    }
    pub fn nhubs(&self) -> usize {
        self.ngroups.iter().sum()
    }
    pub fn npoints(&self) -> usize {
        self.nlegs() + self.nhubs()
    }
    /// point index of the hub of group g of merge m
    #[inline]
    pub fn hub(&self, m: usize, g: usize) -> usize {
        self.hub_off[m] + g
    }
    #[inline]
    pub fn leg_node(&self, l: usize) -> usize {
        let (u, v) = self.edges[l / 2];
        if l % 2 == 0 {
            u
        } else {
            v
        }
    }
    pub fn total_weight(&self) -> f64 {
        self.weights.iter().sum()
    }
    /// The flat (Euclidean far-leg) value of the orthogonal-simplex price: per merge,
    /// (1/p) sum_e w_e |sum_k Delta^k_e| with |Delta^k_e| = 1 if e crosses k, else 0.
    pub fn flat_value(&self) -> f64 {
        let p = self.p() as f64;
        let s: f64 = self
            .edges
            .iter()
            .zip(&self.weights)
            .map(|(&(u, v), w)| w * (self.groups.iter().filter(|g| g[u] != g[v]).count() as f64).sqrt())
            .sum();
        s / p
    }
    /// b-vector for a distance function on point indices.
    pub fn bvec<F: Fn(usize, usize) -> f64>(&self, d: F) -> Vec<f64> {
        let mut l = 0.0;
        let mut h = vec![0.0; self.p()];
        for (e, &(u, v)) in self.edges.iter().enumerate() {
            let w = self.weights[e];
            l += w * d(2 * e, 2 * e + 1);
            for m in 0..self.p() {
                h[m] += w * (d(2 * e, self.hub(m, self.groups[m][u])) + d(2 * e + 1, self.hub(m, self.groups[m][v])));
            }
        }
        (0..self.p())
            .map(|m| {
                let mut dm: f64 = 0.0;
                for g in 0..self.ngroups[m] {
                    for g2 in g + 1..self.ngroups[m] {
                        dm = dm.max(d(self.hub(m, g), self.hub(m, g2)));
                    }
                }
                // guard against cancellation: L and H_m are sums of distances of size up to L, so
                // (L - H_m) has absolute error ~ 1e-15 L; require delta_m >= 1e-7 * L / E
                if dm <= 1e-12 || dm < 1e-7 * l / self.edges.len() as f64 {
                    0.0
                } else {
                    (l - h[m]) / dm
                }
            })
            .collect()
    }
}

/// (sum_m max(0, b_m)) / p.
pub fn value(b: &[f64]) -> f64 {
    b.iter().map(|x| x.max(0.0)).sum::<f64>() / b.len() as f64
}

// ------------------------------------------------------------------------------------ Mat_mu(F_2)

/// sqrt(r) for r = 0..=8
pub const SQ: [f64; 9] = [0.0, 1.0, 1.4142135623730951, 1.7320508075688772, 2.0, 2.23606797749979, 2.449489742783178, 2.6457513110645907, 2.8284271247461903];

#[inline]
pub fn mdist(a: u64, b: u64) -> f64 {
    SQ[f2::rank(a ^ b) as usize]
}

/// Matrix with index i (row r = bits mu*r .. mu*r+mu-1 of i).
pub fn idx2mat(i: usize, mu: usize) -> u64 {
    let mask = (1usize << mu) - 1;
    (0..mu).fold(0u64, |a, r| a | ((((i >> (mu * r)) & mask) as u64) << (8 * r)))
}
pub fn mat2idx(a: u64, mu: usize) -> usize {
    (0..mu).fold(0usize, |s, r| s | ((((a >> (8 * r)) & 0xFF) as usize) << (mu * r)))
}

pub fn b_mat(d: &Design, pts: &[u64]) -> Vec<f64> {
    d.bvec(|i, j| mdist(pts[i], pts[j]))
}

/// Enumerated Mat_mu(F_2) for mu <= 3 with the full distance table.
pub struct MatSpace {
    pub mu: usize,
    pub n: usize,
    pub mats: Vec<u64>,
    pub dist: Vec<f64>,
}

impl MatSpace {
    pub fn new(mu: usize) -> Self {
        assert!(mu <= 3);
        let n = 1usize << (mu * mu);
        let mats: Vec<u64> = (0..n).map(|i| idx2mat(i, mu)).collect();
        let mut dist = vec![0.0; n * n];
        for i in 0..n {
            for j in 0..n {
                dist[i * n + j] = mdist(mats[i], mats[j]);
            }
        }
        MatSpace { mu, n, mats, dist }
    }
    #[inline]
    pub fn d(&self, i: usize, j: usize) -> f64 {
        self.dist[i * self.n + j]
    }
    /// Exact optimum over all leg positions for hubs at point indices `hubs` (in hub order of the
    /// design): max over nonempty S of sum_{m in S} b_m, which decouples over edges:
    /// sum_e w_e max_{x,y} [W |xy| - c_u(x) - c_v(y)], W = sum_{m in S} 1/delta_m,
    /// c_u(x) = sum_{m in S} |x, hub_m(u)| / delta_m. Returns (sum_m b_m^+ = p*value, S mask, legs).
    pub fn best_legs(&self, des: &Design, hubs: &[usize], want_legs: bool, scratch: &mut Vec<f64>) -> (f64, u32, Vec<usize>) {
        let p = des.p();
        let n = self.n;
        let nl = des.nlegs();
        let hb = |m: usize, g: usize| hubs[des.hub(m, g) - nl];
        let mut inv = vec![0.0; p];
        for m in 0..p {
            let mut dm: f64 = 0.0;
            for g in 0..des.ngroups[m] {
                for g2 in g + 1..des.ngroups[m] {
                    dm = dm.max(self.d(hb(m, g), hb(m, g2)));
                }
            }
            inv[m] = if dm > 1e-12 { 1.0 / dm } else { 0.0 };
        }
        let nn = des.nnodes;
        scratch.resize(nn * n, 0.0);
        let mut best = (0.0f64, 0u32);
        for s in 1u32..(1u32 << p) {
            if (0..p).any(|m| (s >> m) & 1 == 1 && inv[m] == 0.0) {
                continue;
            }
            let wsum: f64 = (0..p).filter(|m| (s >> m) & 1 == 1).map(|m| inv[m]).sum();
            for u in 0..nn {
                let c = &mut scratch[u * n..(u + 1) * n];
                for x in c.iter_mut() {
                    *x = 0.0;
                }
                for m in 0..p {
                    if (s >> m) & 1 == 1 {
                        let h = hb(m, des.groups[m][u]);
                        let row = &self.dist[h * n..(h + 1) * n];
                        for x in 0..n {
                            c[x] += inv[m] * row[x];
                        }
                    }
                }
            }
            let mut tot = 0.0;
            for (e, &(u, v)) in des.edges.iter().enumerate() {
                let cu = &scratch[u * n..(u + 1) * n];
                let cv = &scratch[v * n..(v + 1) * n];
                let mut bx = f64::NEG_INFINITY;
                for x in 0..n {
                    let row = &self.dist[x * n..(x + 1) * n];
                    let mut by = f64::NEG_INFINITY;
                    for y in 0..n {
                        let t = wsum * row[y] - cv[y];
                        if t > by {
                            by = t;
                        }
                    }
                    let t = by - cu[x];
                    if t > bx {
                        bx = t;
                    }
                }
                tot += des.weights[e] * bx;
            }
            if tot > best.0 + 1e-12 {
                best = (tot, s);
            }
        }
        let mut legs = vec![];
        if want_legs && best.1 != 0 {
            legs = self.legs_for(des, hubs, best.1, &inv);
        }
        (best.0, best.1, legs)
    }
    fn legs_for(&self, des: &Design, hubs: &[usize], s: u32, inv: &[f64]) -> Vec<usize> {
        let n = self.n;
        let p = des.p();
        let nl = des.nlegs();
        let hb = |m: usize, g: usize| hubs[des.hub(m, g) - nl];
        let wsum: f64 = (0..p).filter(|m| (s >> m) & 1 == 1).map(|m| inv[m]).sum();
        let cost = |u: usize, x: usize| -> f64 {
            (0..p).filter(|m| (s >> m) & 1 == 1).map(|m| inv[m] * self.d(x, hb(m, des.groups[m][u]))).sum()
        };
        let mut legs = vec![0; nl];
        for (e, &(u, v)) in des.edges.iter().enumerate() {
            let mut b = (f64::NEG_INFINITY, 0, 0);
            for x in 0..n {
                for y in 0..n {
                    let t = wsum * self.d(x, y) - cost(u, x) - cost(v, y);
                    if t > b.0 + 1e-12 {
                        b = (t, x, y);
                    }
                }
            }
            legs[2 * e] = b.1;
            legs[2 * e + 1] = b.2;
        }
        legs
    }
}

/// Invertible mu x mu matrices over F_2.
pub fn gl(mu: usize) -> Vec<u64> {
    (0..1usize << (mu * mu)).map(|i| idx2mat(i, mu)).filter(|&a| f2::rank(a) as usize == mu).collect()
}

/// The linear isometries a -> alpha a beta, a -> alpha a^T beta of Mat_mu(F_2), as permutations of
/// point indices (deduplicated). Together with translations they generate the isometry group used
/// for orbit reduction (sufficient for correctness: any subgroup gives a valid reduction).
pub fn linear_isometries(mu: usize) -> Vec<Vec<u16>> {
    let g = gl(mu);
    let n = 1usize << (mu * mu);
    let mut set = HashSet::new();
    let mut out = vec![];
    for &a in &g {
        for &b in &g {
            for t in [false, true] {
                let perm: Vec<u16> = (0..n)
                    .map(|i| {
                        let x = idx2mat(i, mu);
                        let x = if t { f2::transpose(x, mu) } else { x };
                        mat2idx(f2::mul(f2::mul(a, x), b), mu) as u16
                    })
                    .collect();
                if set.insert(perm.clone()) {
                    out.push(perm);
                }
            }
        }
    }
    out
}

#[derive(Clone, Debug)]
pub struct ExhaustiveResult {
    pub best: f64,
    pub hubs: Vec<usize>,
    pub legs: Vec<usize>,
    pub subset: u32,
    pub leaves: u64,
    /// histogram of p*value rounded to 1e-6, top entries (value, count of hub orbits)
    pub top: Vec<(f64, u64)>,
}

/// Exhaustive search over all hub placements in Mat_mu(F_2) (mu <= 3) up to the isometry group
/// (first hub at 0 by translation, then lex-min canonical tuples under the linear isometries),
/// with exact leg optimisation for each. Optionally hubs restricted to the first `hub_pts` point
/// indices (e.g. 16 = Mat_2 embedded in the top-left block of Mat_3; then the group used is the
/// one of Mat_2 acting blockwise, passed in `group`).
pub fn exhaustive_hubs(des: &Design, sp: &MatSpace, group: &[Vec<u16>], hub_pts: usize, split_depth: usize) -> ExhaustiveResult {
    let map: Vec<usize> = (0..hub_pts).collect();
    exhaustive_hubs_map(des, sp, group, &map, split_depth)
}

/// Hubs restricted to Mat_2 embedded in the top-left block of Mat_3 (legs anywhere in Mat_3);
/// orbit reduction by the isometries of Mat_2 (which extend blockwise to Mat_3).
pub fn exhaustive_hubs_sub(des: &Design, sp: &MatSpace, group2: &[Vec<u16>], split_depth: usize) -> ExhaustiveResult {
    assert_eq!(sp.mu, 3);
    let map: Vec<usize> = (0..16).map(|i| mat2idx(idx2mat(i, 2), 3)).collect();
    exhaustive_hubs_map(des, sp, group2, &map, split_depth)
}

/// General form: hub labels 0..map.len() (acted on by `group`, label 0 fixed by every element and
/// the group transitive modulo translations, so the first hub may be put at label 0), label i placed at
/// point index map[i] of `sp`. Returned hubs are point indices of `sp`.
pub fn exhaustive_hubs_map(des: &Design, sp: &MatSpace, group: &[Vec<u16>], map: &[usize], split_depth: usize) -> ExhaustiveResult {
    let hub_pts = map.len();
    let nh = des.nhubs();
    // canonical prefixes up to split_depth, with stabilisers
    let mut prefixes: Vec<(Vec<usize>, Vec<u32>)> = vec![(vec![0], (0..group.len() as u32).collect())];
    for _ in 1..split_depth.min(nh) {
        let mut next = vec![];
        for (pre, stab) in &prefixes {
            for p in 0..hub_pts {
                if let Some(st) = extend(group, stab, p) {
                    let mut q = pre.clone();
                    q.push(p);
                    next.push((q, st));
                }
            }
        }
        prefixes = next;
    }
    let results: Vec<(f64, Vec<usize>, u64, Vec<(i64, u64)>)> = prefixes
        .par_iter()
        .map(|(pre, stab)| {
            let mut scratch = vec![];
            let mut hubs = pre.clone();
            hubs.resize(nh, 0);
            let mut best = (f64::NEG_INFINITY, vec![]);
            let mut leaves = 0u64;
            let mut hist: std::collections::HashMap<i64, u64> = Default::default();
            dfs(des, sp, group, map, &mut hubs, pre.len(), stab, &mut scratch, &mut best, &mut leaves, &mut hist);
            let mut h: Vec<(i64, u64)> = hist.into_iter().collect();
            h.sort_by(|a, b| b.0.cmp(&a.0));
            h.truncate(20);
            (best.0, best.1, leaves, h)
        })
        .collect();
    let mut best = (f64::NEG_INFINITY, vec![]);
    let mut leaves = 0;
    let mut hist: std::collections::HashMap<i64, u64> = Default::default();
    for (v, h, l, hh) in results {
        leaves += l;
        if v > best.0 + 1e-12 {
            best = (v, h);
        }
        for (k, c) in hh {
            *hist.entry(k).or_insert(0) += c;
        }
    }
    let mut top: Vec<(i64, u64)> = hist.into_iter().collect();
    top.sort_by(|a, b| b.0.cmp(&a.0));
    top.truncate(10);
    let mut scratch = vec![];
    let best_hubs: Vec<usize> = best.1.iter().map(|&h| map[h]).collect();
    let (v, s, legs) = sp.best_legs(des, &best_hubs, true, &mut scratch);
    assert!((v - best.0).abs() < 1e-9);
    ExhaustiveResult { best: best.0, hubs: best_hubs, legs, subset: s, leaves, top: top.into_iter().map(|(k, c)| (k as f64 * 1e-6, c)).collect() }
}

#[inline]
fn extend(group: &[Vec<u16>], stab: &[u32], p: usize) -> Option<Vec<u32>> {
    let mut st = Vec::with_capacity(stab.len());
    for &g in stab {
        let q = group[g as usize][p] as usize;
        if q < p {
            return None;
        }
        if q == p {
            st.push(g);
        }
    }
    Some(st)
}

#[allow(clippy::too_many_arguments)]
fn dfs(des: &Design, sp: &MatSpace, group: &[Vec<u16>], map: &[usize], hubs: &mut Vec<usize>, k: usize, stab: &[u32],
       scratch: &mut Vec<f64>, best: &mut (f64, Vec<usize>), leaves: &mut u64, hist: &mut std::collections::HashMap<i64, u64>) {
    let hub_pts = map.len();
    if k == hubs.len() {
        *leaves += 1;
        let mapped: Vec<usize> = hubs.iter().map(|&h| map[h]).collect();
        let (v, _, _) = sp.best_legs(des, &mapped, false, scratch);
        *hist.entry((v * 1e6).round() as i64).or_insert(0) += 1;
        if v > best.0 + 1e-12 {
            *best = (v, hubs.clone());
        }
        return;
    }
    for p in 0..hub_pts {
        if let Some(st) = extend(group, stab, p) {
            hubs[k] = p;
            dfs(des, sp, group, map, hubs, k + 1, &st, scratch, best, leaves, hist);
        }
    }
}

// ------------------------------------------------------------------------------------ annealing in Mat_mu

#[derive(Clone, Debug)]
pub struct AnnealOpts {
    pub iters: usize,
    pub chains: usize,
    pub t0: f64,
    pub t1: f64,
    pub seed: u64,
    /// polish legs coordinatewise over all of Mat_mu (only mu <= 4)
    pub polish: bool,
}

#[derive(Clone, Debug)]
pub struct MatSolution {
    pub value: f64,
    pub b: Vec<f64>,
    pub pts: Vec<u64>,
    pub chain: usize,
}

fn random_point<R: Rng>(rng: &mut R, mu: usize) -> u64 {
    match rng.gen_range(0..3) {
        0 => f2::random_matrix(rng, mu),
        1 => f2::random_rank_le(rng, mu, 1),
        _ => f2::random_rank_le(rng, mu, 2),
    }
}

/// Simulated annealing over placements in Mat_mu(F_2) of all legs and hubs, objective
/// sum_m b_m^+ (scale-free). Moves: add a rank-one matrix to a point; copy another point; move a
/// point to a random point. Returns the best solution of each chain, sorted (best first).
pub fn anneal_mat(des: &Design, mu: usize, o: &AnnealOpts) -> Vec<MatSolution> {
    let np = des.npoints();
    let mut sols: Vec<MatSolution> = (0..o.chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(o.seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (c as u64 + 1).wrapping_mul(0xBF58_476D_1CE4_E5B9));
            let mut pts: Vec<u64> = (0..np).map(|_| random_point(&mut rng, mu)).collect();
            let f = |pts: &[u64]| value(&b_mat(des, pts));
            let mut cur = f(&pts);
            let mut best = (cur, pts.clone());
            for it in 0..o.iters {
                let frac = it as f64 / o.iters as f64;
                let t = o.t0 * (o.t1 / o.t0).powf(frac);
                let i = rng.gen_range(0..np);
                let old = pts[i];
                let mv = rng.gen_range(0..10);
                pts[i] = if mv < 6 {
                    old ^ f2::random_rank_one(&mut rng, mu)
                } else if mv < 8 {
                    pts[rng.gen_range(0..np)]
                } else {
                    random_point(&mut rng, mu)
                };
                let v = f(&pts);
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    if v > best.0 + 1e-12 {
                        best = (v, pts.clone());
                    }
                } else {
                    pts[i] = old;
                }
            }
            let mut pts = best.1;
            if o.polish && mu <= 4 {
                polish_mat(des, mu, &mut pts);
            }
            let b = b_mat(des, &pts);
            MatSolution { value: value(&b), b, pts, chain: c }
        })
        .collect();
    sols.sort_by(|a, b| b.value.partial_cmp(&a.value).unwrap());
    sols
}

/// Coordinatewise exhaustive ascent: each point in turn moved to the best point of Mat_mu
/// (mu <= 4), until no improvement.
pub fn polish_mat(des: &Design, mu: usize, pts: &mut [u64]) {
    let n = 1usize << (mu * mu);
    let mut cur = value(&b_mat(des, pts));
    loop {
        let mut improved = false;
        for i in 0..pts.len() {
            let old = pts[i];
            let mut bestp = (cur, old);
            for x in 0..n {
                pts[i] = idx2mat(x, mu);
                let v = value(&b_mat(des, pts));
                if v > bestp.0 + 1e-12 {
                    bestp = (v, pts[i]);
                }
            }
            pts[i] = bestp.1;
            if bestp.0 > cur + 1e-12 {
                cur = bestp.0;
                improved = true;
            }
        }
        if !improved {
            break;
        }
    }
}

/// Hub annealing with exact legs (mu <= 3): state = hub indices, objective = best_legs value.
pub fn anneal_hubs_exact(des: &Design, sp: &MatSpace, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64,
                         starts: Option<Vec<Vec<usize>>>) -> Vec<(f64, Vec<usize>, Vec<usize>)> {
    let nh = des.nhubs();
    let mut out: Vec<(f64, Vec<usize>, Vec<usize>)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 7).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut scratch = vec![];
            let mut hubs: Vec<usize> = match &starts {
                Some(s) => s[c % s.len()].clone(),
                None => (0..nh).map(|_| mat2idx(random_point(&mut rng, sp.mu), sp.mu)).collect(),
            };
            let mut cur = sp.best_legs(des, &hubs, false, &mut scratch).0;
            let mut best = (cur, hubs.clone());
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters.max(1) as f64);
                let i = rng.gen_range(0..nh);
                let old = hubs[i];
                let mv = rng.gen_range(0..10);
                hubs[i] = if mv < 6 {
                    mat2idx(sp.mats[old] ^ f2::random_rank_one(&mut rng, sp.mu), sp.mu)
                } else if mv < 8 {
                    hubs[rng.gen_range(0..nh)]
                } else {
                    rng.gen_range(0..sp.n)
                };
                let v = sp.best_legs(des, &hubs, false, &mut scratch).0;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    if v > best.0 + 1e-12 {
                        best = (v, hubs.clone());
                    }
                } else {
                    hubs[i] = old;
                }
            }
            let (v, _, legs) = sp.best_legs(des, &best.1, true, &mut scratch);
            (v, best.1, legs)
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

// ------------------------------------------------------------------------------------ continuous models

pub const MAXF: usize = 9;
pub const MAXK: usize = 8;

/// l2 product of spiders (arms[f] arms each; a point is (arm, radius) per spider) and R^k.
#[derive(Clone, Debug)]
pub struct Model {
    pub arms: Vec<usize>,
    pub k: usize,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CPoint {
    pub arm: [u8; MAXF],
    pub t: [f64; MAXF],
    pub x: [f64; MAXK],
}

impl Model {
    pub fn label(&self) -> String {
        let mut s: Vec<String> = self.arms.iter().map(|a| if *a == 3 { "tripod".into() } else { format!("spider{}", a) }).collect();
        if self.k > 0 {
            s.push(format!("R^{}", self.k));
        }
        s.join(" x ")
    }
    #[inline]
    pub fn dist(&self, p: &CPoint, q: &CPoint) -> f64 {
        let mut s = 0.0;
        for f in 0..self.arms.len() {
            let d = if p.arm[f] == q.arm[f] { (p.t[f] - q.t[f]).abs() } else { p.t[f] + q.t[f] };
            s += d * d;
        }
        for c in 0..self.k {
            let d = p.x[c] - q.x[c];
            s += d * d;
        }
        s.sqrt()
    }
    fn random_point<R: Rng>(&self, rng: &mut R, scale: f64) -> CPoint {
        let mut p = CPoint::default();
        for f in 0..self.arms.len() {
            p.arm[f] = rng.gen_range(0..self.arms[f]) as u8;
            p.t[f] = rng.gen::<f64>() * scale;
        }
        for c in 0..self.k {
            p.x[c] = (rng.gen::<f64>() * 2.0 - 1.0) * scale;
        }
        p
    }
    pub fn b(&self, des: &Design, pts: &[CPoint]) -> Vec<f64> {
        des.bvec(|i, j| self.dist(&pts[i], &pts[j]))
    }
}

#[derive(Clone, Debug)]
pub struct ModelSolution {
    pub value: f64,
    pub b: Vec<f64>,
    pub pts: Vec<CPoint>,
}

fn gauss<R: Rng>(rng: &mut R) -> f64 {
    let u: f64 = rng.gen::<f64>().max(1e-300);
    let v: f64 = rng.gen();
    (-2.0 * u.ln()).sqrt() * (2.0 * std::f64::consts::PI * v).cos()
}

/// Simulated annealing in a model space; objective sum_m b_m^+ (scale-free; the hub scale is
/// renormalised every 1000 steps so that the largest delta is 1). Moves: Gaussian kick of one point
/// (step size adapted to the acceptance rate), radial scaling of a point, arm change, copy.
pub fn anneal_model(des: &Design, model: &Model, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64) -> Vec<ModelSolution> {
    anneal_model_start(des, model, iters, chains, t0, t1, seed, None)
}

/// [`anneal_model`] with an optional start configuration (used by every chain; chains differ by seed).
/// Without a start the hub scale is renormalised during the run; with a start it is kept.
#[allow(clippy::too_many_arguments)]
pub fn anneal_model_start(des: &Design, model: &Model, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64,
                          start: Option<&[CPoint]>) -> Vec<ModelSolution> {
    let np = des.npoints();
    let nl = des.nlegs();
    let mut sols: Vec<ModelSolution> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 11).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut pts: Vec<CPoint> = match start {
                Some(s) => s.to_vec(),
                None => (0..np).map(|i| model.random_point(&mut rng, if i < nl { 3.0 } else { 1.0 })).collect(),
            };
            let f = |pts: &[CPoint]| value(&model.b(des, pts));
            let mut cur = f(&pts);
            let mut best = (cur, pts.clone());
            let mut sigma = 0.3;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64);
                let i = rng.gen_range(0..np);
                let old = pts[i];
                let mv = rng.gen_range(0..20);
                let mut p = old;
                if mv < 14 {
                    let norm = 1.0 + if i < nl { 0.3 * (p.t.iter().map(|x| x * x).sum::<f64>() + p.x.iter().map(|x| x * x).sum::<f64>()).sqrt() } else { 0.0 };
                    for f in 0..model.arms.len() {
                        p.t[f] = (p.t[f] + sigma * norm * gauss(&mut rng)).max(0.0);
                    }
                    for cc in 0..model.k {
                        p.x[cc] += sigma * norm * gauss(&mut rng);
                    }
                } else if mv < 16 {
                    let s = (0.3 * gauss(&mut rng)).exp();
                    for f in 0..model.arms.len() {
                        p.t[f] *= s;
                    }
                    for cc in 0..model.k {
                        p.x[cc] *= s;
                    }
                } else if mv < 18 && !model.arms.is_empty() {
                    let f = rng.gen_range(0..model.arms.len());
                    p.arm[f] = rng.gen_range(0..model.arms[f]) as u8;
                } else {
                    p = pts[rng.gen_range(0..np)];
                }
                pts[i] = p;
                let v = f(&pts);
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, pts.clone());
                    }
                } else {
                    pts[i] = old;
                }
                if tried == 1000 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.3 } else { 0.77 };
                    sigma = sigma.clamp(1e-7, 10.0);
                    acc = 0;
                    tried = 0;
                    // renormalise scale: largest delta -> 1 (everything is homogeneous)
                    let mut dm: f64 = 0.0;
                    for m in 0..des.p() {
                        for g in 0..des.ngroups[m] {
                            for g2 in g + 1..des.ngroups[m] {
                                dm = dm.max(model.dist(&pts[des.hub(m, g)], &pts[des.hub(m, g2)]));
                            }
                        }
                    }
                    if start.is_none() && dm > 1e-9 && it < iters - 1000 {
                        for q in pts.iter_mut() {
                            for f in 0..model.arms.len() {
                                q.t[f] /= dm;
                            }
                            for cc in 0..model.k {
                                q.x[cc] /= dm;
                            }
                        }
                    }
                }
            }
            let b = model.b(des, &best.1);
            ModelSolution { value: value(&b), b, pts: best.1 }
        })
        .collect();
    sols.sort_by(|a, b| b.value.partial_cmp(&a.value).unwrap());
    sols
}

// ------------------------------------------------------------------------------------ far-leg limit

/// Far-leg (Busemann) limit in spider^j x R^k: the two legs of every edge are sent to infinity in
/// opposite directions of a geodesic line (Tits-antipodal boundary points), at distance M -> inf.
/// With hubs fixed, d(leg, h) = M + beta_xi(h) + o(1), so for a subset S of merges
///   sum_{m in S} b_m -> sum_e w_e max_{line} sum_{m in S} [-beta_{xi+}(h^m_u) - beta_{xi-}(h^m_v)] / delta_m.
/// A line in the product has unit coefficients (c_1..c_j, c_0 w) and in spider f an ordered pair of
/// distinct arms (a, a'); with g_a(b,t) = t if b = a else -t (minus the Busemann function of arm a) the
/// maximum over lines is sqrt(sum_f max(0, A_f)^2 + |B|^2),
///   A_f = max_{a != a'} sum_{m in S} [g_a(h^m_u) + g_a'(h^m_v)] / delta_m,  B = sum_{m in S} (x^m_u - x^m_v) / delta_m.
/// Returns (sum_m b_m^+ in the limit, i.e. p*value, best S). `hubs` in design hub order.
pub fn far_value(des: &Design, model: &Model, hubs: &[CPoint]) -> (f64, u32) {
    let p = des.p();
    let nl = des.nlegs();
    let hb = |m: usize, g: usize| &hubs[des.hub(m, g) - nl];
    let mut inv = vec![0.0; p];
    for m in 0..p {
        let mut dm: f64 = 0.0;
        for g in 0..des.ngroups[m] {
            for g2 in g + 1..des.ngroups[m] {
                dm = dm.max(model.dist(hb(m, g), hb(m, g2)));
            }
        }
        inv[m] = if dm > 1e-12 { 1.0 / dm } else { 0.0 };
    }
    let mut best = (0.0, 0u32);
    for s in 1u32..(1u32 << p) {
        if (0..p).any(|m| (s >> m) & 1 == 1 && inv[m] == 0.0) {
            continue;
        }
        let mut tot = 0.0;
        for (e, &(u, v)) in des.edges.iter().enumerate() {
            let mut sq = 0.0;
            for (f, &na) in model.arms.iter().enumerate() {
                let mut af = f64::NEG_INFINITY;
                for a in 0..na {
                    for a2 in 0..na {
                        if a == a2 {
                            continue;
                        }
                        let mut z = 0.0;
                        for m in 0..p {
                            if (s >> m) & 1 == 1 {
                                let hu = hb(m, des.groups[m][u]);
                                let hv = hb(m, des.groups[m][v]);
                                let gu = if hu.arm[f] as usize == a { hu.t[f] } else { -hu.t[f] };
                                let gv = if hv.arm[f] as usize == a2 { hv.t[f] } else { -hv.t[f] };
                                z += inv[m] * (gu + gv);
                            }
                        }
                        af = af.max(z);
                    }
                }
                if af > 0.0 {
                    sq += af * af;
                }
            }
            for c in 0..model.k {
                let mut z = 0.0;
                for m in 0..p {
                    if (s >> m) & 1 == 1 {
                        z += inv[m] * (hb(m, des.groups[m][u]).x[c] - hb(m, des.groups[m][v]).x[c]);
                    }
                }
                sq += z * z;
            }
            tot += des.weights[e] * sq.sqrt();
        }
        if tot > best.0 + 1e-12 {
            best = (tot, s);
        }
    }
    best
}

/// Annealing over hub positions for the far-leg limit (see [`far_value`]). Returns (value per merge,
/// hubs, S) per chain, best first.
pub fn anneal_far(des: &Design, model: &Model, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64) -> Vec<(f64, Vec<CPoint>, u32)> {
    let nh = des.nhubs();
    let p = des.p() as f64;
    let mut out: Vec<(f64, Vec<CPoint>, u32)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 13).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut hubs: Vec<CPoint> = (0..nh).map(|_| model.random_point(&mut rng, 1.0)).collect();
            let mut cur = far_value(des, model, &hubs).0;
            let mut best = (cur, hubs.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64);
                let i = rng.gen_range(0..nh);
                let old = hubs[i];
                let mut q = old;
                let mv = rng.gen_range(0..10);
                if mv < 7 {
                    for f in 0..model.arms.len() {
                        q.t[f] = (q.t[f] + sigma * gauss(&mut rng)).max(0.0);
                    }
                    for cc in 0..model.k {
                        q.x[cc] += sigma * gauss(&mut rng);
                    }
                } else if mv < 9 && !model.arms.is_empty() {
                    let f = rng.gen_range(0..model.arms.len());
                    q.arm[f] = rng.gen_range(0..model.arms[f]) as u8;
                } else {
                    q = hubs[rng.gen_range(0..nh)];
                }
                hubs[i] = q;
                let v = far_value(des, model, &hubs).0;
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, hubs.clone());
                    }
                } else {
                    hubs[i] = old;
                }
                if tried == 500 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-8, 5.0);
                    acc = 0;
                    tried = 0;
                }
            }
            let (v, s) = far_value(des, model, &best.1);
            (v / p, best.1, s)
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

// ------------------------------------------------------------------------------------ far-leg limit, general trees

/// One tree factor: vertices 0..n with parent pointers (vertex 0 is the root, parent[0] = 0), edge
/// lengths len[v] = |v, parent(v)|, and hub h at vertex hv[h]. Every vertex may carry extra rays (ends):
/// attaching rays keeps the space a tree, and the Busemann function of a ray attached at r is d(., r).
#[derive(Clone, Debug)]
pub struct TreeFactor {
    pub parent: Vec<usize>,
    pub len: Vec<f64>,
    pub hv: Vec<usize>,
    pub dist: Vec<f64>,
}

impl TreeFactor {
    pub fn n(&self) -> usize {
        self.parent.len()
    }
    pub fn recompute(&mut self) {
        let n = self.n();
        let mut adj = vec![vec![]; n];
        for v in 1..n {
            adj[v].push((self.parent[v], self.len[v]));
            adj[self.parent[v]].push((v, self.len[v]));
        }
        self.dist.resize(n * n, 0.0);
        let mut stack = vec![];
        for s in 0..n {
            let mut seen = vec![false; n];
            stack.clear();
            stack.push((s, 0.0));
            seen[s] = true;
            while let Some((v, d)) = stack.pop() {
                self.dist[s * n + v] = d;
                for &(w, l) in &adj[v] {
                    if !seen[w] {
                        seen[w] = true;
                        stack.push((w, d + l));
                    }
                }
            }
        }
    }
    fn is_ancestor(&self, a: usize, mut v: usize) -> bool {
        loop {
            if v == a {
                return true;
            }
            if v == 0 {
                return false;
            }
            v = self.parent[v];
        }
    }
    pub fn random<R: Rng>(rng: &mut R, n: usize, nh: usize) -> Self {
        let mut parent = vec![0; n];
        let mut len = vec![0.0; n];
        for v in 1..n {
            parent[v] = rng.gen_range(0..v);
            len[v] = if rng.gen::<f64>() < 0.2 { 0.0 } else { rng.gen::<f64>() };
        }
        let hv = (0..nh).map(|_| rng.gen_range(0..n)).collect();
        let mut t = TreeFactor { parent, len, hv, dist: vec![] };
        t.recompute();
        t
    }
    /// A pod (star) with `arms` arms, hub h on arm arm[h] at radius t[h]: root = centre, one vertex per hub.
    pub fn pod(arm: &[usize], t: &[f64]) -> Self {
        let nh = arm.len();
        // vertices: 0 centre, 1..=nh hubs (each its own vertex); sort hubs on an arm by radius, chain them
        let mut parent = vec![0; nh + 1];
        let mut len = vec![0.0; nh + 1];
        let mut order: Vec<usize> = (0..nh).collect();
        order.sort_by(|&a, &b| t[a].partial_cmp(&t[b]).unwrap());
        let mut last: std::collections::HashMap<usize, (usize, f64)> = Default::default();
        for &h in &order {
            let (pv, pt) = *last.get(&arm[h]).unwrap_or(&(0, 0.0));
            parent[h + 1] = pv;
            len[h + 1] = t[h] - pt;
            last.insert(arm[h], (h + 1, t[h]));
        }
        let mut f = TreeFactor { parent, len, hv: (1..=nh).collect(), dist: vec![] };
        f.recompute();
        f
    }
}

#[derive(Clone, Debug)]
pub struct TreeModel {
    pub factors: Vec<TreeFactor>,
    pub k: usize,
    /// flat coordinates of the hubs (nh x k)
    pub x: Vec<f64>,
}

impl TreeModel {
    pub fn hub_dist(&self, a: usize, b: usize) -> f64 {
        let mut s = 0.0;
        for f in &self.factors {
            let d = f.dist[f.hv[a] * f.n() + f.hv[b]];
            s += d * d;
        }
        for c in 0..self.k {
            let d = self.x[a * self.k + c] - self.x[b * self.k + c];
            s += d * d;
        }
        s.sqrt()
    }
}

/// Far-leg value (sum_m b_m^+, best S) for hubs in a product of trees x R^k (see [`far_value`]); per
/// edge and factor the best ordered pair of ray roots (r+, r-) over all vertices:
/// A_f = max sum_{m in S} [d(r+,r-) - d(r+,h^m_u) - d(r-,h^m_v)] / delta_m.
pub fn far_value_tree(des: &Design, tm: &TreeModel, scratch: &mut Vec<f64>) -> (f64, u32) {
    let p = des.p();
    let nl = des.nlegs();
    let hidx = |m: usize, g: usize| des.hub(m, g) - nl;
    let mut inv = vec![0.0; p];
    for m in 0..p {
        let mut dm: f64 = 0.0;
        for g in 0..des.ngroups[m] {
            for g2 in g + 1..des.ngroups[m] {
                dm = dm.max(tm.hub_dist(hidx(m, g), hidx(m, g2)));
            }
        }
        inv[m] = if dm > 1e-12 { 1.0 / dm } else { 0.0 };
    }
    let nn = des.nnodes;
    let mut best = (0.0, 0u32);
    let maxn = tm.factors.iter().map(|f| f.n()).max().unwrap_or(0);
    for s in 1u32..(1u32 << p) {
        if (0..p).any(|m| (s >> m) & 1 == 1 && inv[m] == 0.0) {
            continue;
        }
        let w: f64 = (0..p).filter(|m| (s >> m) & 1 == 1).map(|m| inv[m]).sum();
        // per factor, per node: cost_u(r)
        let nf = tm.factors.len();
        scratch.resize(nf * nn * maxn.max(1), 0.0);
        for (fi, f) in tm.factors.iter().enumerate() {
            let n = f.n();
            for u in 0..nn {
                let c = &mut scratch[(fi * nn + u) * maxn..(fi * nn + u) * maxn + n];
                for x in c.iter_mut() {
                    *x = 0.0;
                }
                for m in 0..p {
                    if (s >> m) & 1 == 1 {
                        let hv = f.hv[hidx(m, des.groups[m][u])];
                        let row = &f.dist[hv * n..hv * n + n];
                        for r in 0..n {
                            c[r] += inv[m] * row[r];
                        }
                    }
                }
            }
        }
        let mut tot = 0.0;
        for (e, &(u, v)) in des.edges.iter().enumerate() {
            let mut sq = 0.0;
            for (fi, f) in tm.factors.iter().enumerate() {
                let n = f.n();
                let cu = &scratch[(fi * nn + u) * maxn..(fi * nn + u) * maxn + n];
                let cv = &scratch[(fi * nn + v) * maxn..(fi * nn + v) * maxn + n];
                let mut a = 0.0f64;
                for r in 0..n {
                    let row = &f.dist[r * n..r * n + n];
                    let mut by = f64::NEG_INFINITY;
                    for r2 in 0..n {
                        let t = w * row[r2] - cv[r2];
                        if t > by {
                            by = t;
                        }
                    }
                    a = a.max(by - cu[r]);
                }
                sq += a * a;
            }
            for c in 0..tm.k {
                let mut z = 0.0;
                for m in 0..p {
                    if (s >> m) & 1 == 1 {
                        z += inv[m] * (tm.x[hidx(m, des.groups[m][u]) * tm.k + c] - tm.x[hidx(m, des.groups[m][v]) * tm.k + c]);
                    }
                }
                sq += z * z;
            }
            tot += des.weights[e] * sq.sqrt();
        }
        if tot > best.0 + 1e-12 {
            best = (tot, s);
        }
    }
    best
}

/// Annealing for [`far_value_tree`]: `nf` tree factors with `nv` vertices each, R^k. Moves: edge
/// length (additive / multiplicative / zero), hub to another vertex, re-parent a vertex (subtree
/// prune and regraft), flat coordinate kick, copy a hub's position from another hub.
/// Optional start (pods or a previous solution). Returns (value per merge, model, S), best first.
pub fn anneal_far_tree(des: &Design, nf: usize, nv: usize, k: usize, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64,
                       start: Option<TreeModel>) -> Vec<(f64, TreeModel, u32)> {
    let nh = des.nhubs();
    let p = des.p() as f64;
    let mut out: Vec<(f64, TreeModel, u32)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 17).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut tm = match &start {
                Some(s) if c % 2 == 0 => s.clone(),
                _ => TreeModel {
                    factors: (0..nf).map(|_| TreeFactor::random(&mut rng, nv, nh)).collect(),
                    k,
                    x: (0..nh * k).map(|_| gauss(&mut rng) * 0.5).collect(),
                },
            };
            let mut scratch = vec![];
            let mut cur = far_value_tree(des, &tm, &mut scratch).0;
            let mut best = (cur, tm.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64);
                let old = tm.clone();
                let nfac = tm.factors.len();
                let mv = rng.gen_range(0..100);
                if nfac > 0 && mv < 70 {
                    let f = &mut tm.factors[rng.gen_range(0..nfac)];
                    let n = f.n();
                    let sub = rng.gen_range(0..10);
                    if sub < 5 && n > 1 {
                        let v = rng.gen_range(1..n);
                        f.len[v] = (f.len[v] + sigma * gauss(&mut rng)).max(0.0);
                    } else if sub < 6 && n > 1 {
                        let v = rng.gen_range(1..n);
                        f.len[v] = if rng.gen::<bool>() { 0.0 } else { f.len[v] * (0.5 * gauss(&mut rng)).exp() };
                    } else if sub < 8 {
                        let h = rng.gen_range(0..nh);
                        f.hv[h] = if rng.gen::<bool>() { rng.gen_range(0..n) } else { f.hv[rng.gen_range(0..nh)] };
                    } else if n > 2 {
                        let v = rng.gen_range(1..n);
                        let np = rng.gen_range(0..n);
                        if !f.is_ancestor(v, np) {
                            f.parent[v] = np;
                        }
                    }
                    f.recompute();
                } else if k > 0 && mv < 95 {
                    let h = rng.gen_range(0..nh);
                    for cc in 0..k {
                        tm.x[h * k + cc] += sigma * gauss(&mut rng);
                    }
                } else {
                    // copy hub position (all factors and flat part)
                    let a = rng.gen_range(0..nh);
                    let b = rng.gen_range(0..nh);
                    for f in tm.factors.iter_mut() {
                        f.hv[a] = f.hv[b];
                    }
                    for cc in 0..k {
                        tm.x[a * k + cc] = tm.x[b * k + cc];
                    }
                }
                let v = far_value_tree(des, &tm, &mut scratch).0;
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, tm.clone());
                    }
                } else {
                    tm = old;
                }
                if tried == 500 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-8, 5.0);
                    acc = 0;
                    tried = 0;
                }
            }
            let (v, s) = far_value_tree(des, &best.1, &mut scratch);
            (v / p, best.1, s)
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

/// Convert a pod-product hub configuration (Model with spiders) to a TreeModel.
pub fn pods_to_trees(model: &Model, hubs: &[CPoint]) -> TreeModel {
    let factors = (0..model.arms.len())
        .map(|f| {
            let arm: Vec<usize> = hubs.iter().map(|h| h.arm[f] as usize).collect();
            let t: Vec<f64> = hubs.iter().map(|h| h.t[f]).collect();
            TreeFactor::pod(&arm, &t)
        })
        .collect();
    let k = model.k;
    let x = hubs.iter().flat_map(|h| h.x[..k].to_vec()).collect();
    TreeModel { factors, k, x }
}

// ------------------------------------------------------------------------------------ one-tree reduction

/// Edge savings of ONE tree factor (all merges, no delta normalisation):
/// s_e = max(0, max_{r+, r-} sum_k [d(r+,r-) - d(r+, h^k_u) - d(r-, h^k_v)]), ray roots at any vertex.
pub fn tree_savings(des: &Design, f: &TreeFactor, cost: &mut Vec<f64>) -> Vec<f64> {
    let p = des.p();
    let nl = des.nlegs();
    let n = f.n();
    let nn = des.nnodes;
    cost.resize(nn * n, 0.0);
    for u in 0..nn {
        for r in 0..n {
            let mut c = 0.0;
            for m in 0..p {
                let hv = f.hv[des.hub(m, des.groups[m][u]) - nl];
                c += f.dist[hv * n + r];
            }
            cost[u * n + r] = c;
        }
    }
    let w = p as f64;
    des.edges
        .iter()
        .map(|&(u, v)| {
            let cu = &cost[u * n..u * n + n];
            let cv = &cost[v * n..v * n + n];
            let mut a = 0.0f64;
            for r in 0..n {
                let row = &f.dist[r * n..r * n + n];
                let mut by = f64::NEG_INFINITY;
                for r2 in 0..n {
                    let t = w * row[r2] - cv[r2];
                    if t > by {
                        by = t;
                    }
                }
                a = a.max(by - cu[r]);
            }
            a
        })
        .collect()
}

/// Dbar = mean over merges k and pairs of hubs of merge k of d^2.
pub fn tree_dbar(des: &Design, f: &TreeFactor) -> f64 {
    let nl = des.nlegs();
    let n = f.n();
    let mut tot = 0.0;
    for m in 0..des.p() {
        let r = des.ngroups[m];
        let mut s = 0.0;
        for g in 0..r {
            for g2 in g + 1..r {
                let d = f.dist[f.hv[des.hub(m, g) - nl] * n + f.hv[des.hub(m, g2) - nl]];
                s += d * d;
            }
        }
        tot += s / (r * (r - 1) / 2) as f64;
    }
    tot / des.p() as f64
}

/// Edge orbits for AG(2,q) designs: direction classes of edges, merged under the semilinear maps of
/// GF(q)^2 that permute the merge classes. For other designs every edge is in orbit 0.
pub fn edge_orbits(des: &Design) -> Vec<usize> {
    if let Some(qn) = des.name.strip_prefix("net-") {
        // orbits of difference vectors (dr, dc) up to sign under (x,y)->(y,x), (x,y)->(x,x-y) and, for cyclic
        // Q, multiplication by units
        let q = QGroup::new(qn);
        let m = q.m;
        let idx = |x: usize, y: usize| x * m + y;
        let mut lab: Vec<usize> = (0..m * m).collect();
        let units: Vec<usize> = if q.dims.len() == 1 { (1..m).filter(|&a| (1..m).any(|b| (a * b) % m == 1)).collect() } else { vec![1] };
        let find = |lab: &Vec<usize>, mut x: usize| { while lab[x] != x { x = lab[x]; } x };
        loop {
            let mut ch = false;
            for x in 0..m {
                for y in 0..m {
                    let mut imgs = vec![idx(y, x), idx(x, q.lin(1, -1, x, y)), idx(q.neg[x], q.neg[y])];
                    for &a in &units {
                        imgs.push(idx((x * a) % m, (y * a) % m));
                    }
                    for j in imgs {
                        let (r1, r2) = (find(&lab, idx(x, y)), find(&lab, j));
                        if r1 != r2 {
                            let mn = r1.min(r2);
                            lab[r1] = mn;
                            lab[r2] = mn;
                            ch = true;
                        }
                    }
                }
            }
            if !ch {
                break;
            }
        }
        return des
            .edges
            .iter()
            .map(|&(u, v)| {
                let (r1, c1, r2, c2) = (u / m, u % m, v / m, v % m);
                find(&lab, idx(q.lin(1, -1, r2, r1), q.lin(1, -1, c2, c1)))
            })
            .collect();
    }
    let q = match des.name.strip_prefix("AG2-") {
        Some(r) => r.split('-').next().unwrap().parse::<usize>().unwrap(),
        None => return vec![0; des.edges.len()],
    };
    let add = |a: usize, b: usize| if q == 4 { a ^ b } else { (a + b) % q };
    const T4: [[usize; 4]; 4] = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]];
    let mul = |a: usize, b: usize| if q == 4 { T4[a][b] } else { (a * b) % q };
    let neg = |a: usize| if q == 4 { a } else { (q - a) % q };
    // projective direction index: normalise (dx,dy) so the first nonzero coordinate is 1
    let inv = |a: usize| (1..q).find(|&b| mul(a, b) == 1).unwrap();
    let norm = |dx: usize, dy: usize| -> (usize, usize) {
        if dx != 0 {
            let i = inv(dx);
            (1, mul(dy, i))
        } else {
            (0, 1)
        }
    };
    let dir = |(u, v): (usize, usize)| {
        let (x1, y1, x2, y2) = (u / q, u % q, v / q, v % q);
        norm(add(x2, neg(x1)), add(y2, neg(y1)))
    };
    // directions of the merge classes: a class is a set of parallel lines; take two nodes in one group
    let mut mdirs = vec![];
    for g in &des.groups {
        let a = (0..q * q).find(|&v| g[v] == g[0] && v != 0).unwrap();
        mdirs.push(dir((0, a)));
    }
    let frob = |a: usize| if q == 4 { mul(a, a) } else { a };
    let mut maps = vec![];
    for a in 0..q {
        for b in 0..q {
            for c in 0..q {
                for d in 0..q {
                    if add(mul(a, d), neg(mul(b, c))) == 0 {
                        continue;
                    }
                    for fr in [false, true] {
                        if fr && q != 4 {
                            continue;
                        }
                        let ap = move |(x, y): (usize, usize)| {
                            let (x, y) = if fr { (frob(x), frob(y)) } else { (x, y) };
                            (add(mul(a, x), mul(b, y)), add(mul(c, x), mul(d, y)))
                        };
                        let mut ok = true;
                        for &md in &mdirs {
                            let (x, y) = ap(md);
                            if !mdirs.contains(&norm(x, y)) {
                                ok = false;
                            }
                        }
                        if ok {
                            maps.push((a, b, c, d, fr));
                        }
                    }
                }
            }
        }
    }
    // union-find over directions
    let dirs: Vec<(usize, usize)> = std::iter::once((0, 1)).chain((0..q).map(|m| (1, m))).collect();
    let mut lab: Vec<usize> = (0..dirs.len()).collect();
    loop {
        let mut ch = false;
        for &(a, b, c, d, fr) in &maps {
            for (i, &(x, y)) in dirs.iter().enumerate() {
                let (x, y) = if fr { (frob(x), frob(y)) } else { (x, y) };
                let img = norm(add(mul(a, x), mul(b, y)), add(mul(c, x), mul(d, y)));
                let j = dirs.iter().position(|&z| z == img).unwrap();
                let m = lab[i].min(lab[j]);
                if lab[i] != m || lab[j] != m {
                    lab[i] = m;
                    lab[j] = m;
                    ch = true;
                }
            }
        }
        if !ch {
            break;
        }
    }
    des.edges.iter().map(|&e| lab[dirs.iter().position(|&z| z == dir(e)).unwrap()]).collect()
}

/// (Gamma = sum_e s_e^2 / Dbar, symmetrised-product value per merge
///  (1/p) sum_O |O| sqrt(mean_{e in O} s_e^2 / Dbar), Cauchy-Schwarz bound (1/p) sqrt(E Gamma)).
pub fn one_tree_scores(des: &Design, f: &TreeFactor, orbits: &[usize], cost: &mut Vec<f64>) -> (f64, f64, f64) {
    let s = tree_savings(des, f, cost);
    let db = tree_dbar(des, f);
    if db < 1e-14 {
        return (0.0, 0.0, 0.0);
    }
    let g: f64 = s.iter().map(|x| x * x).sum::<f64>() / db;
    let no = orbits.iter().max().unwrap() + 1;
    let mut cnt = vec![0usize; no];
    let mut sq = vec![0.0; no];
    for (e, &o) in orbits.iter().enumerate() {
        cnt[o] += 1;
        sq[o] += des.weights[e] * s[e] * s[e];
    }
    let p = des.p() as f64;
    let sym: f64 = (0..no).filter(|&o| cnt[o] > 0).map(|o| cnt[o] as f64 * (sq[o] / cnt[o] as f64 / db).sqrt()).sum::<f64>() / p;
    let cs = (des.edges.len() as f64 * g).sqrt() / p;
    (g, sym, cs)
}

/// Annealing over ONE tree (nv vertices; hubs at vertices) maximising Gamma (`target_sym` false) or the
/// symmetrised-product value (true). Returns (gamma, sym, cs, tree), best first.
pub fn anneal_one_tree(des: &Design, nv: usize, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64, target_sym: bool,
                       starts: &[TreeFactor]) -> Vec<(f64, f64, f64, TreeFactor)> {
    let nh = des.nhubs();
    let orbits = edge_orbits(des);
    let mut out: Vec<(f64, f64, f64, TreeFactor)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 19).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut f = if !starts.is_empty() && c % 2 == 0 {
                let mut s = starts[(c / 2) % starts.len()].clone();
                while s.parent.len() < nv {
                    let v = s.parent.len();
                    s.parent.push(rng.gen_range(0..v));
                    s.len.push(0.0);
                }
                s.recompute();
                s
            } else {
                TreeFactor::random(&mut rng, nv, nh)
            };
            let mut cost = vec![];
            let score = |f: &TreeFactor, cost: &mut Vec<f64>| {
                let (g, s, _) = one_tree_scores(des, f, &orbits, cost);
                if target_sym { s } else { g }
            };
            let mut cur = score(&f, &mut cost);
            let mut best = (cur, f.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            let n = f.n();
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64) * best.0.max(1e-9);
                let old = f.clone();
                let sub = rng.gen_range(0..10);
                if sub < 5 {
                    let v = rng.gen_range(1..n);
                    f.len[v] = (f.len[v] + sigma * gauss(&mut rng)).max(0.0);
                } else if sub < 6 {
                    let v = rng.gen_range(1..n);
                    f.len[v] = if rng.gen::<bool>() { 0.0 } else { f.len[v] * (0.5 * gauss(&mut rng)).exp() };
                } else if sub < 8 {
                    let h = rng.gen_range(0..nh);
                    f.hv[h] = if rng.gen::<bool>() { rng.gen_range(0..n) } else { f.hv[rng.gen_range(0..nh)] };
                } else {
                    let v = rng.gen_range(1..n);
                    let np = rng.gen_range(0..n);
                    if !f.is_ancestor(v, np) {
                        f.parent[v] = np;
                    }
                }
                f.recompute();
                let v = score(&f, &mut cost);
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, f.clone());
                    }
                } else {
                    f = old;
                }
                if tried == 500 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-8, 5.0);
                    acc = 0;
                    tried = 0;
                }
            }
            let (g, s, cs) = one_tree_scores(des, &best.1, &orbits, &mut cost);
            (g, s, cs, best.1)
        })
        .collect();
    if target_sym {
        out.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    } else {
        out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    }
    out
}

/// The node-tripod (theory agent): the p hubs of node `node` on arms 0..p-1 at radius 1, all others at the centre.
pub fn node_pod(des: &Design, node: usize) -> TreeFactor {
    let nh = des.nhubs();
    let nl = des.nlegs();
    let mut arm = vec![0usize; nh];
    let mut t = vec![0.0; nh];
    for m in 0..des.p() {
        let h = des.hub(m, des.groups[m][node]) - nl;
        arm[h] = m;
        t[h] = 1.0;
    }
    TreeFactor::pod(&arm, &t)
}

// ------------------------------------------------------------------------------------ large-net limit

/// Finite abelian group Q = Z_{d1} x ... x Z_{dr} (elements in mixed radix).
#[derive(Clone, Debug)]
pub struct QGroup {
    pub name: String,
    pub m: usize,
    pub dims: Vec<usize>,
    /// lin[(a, b, x, y)] = a x + b y for small integer coefficients a, b in {-1, 0, 1}: table per coefficient pair
    pub add: Vec<usize>,
    pub neg: Vec<usize>,
}

impl QGroup {
    /// "4" = Z_4, "2x2" = Z_2^2, "2x4", "3x3", ...
    pub fn new(name: &str) -> Self {
        let dims: Vec<usize> = name.split('x').map(|t| t.parse().unwrap()).collect();
        let m: usize = dims.iter().product();
        let dec = |mut i: usize| -> Vec<usize> {
            let mut v = vec![];
            for &d in &dims {
                v.push(i % d);
                i /= d;
            }
            v
        };
        let enc = |v: &[usize]| -> usize {
            let mut i = 0;
            for (k, &d) in dims.iter().enumerate().rev() {
                i = i * d + v[k];
            }
            i
        };
        let mut add = vec![0; m * m];
        let mut neg = vec![0; m];
        for a in 0..m {
            let va = dec(a);
            neg[a] = enc(&va.iter().zip(&dims).map(|(x, d)| (d - x) % d).collect::<Vec<_>>());
            for b in 0..m {
                let vb = dec(b);
                add[a * m + b] = enc(&va.iter().zip(&vb).zip(&dims).map(|((x, y), d)| (x + y) % d).collect::<Vec<_>>());
            }
        }
        QGroup { name: name.into(), m, dims, add, neg }
    }
    /// a x + b y with a, b in {-1, 0, 1}
    pub fn lin(&self, a: i32, b: i32, x: usize, y: usize) -> usize {
        let t = |c: i32, z: usize| match c {
            0 => 0,
            1 => z,
            _ => self.neg[z],
        };
        self.add[t(a, x) * self.m + t(b, y)]
    }
}

/// The limit problem (theory agent, research/sat3/limitnet.py): nodes n = (r, c) in Q^2, p merges given
/// by functionals (a_k, b_k): hub of n under merge k is class (k, a_k r + b_k c); hub class (k, q) sits at
/// vertex hv[k m + q] of ONE tree. Two generic nodes are independent uniform elements of Q^2:
///   Phi = E_{n,n'} [c(n,n')_+^2] / Dbar,  c(n,n') = max_{r+,r-} [p d(r+,r-) - F_n(r+) - F_n'(r-)],
///   F_n(x) = sum_k d(x, hub_k(n)),  Dbar = (1/p) sum_k E_{q,q'} d(pos_k(q), pos_k(q'))^2.
/// Level value (lower bound on the floor rho if the tree's far-leg sets are prices) = sqrt(Phi)/p.
pub struct LimitNet {
    pub q: QGroup,
    pub funcs: Vec<(i32, i32)>,
    /// node -> hub classes (k m + q)
    pub node_hubs: Vec<Vec<usize>>,
}

impl LimitNet {
    pub fn new(qname: &str, p: usize) -> Self {
        let q = QGroup::new(qname);
        let funcs: Vec<(i32, i32)> = [(1, 0), (0, 1), (1, -1), (1, 1)][..p].to_vec();
        let m = q.m;
        let mut node_hubs = vec![];
        for r in 0..m {
            for c in 0..m {
                node_hubs.push(funcs.iter().enumerate().map(|(k, &(a, b))| k * m + q.lin(a, b, r, c)).collect());
            }
        }
        LimitNet { q, funcs, node_hubs }
    }
    pub fn p(&self) -> usize {
        self.funcs.len()
    }
    pub fn nhubs(&self) -> usize {
        self.p() * self.q.m
    }
    pub fn phi(&self, f: &TreeFactor) -> f64 {
        let n = f.n();
        let m = self.q.m;
        let p = self.p();
        let mut db = 0.0;
        for k in 0..p {
            for a in 0..m {
                for b in 0..m {
                    let d = f.dist[f.hv[k * m + a] * n + f.hv[k * m + b]];
                    db += d * d;
                }
            }
        }
        db /= (p * m * m) as f64;
        if db < 1e-14 {
            return 0.0;
        }
        // distinct sorted vertex tuples of nodes, with multiplicities
        let mut tuples: std::collections::HashMap<Vec<usize>, usize> = Default::default();
        for nh in &self.node_hubs {
            let mut t: Vec<usize> = nh.iter().map(|&h| f.hv[h]).collect();
            t.sort_unstable();
            *tuples.entry(t).or_insert(0) += 1;
        }
        let tl: Vec<(Vec<f64>, f64)> = tuples
            .into_iter()
            .map(|(t, w)| ((0..n).map(|x| t.iter().map(|&v| f.dist[v * n + x]).sum()).collect(), w as f64))
            .collect();
        let pw = p as f64;
        let mut s = 0.0;
        for (cu, wu) in &tl {
            for (cv, wv) in &tl {
                let mut best = 0.0f64;
                for r in 0..n {
                    let row = &f.dist[r * n..r * n + n];
                    let mut by = f64::NEG_INFINITY;
                    for r2 in 0..n {
                        let t = pw * row[r2] - cv[r2];
                        if t > by {
                            by = t;
                        }
                    }
                    best = best.max(by - cu[r]);
                }
                s += wu * wv * best * best;
            }
        }
        s / ((m * m * m * m) as f64) / db
    }
    /// Pod labelling: hub class h on arm lab[h] (1..=A) at radius 1, or at the centre (lab 0).
    pub fn pod01(&self, lab: &[usize], arms: usize) -> TreeFactor {
        let mut parent = vec![0; arms + 1];
        let mut len = vec![1.0; arms + 1];
        len[0] = 0.0;
        for v in 1..=arms {
            parent[v] = 0;
        }
        let mut f = TreeFactor { parent, len, hv: lab.to_vec(), dist: vec![] };
        f.recompute();
        f
    }
}

/// Exhaustive search over pod labellings with radii in {0, 1} and at most `arms` arms (arm labels in
/// restricted-growth order to quotient by arm permutations). Returns (best Phi, labelling, count).
pub fn limit_exhaustive_pod01(net: &LimitNet, arms: usize) -> (f64, Vec<usize>, u64) {
    let nh = net.nhubs();
    // split on the first 4 hubs (restricted growth), then parallel DFS
    fn rec(net: &LimitNet, arms: usize, lab: &mut Vec<usize>, used: usize, f: &mut TreeFactor, best: &mut (f64, Vec<usize>), cnt: &mut u64) {
        if lab.len() == net.nhubs() {
            *cnt += 1;
            f.hv.copy_from_slice(lab);
            let v = net.phi(f);
            if v > best.0 + 1e-12 {
                *best = (v, lab.clone());
            }
            return;
        }
        for a in 0..=(used + 1).min(arms) {
            lab.push(a);
            rec(net, arms, lab, used.max(a), f, best, cnt);
            lab.pop();
        }
    }
    let mut prefixes: Vec<(Vec<usize>, usize)> = vec![(vec![], 0)];
    for _ in 0..nh.min(6) {
        let mut nx = vec![];
        for (pre, used) in &prefixes {
            for a in 0..=(used + 1).min(arms) {
                let mut q = pre.clone();
                q.push(a);
                nx.push((q, (*used).max(a)));
            }
        }
        prefixes = nx;
    }
    let res: Vec<(f64, Vec<usize>, u64)> = prefixes
        .par_iter()
        .map(|(pre, used)| {
            let mut f = net.pod01(&vec![0; nh], arms);
            let mut best = (f64::NEG_INFINITY, vec![]);
            let mut cnt = 0;
            let mut lab = pre.clone();
            rec(net, arms, &mut lab, *used, &mut f, &mut best, &mut cnt);
            (best.0, best.1, cnt)
        })
        .collect();
    let mut best = (f64::NEG_INFINITY, vec![], 0u64);
    for (v, l, c) in res {
        best.2 += c;
        if v > best.0 + 1e-12 {
            best.0 = v;
            best.1 = l;
        }
    }
    best
}

/// Annealing over one general tree for the limit problem (same moves as [`anneal_one_tree`]).
pub fn anneal_limit(net: &LimitNet, nv: usize, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64, starts: &[TreeFactor]) -> Vec<(f64, TreeFactor)> {
    let nh = net.nhubs();
    let mut out: Vec<(f64, TreeFactor)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 23).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut f = if !starts.is_empty() && c % 2 == 0 {
                let mut s = starts[(c / 2) % starts.len()].clone();
                while s.parent.len() < nv {
                    let v = s.parent.len();
                    s.parent.push(rng.gen_range(0..v));
                    s.len.push(0.0);
                }
                s.recompute();
                s
            } else {
                TreeFactor::random(&mut rng, nv, nh)
            };
            let n = f.n();
            let mut cur = net.phi(&f);
            let mut best = (cur, f.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64) * best.0.max(1e-9);
                let old = f.clone();
                let sub = rng.gen_range(0..12);
                if sub >= 10 {
                    // coset move: the classes q + <g> of one merge (or of every merge) go to one vertex
                    let m = net.q.m;
                    let g = rng.gen_range(0..m);
                    let mut h = vec![0usize];
                    let mut x = g;
                    while x != 0 {
                        h.push(x);
                        x = net.q.add[x * m + g];
                    }
                    let q0 = rng.gen_range(0..m);
                    let target = rng.gen_range(0..n);
                    let ks: Vec<usize> = if rng.gen::<bool>() { vec![rng.gen_range(0..net.p())] } else { (0..net.p()).collect() };
                    for &k in &ks {
                        for &y in &h {
                            f.hv[k * m + net.q.add[q0 * m + y]] = target;
                        }
                    }
                } else if sub < 4 {
                    let v = rng.gen_range(1..n);
                    f.len[v] = (f.len[v] + sigma * gauss(&mut rng)).max(0.0);
                } else if sub < 5 {
                    let v = rng.gen_range(1..n);
                    f.len[v] = if rng.gen::<bool>() { 0.0 } else { f.len[v] * (0.5 * gauss(&mut rng)).exp() };
                } else if sub < 8 {
                    let h = rng.gen_range(0..nh);
                    f.hv[h] = if rng.gen::<bool>() { rng.gen_range(0..n) } else { f.hv[rng.gen_range(0..nh)] };
                } else {
                    let v = rng.gen_range(1..n);
                    let np = rng.gen_range(0..n);
                    if !f.is_ancestor(v, np) {
                        f.parent[v] = np;
                    }
                }
                f.recompute();
                let v = net.phi(&f);
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, f.clone());
                    }
                } else {
                    f = old;
                }
                if tried == 500 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-8, 5.0);
                    acc = 0;
                    tried = 0;
                }
            }
            (net.phi(&best.1), best.1)
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

// ------------------------------------------------------------------------------------ cones over metric graphs

/// A finite metric graph G (all cycles >= 2 pi) as the link of the Euclidean cone C(G), given by its
/// (subdivided) vertex set; d = min(pi, d_G). Hubs and leg directions live at vertices.
#[derive(Clone, Debug)]
pub struct ConeGraph {
    pub name: String,
    pub n: usize,
    /// edges of the subdivided graph: (a, b, length)
    pub edges: Vec<(usize, usize, f64)>,
    pub dist: Vec<f64>,
    pub cosd: Vec<f64>,
    /// for each direction b, the directions at angle >= pi
    pub opp: Vec<Vec<u32>>,
    /// original edges (a, b, subdivision chain) for free graphs: list of subdivided-edge indices
    pub chains: Vec<Vec<usize>>,
}

fn pg_incidence(q: usize) -> (usize, Vec<(usize, usize)>) {
    let mut pts: Vec<[usize; 3]> = vec![];
    for a in 0..q {
        for b in 0..q {
            for c in 0..q {
                let v = [a, b, c];
                if v == [0, 0, 0] {
                    continue;
                }
                let f = *v.iter().find(|&&x| x != 0).unwrap();
                let inv = (1..q).find(|&y| (f * y) % q == 1).unwrap();
                let w = [(a * inv) % q, (b * inv) % q, (c * inv) % q];
                if !pts.contains(&w) {
                    pts.push(w);
                }
            }
        }
    }
    let n = pts.len();
    let mut e = vec![];
    for (i, p) in pts.iter().enumerate() {
        for (j, l) in pts.iter().enumerate() {
            if (p[0] * l[0] + p[1] * l[1] + p[2] * l[2]) % q == 0 {
                e.push((i, n + j));
            }
        }
    }
    (2 * n, e)
}

fn gq22_incidence() -> (usize, Vec<(usize, usize)>) {
    let mut pts = vec![];
    for a in 0..6 {
        for b in a + 1..6 {
            pts.push((a, b));
        }
    }
    let mut lines: Vec<Vec<(usize, usize)>> = vec![];
    fn rec(rest: Vec<usize>, cur: Vec<(usize, usize)>, out: &mut Vec<Vec<(usize, usize)>>) {
        if rest.is_empty() {
            out.push(cur);
            return;
        }
        let a = rest[0];
        for &b in &rest[1..] {
            let r2: Vec<usize> = rest.iter().cloned().filter(|&x| x != a && x != b).collect();
            let mut c2 = cur.clone();
            c2.push((a, b));
            rec(r2, c2, out);
        }
    }
    rec((0..6).collect(), vec![], &mut lines);
    let mut e = vec![];
    for (j, l) in lines.iter().enumerate() {
        for pr in l {
            e.push((pts.iter().position(|x| x == pr).unwrap(), 15 + j));
        }
    }
    (15 + lines.len(), e)
}

impl ConeGraph {
    /// Build from base edges with lengths; each base edge subdivided into `s` pieces; `extra` isolated points.
    pub fn from_edges(name: &str, n0: usize, base: &[(usize, usize, f64)], s: usize, extra: usize) -> Self {
        let mut n = n0;
        let mut edges = vec![];
        let mut chains = vec![];
        for &(a, b, l) in base {
            let mut chain = vec![];
            let mut prev = a;
            for _ in 0..s.max(1) - 1 {
                chain.push(edges.len());
                edges.push((prev, n, l / s as f64));
                prev = n;
                n += 1;
            }
            chain.push(edges.len());
            edges.push((prev, b, l / s.max(1) as f64));
            chains.push(chain);
        }
        let n = n + extra;
        let mut g = ConeGraph { name: name.into(), n, edges, dist: vec![], cosd: vec![], opp: vec![], chains };
        g.recompute();
        g
    }
    pub fn recompute(&mut self) {
        let n = self.n;
        let mut d = vec![f64::INFINITY; n * n];
        for i in 0..n {
            d[i * n + i] = 0.0;
        }
        for &(a, b, l) in &self.edges {
            if l < d[a * n + b] {
                d[a * n + b] = l;
                d[b * n + a] = l;
            }
        }
        for k in 0..n {
            for i in 0..n {
                let dik = d[i * n + k];
                if dik == f64::INFINITY {
                    continue;
                }
                for j in 0..n {
                    let t = dik + d[k * n + j];
                    if t < d[i * n + j] {
                        d[i * n + j] = t;
                    }
                }
            }
        }
        let pi = std::f64::consts::PI;
        self.dist = d.iter().map(|&x| x.min(pi)).collect();
        self.cosd = self.dist.iter().map(|x| x.cos()).collect();
        self.opp = (0..n).map(|b| (0..n).filter(|&c| self.dist[b * n + c] >= pi - 1e-9).map(|c| c as u32).collect()).collect();
    }
    /// Shortest cycle length (girth) of the graph, inf if a forest.
    pub fn girth(&self) -> f64 {
        let n = self.n;
        let mut best = f64::INFINITY;
        for (ei, &(a, b, l)) in self.edges.iter().enumerate() {
            // Dijkstra from a without edge ei
            let mut dist = vec![f64::INFINITY; n];
            let mut done = vec![false; n];
            dist[a] = 0.0;
            for _ in 0..n {
                let mut u = usize::MAX;
                let mut du = f64::INFINITY;
                for v in 0..n {
                    if !done[v] && dist[v] < du {
                        du = dist[v];
                        u = v;
                    }
                }
                if u == usize::MAX {
                    break;
                }
                done[u] = true;
                for (ej, &(x, y, w)) in self.edges.iter().enumerate() {
                    if ej == ei {
                        continue;
                    }
                    let o = if x == u { y } else if y == u { x } else { continue };
                    if du + w < dist[o] {
                        dist[o] = du + w;
                    }
                }
            }
            best = best.min(l + dist[b]);
        }
        best
    }
    /// pods:M | circle:N | kmm:M | heawood | pg3 | gq22, optional "+pods:K" (K isolated points), subdivision s.
    pub fn named(spec: &str, s: usize) -> Self {
        let pi = std::f64::consts::PI;
        let (main, extra) = match spec.split_once("+pods:") {
            Some((m, k)) => (m, k.parse().unwrap()),
            None => (spec, 0),
        };
        let (n0, base, l): (usize, Vec<(usize, usize)>, f64) = if let Some(m) = main.strip_prefix("pods:") {
            (m.parse().unwrap(), vec![], pi)
        } else if let Some(m) = main.strip_prefix("circle:") {
            let n: usize = m.parse().unwrap();
            (n, (0..n).map(|i| (i, (i + 1) % n)).collect(), 2.0 * pi / n as f64)
        } else if let Some(m) = main.strip_prefix("kmm:") {
            let m: usize = m.parse().unwrap();
            (2 * m, (0..m).flat_map(|i| (0..m).map(move |j| (i, m + j))).collect(), pi / 2.0)
        } else if main == "heawood" {
            let (n, e) = pg_incidence(2);
            (n, e, pi / 3.0)
        } else if main == "pg3" {
            let (n, e) = pg_incidence(3);
            (n, e, pi / 3.0)
        } else if main == "gq22" {
            let (n, e) = gq22_incidence();
            (n, e, pi / 4.0)
        } else {
            panic!("unknown graph {}", spec)
        };
        let base: Vec<(usize, usize, f64)> = base.into_iter().map(|(a, b)| (a, b, l)).collect();
        ConeGraph::from_edges(&format!("{}/s{}", spec, s), n0, &base, s, extra)
    }
    /// Random free graph: n0 vertices, `ne` random edges with lengths in [lmin, lmax], girth >= 2 pi enforced
    /// by rejection when adding edges.
    pub fn random_free<R: Rng>(rng: &mut R, n0: usize, ne: usize, s: usize, extra: usize) -> Self {
        let pi = std::f64::consts::PI;
        let mut base: Vec<(usize, usize, f64)> = vec![];
        let mut tries = 0;
        while base.len() < ne && tries < 2000 {
            tries += 1;
            let a = rng.gen_range(0..n0);
            let b = rng.gen_range(0..n0);
            if a == b || base.iter().any(|&(x, y, _)| (x, y) == (a, b) || (x, y) == (b, a)) {
                continue;
            }
            let l = pi * (0.25 + 0.9 * rng.gen::<f64>());
            base.push((a, b, l));
            let g = ConeGraph::from_edges("free", n0, &base, 1, 0);
            if g.girth() < 2.0 * pi - 1e-9 {
                base.pop();
            }
        }
        ConeGraph::from_edges("free", n0, &base, s, extra)
    }
}

/// Hubs in ONE cone factor: vertex hv[h] of the link, radius r[h].
#[derive(Clone, Debug)]
pub struct ConePlacement {
    pub hv: Vec<usize>,
    pub r: Vec<f64>,
}

#[inline]
fn cone_d2(g: &ConeGraph, a: usize, ra: f64, b: usize, rb: f64) -> f64 {
    (ra * ra + rb * rb - 2.0 * ra * rb * g.cosd[a * g.n + b]).max(0.0)
}

/// Node gain vectors f_u(b) = sum_k r^k_u cos(theta(b, x^k_u)), for a list of hub triples.
fn cone_gains(g: &ConeGraph, pl: &ConePlacement, hubsets: &[Vec<usize>]) -> Vec<Vec<f64>> {
    let n = g.n;
    hubsets
        .iter()
        .map(|hs| {
            let mut f = vec![0.0; n];
            for &h in hs {
                let row = &g.cosd[pl.hv[h] * n..pl.hv[h] * n + n];
                let r = pl.r[h];
                if r != 0.0 {
                    for b in 0..n {
                        f[b] += r * row[b];
                    }
                }
            }
            f
        })
        .collect()
}

/// best saving max_{b, b' at angle >= pi} f_u(b) + f_v(b'), clipped at 0
fn cone_pair(g: &ConeGraph, fu: &[f64], fv: &[f64]) -> f64 {
    let mut best = 0.0f64;
    for b in 0..g.n {
        let mut m = f64::NEG_INFINITY;
        for &c in &g.opp[b] {
            m = m.max(fv[c as usize]);
        }
        best = best.max(fu[b] + m);
    }
    best
}

/// One cone factor on a design: (Gamma = S/Dbar, S, Dbar); value over products of such cones
/// (orbit product, merge- and edge-transitive designs) = (1/p) sqrt(E Gamma) per merge, balanced.
pub fn cone_gamma(des: &Design, g: &ConeGraph, pl: &ConePlacement) -> (f64, f64, f64) {
    let nl = des.nlegs();
    let p = des.p();
    let hubsets: Vec<Vec<usize>> = (0..des.nnodes).map(|u| (0..p).map(|m| des.hub(m, des.groups[m][u]) - nl).collect()).collect();
    let f = cone_gains(g, pl, &hubsets);
    let s: f64 = des.edges.iter().zip(&des.weights).map(|(&(u, v), w)| {
        let c = cone_pair(g, &f[u], &f[v]);
        w * c * c
    }).sum();
    let mut db = 0.0;
    for m in 0..p {
        let r = des.ngroups[m];
        let mut t = 0.0;
        for a in 0..r {
            for b in a + 1..r {
                let (ha, hb) = (des.hub(m, a) - nl, des.hub(m, b) - nl);
                t += cone_d2(g, pl.hv[ha], pl.r[ha], pl.hv[hb], pl.r[hb]);
            }
        }
        db += t / (r * (r - 1) / 2) as f64;
    }
    db /= p as f64;
    if db < 1e-14 {
        return (0.0, s, db);
    }
    (s / db, s, db)
}

/// One cone factor in the limit problem: Phi.
pub fn cone_limit_phi(net: &LimitNet, g: &ConeGraph, pl: &ConePlacement) -> f64 {
    let m = net.q.m;
    let p = net.p();
    let mut db = 0.0;
    for k in 0..p {
        for a in 0..m {
            for b in 0..m {
                let (ha, hb) = (k * m + a, k * m + b);
                db += cone_d2(g, pl.hv[ha], pl.r[ha], pl.hv[hb], pl.r[hb]);
            }
        }
    }
    db /= (p * m * m) as f64;
    if db < 1e-14 {
        return 0.0;
    }
    // node types by (vertex, radius) multiset
    let mut types: Vec<(Vec<usize>, f64)> = vec![];
    for nh in &net.node_hubs {
        let mut t: Vec<usize> = nh.clone();
        t.sort_by(|&a, &b| (pl.hv[a], pl.r[a].to_bits()).cmp(&(pl.hv[b], pl.r[b].to_bits())));
        let key: Vec<(usize, u64)> = t.iter().map(|&h| (pl.hv[h], pl.r[h].to_bits())).collect();
        if let Some(e) = types.iter_mut().find(|(tt, _)| tt.iter().map(|&h| (pl.hv[h], pl.r[h].to_bits())).collect::<Vec<_>>() == key) {
            e.1 += 1.0;
        } else {
            types.push((t, 1.0));
        }
    }
    let hs: Vec<Vec<usize>> = types.iter().map(|t| t.0.clone()).collect();
    let f = cone_gains(g, pl, &hs);
    let mut s = 0.0;
    for (i, (_, wi)) in types.iter().enumerate() {
        for (j, (_, wj)) in types.iter().enumerate() {
            let c = cone_pair(g, &f[i], &f[j]);
            s += wi * wj * c * c;
        }
    }
    s / (m * m * m * m) as f64 / db
}

/// Objective for the cone annealer.
pub enum ConeTarget<'a> {
    Design(&'a Design),
    Limit(&'a LimitNet),
}

impl ConeTarget<'_> {
    fn nhubs(&self) -> usize {
        match self {
            ConeTarget::Design(d) => d.nhubs(),
            ConeTarget::Limit(l) => l.nhubs(),
        }
    }
    pub fn score(&self, g: &ConeGraph, pl: &ConePlacement) -> f64 {
        match self {
            ConeTarget::Design(d) => cone_gamma(d, g, pl).0,
            ConeTarget::Limit(l) => cone_limit_phi(l, g, pl),
        }
    }
}

/// Annealing over hub vertices and radii in one cone factor; if `free` is set, also over the lengths of
/// the base edges of the link (moves keeping girth >= 2 pi) and over deleting / restoring base edges.
/// Starts: `starts` (cycled over even chains), random otherwise. Returns (score, graph, placement).
#[allow(clippy::too_many_arguments)]
pub fn anneal_cone(target: &ConeTarget, g0: &ConeGraph, free: bool, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64,
                   starts: &[ConePlacement]) -> Vec<(f64, ConeGraph, ConePlacement)> {
    let nh = target.nhubs();
    let pi = std::f64::consts::PI;
    let mut out: Vec<(f64, ConeGraph, ConePlacement)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 29).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut g = g0.clone();
            let n = g.n;
            let mut pl = if !starts.is_empty() && c % 2 == 0 {
                starts[(c / 2) % starts.len()].clone()
            } else {
                ConePlacement {
                    hv: (0..nh).map(|_| rng.gen_range(0..n)).collect(),
                    r: (0..nh).map(|_| if rng.gen::<f64>() < 0.3 { 0.0 } else { rng.gen::<f64>() }).collect(),
                }
            };
            let mut cur = target.score(&g, &pl);
            let mut best = (cur, g.clone(), pl.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64) * best.0.max(1e-9);
                let (oldpl, mut oldg) = (pl.clone(), None);
                let mv = rng.gen_range(0..20);
                if mv < 7 {
                    let h = rng.gen_range(0..nh);
                    pl.r[h] = (pl.r[h] + sigma * gauss(&mut rng)).max(0.0);
                } else if mv < 8 {
                    let h = rng.gen_range(0..nh);
                    pl.r[h] = if rng.gen::<bool>() { 0.0 } else { pl.r[rng.gen_range(0..nh)] };
                } else if mv < 13 {
                    let h = rng.gen_range(0..nh);
                    pl.hv[h] = rng.gen_range(0..n);
                } else if mv < 15 {
                    // move to a neighbouring vertex
                    let h = rng.gen_range(0..nh);
                    let v = pl.hv[h];
                    let nb: Vec<usize> = g.edges.iter().filter_map(|&(a, b, _)| if a == v { Some(b) } else if b == v { Some(a) } else { None }).collect();
                    if !nb.is_empty() {
                        pl.hv[h] = nb[rng.gen_range(0..nb.len())];
                    }
                } else if mv < 17 || !free {
                    let a = rng.gen_range(0..nh);
                    let b = rng.gen_range(0..nh);
                    pl.hv[a] = pl.hv[b];
                    pl.r[a] = pl.r[b];
                } else if !g.chains.is_empty() {
                    // change the length of one base edge (all its subdivision pieces)
                    oldg = Some(g.clone());
                    let ci = rng.gen_range(0..g.chains.len());
                    let chain = g.chains[ci].clone();
                    let total: f64 = chain.iter().map(|&e| g.edges[e].2).sum();
                    let nt = if rng.gen_range(0..10) == 0 { 10.0 } else { (total + 0.3 * sigma * gauss(&mut rng)).clamp(0.05, 10.0) };
                    for &e in &chain {
                        g.edges[e].2 = nt / chain.len() as f64;
                    }
                    g.recompute();
                    if g.girth() < 2.0 * pi - 1e-9 {
                        g = oldg.take().unwrap();
                    }
                }
                let v = target.score(&g, &pl);
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, g.clone(), pl.clone());
                    }
                } else {
                    pl = oldpl;
                    if let Some(og) = oldg {
                        g = og;
                    }
                }
                if tried == 500 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-8, 5.0);
                    acc = 0;
                    tried = 0;
                }
            }
            best
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

/// Direct far-leg value of an explicit l2-product of cone factors on a design (b-vector per merge),
/// independent of the one-factor reduction: per edge, per factor the best antipodal direction pair for
/// the delta-weighted sum, weights proportional to the positive parts.
pub fn cone_product_b(des: &Design, factors: &[(&ConeGraph, &ConePlacement)]) -> Vec<f64> {
    let nl = des.nlegs();
    let p = des.p();
    let hd = |a: usize, b: usize| -> f64 {
        factors.iter().map(|(g, pl)| cone_d2(g, pl.hv[a], pl.r[a], pl.hv[b], pl.r[b])).sum::<f64>().sqrt()
    };
    let mut inv = vec![0.0; p];
    for m in 0..p {
        let mut dm: f64 = 0.0;
        for a in 0..des.ngroups[m] {
            for b in a + 1..des.ngroups[m] {
                dm = dm.max(hd(des.hub(m, a) - nl, des.hub(m, b) - nl));
            }
        }
        inv[m] = if dm > 1e-12 { 1.0 / dm } else { 0.0 };
    }
    let mut bk = vec![0.0; p];
    for &(u, v) in &des.edges {
        let mut cvec = vec![];
        let mut svec = vec![];
        for (g, pl) in factors {
            let n = g.n;
            let hu: Vec<usize> = (0..p).map(|m| des.hub(m, des.groups[m][u]) - nl).collect();
            let hv: Vec<usize> = (0..p).map(|m| des.hub(m, des.groups[m][v]) - nl).collect();
            let gain = |h: usize, b: usize| pl.r[h] * g.cosd[pl.hv[h] * n + b];
            let mut best = (f64::NEG_INFINITY, 0, 0);
            for b in 0..n {
                let fu: f64 = (0..p).map(|m| inv[m] * gain(hu[m], b)).sum();
                for &c in &g.opp[b] {
                    let fv: f64 = (0..p).map(|m| inv[m] * gain(hv[m], c as usize)).sum();
                    if fu + fv > best.0 {
                        best = (fu + fv, b, c as usize);
                    }
                }
            }
            cvec.push(best.0.max(0.0));
            svec.push((0..p).map(|m| gain(hu[m], best.1) + gain(hv[m], best.2)).collect::<Vec<f64>>());
        }
        let nrm = cvec.iter().map(|x| x * x).sum::<f64>().sqrt();
        if nrm > 0.0 {
            for m in 0..p {
                let s: f64 = cvec.iter().zip(&svec).map(|(c, sv)| c / nrm * sv[m]).sum();
                bk[m] += inv[m] * s;
            }
        }
    }
    bk
}

// ------------------------------------------------------------------------------------ filtrations of F_q^N

/// The field F_q, q in {2, 3, 4, 5, 7}.
#[derive(Clone, Debug)]
pub struct Fq {
    pub q: usize,
    pub add: Vec<u8>,
    pub mul: Vec<u8>,
    pub inv: Vec<u8>,
    pub neg: Vec<u8>,
}

impl Fq {
    pub fn new(q: usize) -> Self {
        let mut add = vec![0u8; q * q];
        let mut mul = vec![0u8; q * q];
        const T4: [[u8; 4]; 4] = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]];
        for a in 0..q {
            for b in 0..q {
                if q == 4 {
                    add[a * q + b] = (a ^ b) as u8;
                    mul[a * q + b] = T4[a][b];
                } else {
                    add[a * q + b] = ((a + b) % q) as u8;
                    mul[a * q + b] = ((a * b) % q) as u8;
                }
            }
        }
        let inv = (0..q).map(|a| if a == 0 { 0 } else { (1..q).find(|&b| mul[a * q + b] == 1).unwrap() as u8 }).collect();
        let neg = (0..q).map(|a| (0..q).find(|&b| add[a * q + b] == 0).unwrap() as u8).collect();
        Fq { q, add, mul, inv, neg }
    }
    #[inline]
    pub fn a(&self, x: u8, y: u8) -> u8 {
        self.add[x as usize * self.q + y as usize]
    }
    #[inline]
    pub fn m(&self, x: u8, y: u8) -> u8 {
        self.mul[x as usize * self.q + y as usize]
    }
}

/// The space C_N(q) of real filtrations of V = F_q^N (Cone over the spherical building x R), with hubs at
/// "point h at level a, V at level 0". Frames = unordered bases up to scaling; for each frame the support
/// (bitmask of nonzero coordinates) of every projective point is stored.
pub struct FiltSpace {
    pub f: Fq,
    pub n: usize,
    pub pts: Vec<Vec<u8>>,
    pub nframes: usize,
    pub supp: Vec<u8>,
    /// dsupp[frame][point]: indices i with <phi, f_i> != 0 for the functional phi with coordinates of the point
    /// (support of the hyperplane ker phi in the dual frame)
    pub dsupp: Vec<u8>,
    pub exhaustive: bool,
}

fn rank_and_inverse(f: &Fq, cols: &[Vec<u8>], n: usize) -> Option<Vec<Vec<u8>>> {
    // matrix M with the given columns; return M^{-1} (rows) if invertible
    let mut a: Vec<Vec<u8>> = (0..n).map(|i| (0..n).map(|j| cols[j][i]).collect()).collect();
    let mut inv: Vec<Vec<u8>> = (0..n).map(|i| (0..n).map(|j| (i == j) as u8).collect()).collect();
    for c in 0..n {
        let p = (c..n).find(|&r| a[r][c] != 0)?;
        a.swap(c, p);
        inv.swap(c, p);
        let iv = f.inv[a[c][c] as usize];
        for j in 0..n {
            a[c][j] = f.m(a[c][j], iv);
            inv[c][j] = f.m(inv[c][j], iv);
        }
        for r in 0..n {
            if r != c && a[r][c] != 0 {
                let t = f.neg[a[r][c] as usize];
                for j in 0..n {
                    a[r][j] = f.a(a[r][j], f.m(t, a[c][j]));
                    inv[r][j] = f.a(inv[r][j], f.m(t, inv[c][j]));
                }
            }
        }
    }
    Some(inv)
}

impl FiltSpace {
    /// All frames if there are at most `max_frames` N-subsets of points to test, else `max_frames` random frames.
    pub fn new(q: usize, n: usize, max_frames: usize, seed: u64) -> Self {
        let f = Fq::new(q);
        let mut pts = vec![];
        let total = q.pow(n as u32);
        for code in 1..total {
            let v: Vec<u8> = (0..n).map(|i| ((code / q.pow(i as u32)) % q) as u8).collect();
            // normalised: first nonzero coordinate (from index 0) equal to 1
            if v.iter().find(|&&x| x != 0) == Some(&1) {
                pts.push(v);
            }
        }
        let np = pts.len();
        // count N-subsets
        let mut comb = 1f64;
        for i in 0..n {
            comb *= (np - i) as f64 / (i + 1) as f64;
        }
        let exhaustive = comb <= max_frames as f64 * 1.5;
        let mut supp = vec![];
        let mut dsupp: Vec<u8> = vec![];
        let mut nframes = 0;
        let mut push_frame = |idx: &[usize], supp: &mut Vec<u8>| -> bool {
            let cols: Vec<Vec<u8>> = idx.iter().map(|&i| pts[i].clone()).collect();
            if let Some(inv) = rank_and_inverse(&f, &cols, n) {
                for ph in &pts {
                    let mut mask = 0u8;
                    for (r, col) in cols.iter().enumerate() {
                        let mut c = 0u8;
                        for j in 0..n {
                            c = f.a(c, f.m(ph[j], col[j]));
                        }
                        if c != 0 {
                            mask |= 1 << r;
                        }
                    }
                    dsupp.push(mask);
                }
                for p in &pts {
                    let mut mask = 0u8;
                    for r in 0..n {
                        let mut c = 0u8;
                        for j in 0..n {
                            c = f.a(c, f.m(inv[r][j], p[j]));
                        }
                        if c != 0 {
                            mask |= 1 << r;
                        }
                    }
                    supp.push(mask);
                }
                true
            } else {
                false
            }
        };
        if exhaustive {
            let mut idx: Vec<usize> = (0..n).collect();
            loop {
                if push_frame(&idx, &mut supp) {
                    nframes += 1;
                }
                // next combination
                let mut i = n;
                loop {
                    if i == 0 {
                        break;
                    }
                    i -= 1;
                    if idx[i] < np - n + i {
                        idx[i] += 1;
                        for j in i + 1..n {
                            idx[j] = idx[j - 1] + 1;
                        }
                        i += 1;
                        break;
                    }
                    if i == 0 {
                        i = usize::MAX;
                        break;
                    }
                }
                if i == usize::MAX || i == 0 {
                    break;
                }
            }
        } else {
            let mut rng = SmallRng::seed_from_u64(seed);
            while nframes < max_frames {
                let mut idx: Vec<usize> = vec![];
                while idx.len() < n {
                    let x = rng.gen_range(0..np);
                    if !idx.contains(&x) {
                        idx.push(x);
                    }
                }
                if push_frame(&idx, &mut supp) {
                    nframes += 1;
                }
            }
        }
        FiltSpace { f, n, pts, nframes, supp, dsupp, exhaustive }
    }
    pub fn point_index(&self, v: &[u8]) -> usize {
        // normalise
        let lead = *v.iter().find(|&&x| x != 0).unwrap();
        let iv = self.f.inv[lead as usize];
        let w: Vec<u8> = v.iter().map(|&x| self.f.m(x, iv)).collect();
        self.pts.iter().position(|p| *p == w).unwrap()
    }
}

/// Wolfe's minimum-norm-point algorithm for conv{Σ_k (a_k e_{i_k} - b_k e_{j_k}) : i_k in A_k, j_k in B_k}
/// in R^n (n <= 8), via the separable linear oracle. Returns the minimum-norm point.
pub fn mnp_supports(n: usize, a: &[(u8, f64)], b: &[(u8, f64)]) -> [f64; 8] {
    mnp_supports_lin(n, a, b, &[0.0; 8])
}

/// [`mnp_supports`] with a constant vector `lin` added to every hull point.
pub fn mnp_supports_lin(n: usize, a: &[(u8, f64)], b: &[(u8, f64)], lin: &[f64; 8]) -> [f64; 8] {
    let oracle = |x: &[f64; 8]| -> [f64; 8] {
        let mut v = *lin;
        for &(m, w) in a {
            if w == 0.0 || m == 0 {
                continue;
            }
            let mut bi = 0;
            let mut bv = f64::INFINITY;
            for i in 0..n {
                if (m >> i) & 1 == 1 && x[i] < bv {
                    bv = x[i];
                    bi = i;
                }
            }
            v[bi] += w;
        }
        for &(m, w) in b {
            if w == 0.0 || m == 0 {
                continue;
            }
            let mut bi = 0;
            let mut bv = f64::NEG_INFINITY;
            for i in 0..n {
                if (m >> i) & 1 == 1 && x[i] > bv {
                    bv = x[i];
                    bi = i;
                }
            }
            v[bi] -= w;
        }
        v
    };
    let dot = |x: &[f64; 8], y: &[f64; 8]| -> f64 { (0..n).map(|i| x[i] * y[i]).sum() };
    let mut sset: Vec<[f64; 8]> = vec![oracle(&[0.0; 8])];
    let mut lam: Vec<f64> = vec![1.0];
    let mut x = sset[0];
    for _major in 0..200 {
        let v = oracle(&x);
        let xx = dot(&x, &x);
        if xx - dot(&x, &v) <= 1e-12 * xx.max(1e-12) || xx < 1e-24 {
            break;
        }
        if sset.iter().any(|s| (0..n).all(|i| (s[i] - v[i]).abs() < 1e-14)) {
            break;
        }
        sset.push(v);
        lam.push(0.0);
        for _minor in 0..50 {
            // affine minimiser: min |Σ α_i s_i|^2, Σ α = 1
            let k = sset.len();
            let mut mat = vec![vec![0.0; k + 1]; k + 1];
            let mut rhs = vec![0.0; k + 1];
            for i in 0..k {
                for j in 0..k {
                    mat[i][j] = dot(&sset[i], &sset[j]);
                }
                mat[i][k] = 1.0;
                mat[k][i] = 1.0;
            }
            rhs[k] = 1.0;
            let alpha = match solve_dense(mat, rhs) {
                Some(s) => s,
                None => break,
            };
            let alpha = &alpha[..k];
            if alpha.iter().all(|&t| t > 1e-12) {
                lam = alpha.to_vec();
                break;
            }
            let mut theta = 1.0f64;
            for i in 0..k {
                if alpha[i] <= 1e-12 {
                    let d = lam[i] - alpha[i];
                    if d > 0.0 {
                        theta = theta.min(lam[i] / d);
                    }
                }
            }
            for i in 0..k {
                lam[i] = theta * alpha[i] + (1.0 - theta) * lam[i];
            }
            let mut i = 0;
            while i < sset.len() {
                if lam[i] <= 1e-13 {
                    sset.remove(i);
                    lam.remove(i);
                } else {
                    i += 1;
                }
            }
            let tot: f64 = lam.iter().sum();
            for l in lam.iter_mut() {
                *l /= tot;
            }
        }
        x = [0.0; 8];
        for (s, &l) in sset.iter().zip(&lam) {
            for i in 0..n {
                x[i] += l * s[i];
            }
        }
    }
    x
}

fn solve_dense(mut a: Vec<Vec<f64>>, mut b: Vec<f64>) -> Option<Vec<f64>> {
    let n = b.len();
    for c in 0..n {
        let p = (c..n).max_by(|&i, &j| a[i][c].abs().partial_cmp(&a[j][c].abs()).unwrap())?;
        if a[p][c].abs() < 1e-14 {
            return None;
        }
        a.swap(c, p);
        b.swap(c, p);
        for r in 0..n {
            if r != c {
                let t = a[r][c] / a[c][c];
                if t != 0.0 {
                    for j in c..n {
                        a[r][j] -= t * a[c][j];
                    }
                    b[r] -= t * b[c];
                }
            }
        }
    }
    Some((0..n).map(|i| b[i] / a[i][i]).collect())
}

/// Hubs in C_N(q): hub h is the filtration "U at level r[h], V at level c[h]" (r >= c), U = the point pt[h]
/// (kind 0) or the hyperplane ker(phi), phi with the coordinates of the point pt[h] (kind 1).
#[derive(Clone, Debug)]
pub struct FiltPlacement {
    pub pt: Vec<usize>,
    pub r: Vec<f64>,
    pub kind: Vec<u8>,
    pub c: Vec<f64>,
}

impl FiltPlacement {
    pub fn points(pt: Vec<usize>, r: Vec<f64>) -> Self {
        let n = pt.len();
        FiltPlacement { pt, r, kind: vec![0; n], c: vec![0.0; n] }
    }
}

/// A hub as seen by one edge: (point index, kind, a, c).
pub type FHub = (usize, u8, f64, f64);

/// Busemann-type term of a hub for a leg along +d (side 0) or -d (side 1) in a frame: value at d.
fn fhub_term(fs: &FiltSpace, fr: usize, h: FHub, side: u8, d: &[f64]) -> f64 {
    let np = fs.pts.len();
    let n = fs.n;
    let (p, kind, a, c) = h;
    let sum: f64 = d[..n].iter().sum();
    let mask = if kind == 0 { fs.supp[fr * np + p] } else { fs.dsupp[fr * np + p] };
    let mn = (0..n).filter(|&i| (mask >> i) & 1 == 1).map(|i| d[i]).fold(f64::INFINITY, f64::min);
    let mx = (0..n).filter(|&i| (mask >> i) & 1 == 1).map(|i| d[i]).fold(f64::NEG_INFINITY, f64::max);
    match (kind, side) {
        (0, 0) => (a - c) * mn + c * sum,
        (1, 0) => a * sum - (a - c) * mx,
        (0, _) => -(a - c) * mx - c * sum,
        _ => -a * sum + (a - c) * mn,
    }
}

/// Far-leg value of one edge: max over frames and unit d of Σ_k w_k [term(h_k, +d) + term(h'_k, -d)], where for
/// U = point (support A in the frame) term(+d) = (a-c) min_A d + c Σd, term(-d) = -(a-c) max_A d - c Σd; for U =
/// hyperplane (dual support A*) term(+d) = a Σd - (a-c) max_{A*} d, term(-d) = -a Σd + (a-c) min_{A*} d (entry levels of
/// U in the flag of the ray; q1-notes Lemma 1.4 for points). Each term is concave in d, so the maximum is the
/// distance from 0 to a convex hull (Wolfe). Returns (c_e, per-merge savings at the optimum, unweighted).
pub fn filt_edge(fs: &FiltSpace, hu: &[FHub], hv: &[FHub], w: &[f64]) -> (f64, Vec<f64>) {
    let np = fs.pts.len();
    let n = fs.n;
    let mut seen: std::collections::HashSet<Vec<u8>> = Default::default();
    let mut best = (0.0f64, vec![0.0; hu.len()], 0usize, [0.0f64; 8]);
    for fr in 0..fs.nframes {
        let key: Vec<u8> = hu
            .iter()
            .chain(hv.iter())
            .map(|&(p, k, _, _)| if k == 0 { fs.supp[fr * np + p] } else { fs.dsupp[fr * np + p] })
            .collect();
        if !seen.insert(key) {
            continue;
        }
        let mut lin = [0.0f64; 8];
        let mut mins: Vec<(u8, f64)> = vec![];
        let mut maxs: Vec<(u8, f64)> = vec![];
        for (side, hs) in [(0u8, hu), (1u8, hv)] {
            for (&(p, kind, a, c), &wk) in hs.iter().zip(w) {
                let mask = if kind == 0 { fs.supp[fr * np + p] } else { fs.dsupp[fr * np + p] };
                let (l, mi, ma) = match (kind, side) {
                    (0, 0) => (c, a - c, 0.0),
                    (1, 0) => (a, 0.0, a - c),
                    (0, _) => (-c, 0.0, a - c),
                    _ => (-a, a - c, 0.0),
                };
                for x in lin.iter_mut().take(n) {
                    *x += wk * l;
                }
                if mi != 0.0 {
                    mins.push((mask, wk * mi));
                }
                if ma != 0.0 {
                    maxs.push((mask, wk * ma));
                }
            }
        }
        let x = mnp_supports_lin(n, &mins, &maxs, &lin);
        let nrm = (0..n).map(|i| x[i] * x[i]).sum::<f64>().sqrt();
        if nrm > best.0 + 1e-12 {
            let mut d = [0.0; 8];
            for i in 0..n {
                d[i] = x[i] / nrm;
            }
            best = (nrm, vec![], fr, d);
        }
    }
    let (c, _, fr, d) = best;
    let sk = if c > 0.0 { hu.iter().zip(hv).map(|(&h, &h2)| fhub_term(fs, fr, h, 0, &d) + fhub_term(fs, fr, h2, 1, &d)).collect() } else { vec![0.0; hu.len()] };
    (c, sk)
}

/// Squared distance of two hub filtrations (U at a, V at c), (U' at b, V at c'), dims k, k', i = dim(U ∩ U'):
/// i(a-b)^2 + (k-i)(a-c')^2 + (k'-i)(c-b)^2 + (N-k-k'+i)(c-c')^2.
fn filt_d2(fs: &FiltSpace, x: FHub, y: FHub) -> f64 {
    let n = fs.n;
    let f = &fs.f;
    let (p, kp, a, c) = x;
    let (p2, kp2, b, c2) = y;
    let dot = |u: &[u8], v: &[u8]| (0..n).fold(0u8, |acc, j| f.a(acc, f.m(u[j], v[j])));
    let (k, k2) = (if kp == 0 { 1 } else { n - 1 }, if kp2 == 0 { 1 } else { n - 1 });
    let i = match (kp, kp2) {
        (0, 0) => (p == p2) as usize,
        (1, 1) => if p == p2 { n - 1 } else { n - 2 },
        (0, 1) => (dot(&fs.pts[p], &fs.pts[p2]) == 0) as usize,
        _ => (dot(&fs.pts[p], &fs.pts[p2]) == 0) as usize,
    };
    let (k, k2, i) = (k as f64, k2 as f64, i as f64);
    i * (a - b).powi(2) + (k - i) * (a - c2).powi(2) + (k2 - i) * (c - b).powi(2) + (n as f64 - k - k2 + i) * (c - c2).powi(2)
}

/// Scores of a single filtration factor on a design:
/// (Gamma = Σ c_e^2/Dbar (weights 1), CS value per merge (1/p)sqrt(E Gamma),
///  direct single-factor average (Σ_k b_k)/p, direct min_k b_k), with b_k = Σ_e s^k_e / delta_k at the
/// per-edge optimum of Σ_k s^k/delta_k.
pub struct FiltScores {
    /// symmetrised-product value (1/p) Σ_O |O| sqrt(mean_O c^2 / Dbar) (orbits from edge_orbits)
    pub sym: f64,
    pub gamma: f64,
    pub cs: f64,
    pub avg: f64,
    pub minb: f64,
    pub b: Vec<f64>,
}

pub fn filt_scores(des: &Design, fs: &FiltSpace, pl: &FiltPlacement, cache: &mut std::collections::HashMap<Vec<u64>, (f64, Vec<f64>)>,
                   want_direct: bool) -> FiltScores {
    let p = des.p();
    let nl = des.nlegs();
    let hub = |m: usize, u: usize| des.hub(m, des.groups[m][u]) - nl;
    let mut db = 0.0;
    let mut delta = vec![0.0f64; p];
    for m in 0..p {
        let r = des.ngroups[m];
        let mut t = 0.0;
        for a in 0..r {
            for b in a + 1..r {
                let (ha, hb) = (des.hub(m, a) - nl, des.hub(m, b) - nl);
                let d2 = filt_d2(fs, (pl.pt[ha], pl.kind[ha], pl.r[ha], pl.c[ha]), (pl.pt[hb], pl.kind[hb], pl.r[hb], pl.c[hb]));
                t += d2;
                delta[m] = delta[m].max(d2.sqrt());
            }
        }
        db += t / (r * (r - 1) / 2) as f64;
    }
    db /= p as f64;
    let mut eval = |u: usize, v: usize, w: &[f64]| -> (f64, Vec<f64>) {
        let fh = |h: usize| -> FHub { (pl.pt[h], pl.kind[h], pl.r[h], pl.c[h]) };
        let hu: Vec<FHub> = (0..p).map(|m| fh(hub(m, u))).collect();
        let hv: Vec<FHub> = (0..p).map(|m| fh(hub(m, v))).collect();
        let mut key: Vec<u64> = hu.iter().chain(hv.iter()).flat_map(|&(a, k, r, c)| [(a as u64) << 1 | k as u64, r.to_bits(), c.to_bits()]).collect();
        key.extend(w.iter().map(|x| x.to_bits()));
        if let Some(c) = cache.get(&key) {
            return c.clone();
        }
        let r = filt_edge(fs, &hu, &hv, w);
        cache.insert(key, r.clone());
        r
    };
    let ones = vec![1.0; p];
    let mut s = 0.0;
    let orbits = edge_orbits(des);
    let no = orbits.iter().max().unwrap() + 1;
    let mut osq = vec![0.0; no];
    let mut ocnt = vec![0usize; no];
    for (e, &(u, v)) in des.edges.iter().enumerate() {
        let (c, _) = eval(u, v, &ones);
        s += c * c;
        osq[orbits[e]] += c * c;
        ocnt[orbits[e]] += 1;
    }
    let sym = if db > 1e-14 {
        (0..no).filter(|&o| ocnt[o] > 0).map(|o| ocnt[o] as f64 * (osq[o] / ocnt[o] as f64 / db).sqrt()).sum::<f64>() / p as f64
    } else {
        0.0
    };
    let gamma = if db > 1e-14 { s / db } else { 0.0 };
    let cs = (des.edges.len() as f64 * gamma).sqrt() / p as f64;
    let (mut avg, mut minb, mut b) = (0.0, 0.0, vec![0.0; p]);
    if want_direct && delta.iter().all(|&x| x > 1e-12) {
        let w: Vec<f64> = delta.iter().map(|x| 1.0 / x).collect();
        for &(u, v) in &des.edges {
            let (_, sk) = eval(u, v, &w);
            for m in 0..p {
                b[m] += sk[m] / delta[m];
            }
        }
        avg = b.iter().map(|x| x.max(0.0)).sum::<f64>() / p as f64;
        minb = b.iter().cloned().fold(f64::INFINITY, f64::min);
    }
    FiltScores { sym, gamma, cs, avg, minb, b }
}

/// Annealing over hub points and levels in C_N(q). target: "gamma" (CS / orbit value) or "min" (direct min_k b_k)
/// or "avg" (direct average). Returns (score, placement) per chain, best first.
#[allow(clippy::too_many_arguments)]
pub fn anneal_filt(des: &Design, fs: &FiltSpace, target: &str, iters: usize, chains: usize, t0: f64, t1: f64, seed: u64,
                   starts: &[FiltPlacement]) -> Vec<(f64, FiltPlacement)> {
    let nh = des.nhubs();
    let np = fs.pts.len();
    let direct = target != "gamma" && target != "sym";
    // PF_FILT_POINTS: points only; PF_FILT_NOC: V at level 0 only
    let allow_hyp = std::env::var("PF_FILT_POINTS").is_err();
    let allow_c = std::env::var("PF_FILT_NOC").is_err();
    let score = |sc: &FiltScores| match target {
        "gamma" => sc.gamma,
        "sym" => sc.sym,
        "min" => sc.minb,
        _ => sc.avg,
    };
    let mut out: Vec<(f64, FiltPlacement)> = (0..chains)
        .into_par_iter()
        .map(|c| {
            let mut rng = SmallRng::seed_from_u64(seed ^ (c as u64 + 31).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut cache = Default::default();
            let mut pl = if !starts.is_empty() && c % 2 == 0 {
                starts[(c / 2) % starts.len()].clone()
            } else {
                FiltPlacement {
                    pt: (0..nh).map(|_| rng.gen_range(0..np)).collect(),
                    r: vec![1.0; nh],
                    kind: (0..nh).map(|_| if allow_hyp && rng.gen::<bool>() { 1 } else { 0 }).collect(),
                    c: vec![0.0; nh],
                }
            };
            let mut cur = score(&filt_scores(des, fs, &pl, &mut cache, direct));
            let mut best = (cur, pl.clone());
            let mut sigma = 0.2;
            let (mut acc, mut tried) = (0usize, 0usize);
            for it in 0..iters {
                let t = t0 * (t1 / t0).powf(it as f64 / iters as f64) * best.0.abs().max(1e-6);
                let old = pl.clone();
                let h = rng.gen_range(0..nh);
                match rng.gen_range(0..14) {
                    0..=4 => pl.pt[h] = rng.gen_range(0..np),
                    5 => {
                        let h2 = rng.gen_range(0..nh);
                        pl.pt[h] = pl.pt[h2];
                        pl.kind[h] = pl.kind[h2];
                    }
                    6..=7 => pl.r[h] = (pl.r[h] + sigma * gauss(&mut rng)).max(pl.c[h]),
                    8 => pl.r[h] = if rng.gen::<bool>() { pl.c[h].max(0.0) } else { pl.c[h] + 1.0 },
                    9 if allow_hyp => pl.kind[h] ^= 1,
                    10..=11 if allow_c => pl.c[h] = (pl.c[h] + sigma * gauss(&mut rng)).min(pl.r[h]),
                    12 if allow_c => pl.c[h] = if rng.gen::<bool>() { 0.0 } else { pl.r[h] - 1.0 },
                    _ => {
                        let h2 = rng.gen_range(0..nh);
                        pl.pt.swap(h, h2);
                        pl.r.swap(h, h2);
                        pl.kind.swap(h, h2);
                        pl.c.swap(h, h2);
                    }
                }
                if cache.len() > 2_000_000 {
                    cache.clear();
                }
                let v = score(&filt_scores(des, fs, &pl, &mut cache, direct));
                tried += 1;
                if v >= cur || rng.gen::<f64>() < ((v - cur) / t).exp() {
                    cur = v;
                    acc += 1;
                    if v > best.0 + 1e-12 {
                        best = (v, pl.clone());
                    }
                } else {
                    pl = old;
                }
                if tried == 200 {
                    let r = acc as f64 / tried as f64;
                    sigma *= if r > 0.3 { 1.25 } else { 0.8 };
                    sigma = sigma.clamp(1e-6, 2.0);
                    acc = 0;
                    tried = 0;
                }
            }
            best
        })
        .collect();
    out.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    out
}

/// The Q1 placement for the 3-net of F_2^m (q1-notes §2.2): hub of class x in {e1, e2, e1+e2} and value y is the
/// point <(x, y)> of F_2^(m+2) (coordinates: x in the first two, y in the last m), level 1.
pub fn q1_placement(des: &Design, fs: &FiltSpace, m: usize) -> FiltPlacement {
    let nl = des.nlegs();
    let g = 1usize << m;
    let mut pt = vec![0; des.nhubs()];
    for (k, x) in [1usize, 2, 3].iter().enumerate() {
        for y in 0..g {
            let mut v = vec![0u8; m + 2];
            v[0] = (x & 1) as u8;
            v[1] = ((x >> 1) & 1) as u8;
            for i in 0..m {
                v[2 + i] = ((y >> i) & 1) as u8;
            }
            pt[des.hub(k, y) - nl] = fs.point_index(&v);
        }
    }
    FiltPlacement::points(pt, vec![1.0; des.nhubs()])
}

// ------------------------------------------------------------------------------------ tests

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn designs_shape() {
        let d = Design::delta3(3);
        assert_eq!((d.nlegs(), d.nhubs(), d.p()), (18, 9, 3));
        for &(u, v) in &d.edges {
            for g in &d.groups {
                assert_ne!(g[u], g[v]);
            }
        }
        assert!((d.flat_value() - 3.0 * 3f64.sqrt()).abs() < 1e-12);
        assert!((Design::delta3(2).flat_value() - 9.0 / 2f64.sqrt()).abs() < 1e-12);
        assert!((Design::crossing(1.0, 1.0).flat_value() - 2f64.sqrt()).abs() < 1e-12);
        assert!((Design::k4().flat_value() - 2.0 * 2f64.sqrt()).abs() < 1e-12);
    }

    #[test]
    fn far_leg_euclid_crossing() {
        // hubs: rows at +-a/2, columns at +-b/2, a ⟂ b; legs far along (a+b), (a-b)
        let des = Design::crossing(1.0, 1.0);
        let m = Model { arms: vec![], k: 2 };
        let mk = |x: f64, y: f64| {
            let mut p = CPoint::default();
            p.x[0] = x;
            p.x[1] = y;
            p
        };
        let big = 1e6;
        let s = 1.0 / 2f64.sqrt();
        let pts = vec![mk(big * s, big * s), mk(-big * s, -big * s), mk(big * s, -big * s), mk(-big * s, big * s),
                       mk(0.5, 0.0), mk(-0.5, 0.0), mk(0.0, 0.5), mk(0.0, -0.5)];
        // legs: edge0 = (x,v): x far +(a+b), v far -(a+b); edge1 = (y,u): y far +(a-b), u far -(a-b)
        let b = m.b(&des, &pts);
        assert!((value(&b) - 2f64.sqrt()).abs() < 1e-4, "{:?}", b);
    }

    #[test]
    fn best_legs_matches_bruteforce_crossing_mu2() {
        let des = Design::crossing(1.0, 1.0);
        let sp = MatSpace::new(2);
        let mut scratch = vec![];
        let mut rng = SmallRng::seed_from_u64(3);
        for _ in 0..20 {
            let hubs: Vec<usize> = (0..4).map(|_| rng.gen_range(0..16)).collect();
            let (v, _, _) = sp.best_legs(&des, &hubs, false, &mut scratch);
            let mut bf = 0.0f64;
            for l in 0..16usize.pow(4) {
                let mut pts: Vec<u64> = (0..4).map(|k| sp.mats[(l >> (4 * k)) & 15]).collect();
                pts.extend(hubs.iter().map(|&h| sp.mats[h]));
                bf = bf.max(b_mat(&des, &pts).iter().map(|x| x.max(0.0)).sum());
            }
            assert!((v - bf).abs() < 1e-9, "{} {}", v, bf);
        }
    }

    #[test]
    fn far_value_orthogonal_delta3() {
        let des = Design::delta3(3);
        let m = Model { arms: vec![], k: 6 };
        let mut hubs = vec![CPoint::default(); 9];
        for k in 0..3 {
            for g in 0..3 {
                let th = 2.0 * std::f64::consts::PI * g as f64 / 3.0;
                hubs[3 * k + g].x[2 * k] = th.cos() / 3f64.sqrt();
                hubs[3 * k + g].x[2 * k + 1] = th.sin() / 3f64.sqrt();
            }
        }
        let (v, _) = far_value(&des, &m, &hubs);
        assert!((v / 3.0 - 3.0 * 3f64.sqrt()).abs() < 1e-9, "{}", v);
        // the same hubs embedded in tripod x R^6 (radius 0 on the tripod) give the same value
        let m2 = Model { arms: vec![3], k: 6 };
        assert!((far_value(&des, &m2, &hubs).0 - v).abs() < 1e-9);
    }

    #[test]
    fn identities_delta3() {
        // "merge pods" R x C x D: in factor k, hub g of merge k on arm g at radius 1/sqrt2 (so delta = 1),
        // all other hubs at the centre: value 9/sqrt3 per merge.
        let des = Design::delta3(3);
        let r = 1.0 / 2f64.sqrt();
        let mut hubs = vec![CPoint::default(); 9];
        for k in 0..3 {
            for g in 0..3 {
                hubs[3 * k + g].arm[k] = g as u8;
                hubs[3 * k + g].t[k] = r;
            }
        }
        let m = Model { arms: vec![3, 3, 3], k: 0 };
        let (v, _) = far_value(&des, &m, &hubs);
        assert!((v / 3.0 - 3.0 * 3f64.sqrt()).abs() < 1e-9, "{}", v / 3.0);
        let tm = pods_to_trees(&m, &hubs);
        let mut sc = vec![];
        let (v2, _) = far_value_tree(&des, &tm, &mut sc);
        assert!((v2 - v).abs() < 1e-9, "{} {}", v, v2);
    }

    #[test]
    fn ag_designs() {
        let d = Design::ag(3, &[0, 1, 2]);
        assert_eq!((d.edges.len(), d.nhubs()), (36, 9));
        // (sqrt3 + 3 sqrt2)/12 * 36 per merge = orthogonal price (z1 table, rho 0.498)
        assert!((d.flat_value() / 36.0 - (3f64.sqrt() + 3.0 * 2f64.sqrt()) / 12.0).abs() < 1e-12);
        let d4 = Design::ag(4, &[0, 1, 2]);
        for m in 0..3 {
            for g in 0..4 {
                assert_eq!(d4.groups[m].iter().filter(|&&x| x == g).count(), 4);
            }
        }
        // any two classes: lines meet in exactly one point
        for (a, b) in [(0, 1), (0, 2), (1, 2)] {
            for g in 0..4 {
                for h in 0..4 {
                    assert_eq!((0..16).filter(|&v| d4.groups[a][v] == g && d4.groups[b][v] == h).count(), 1);
                }
            }
        }
    }

    #[test]
    fn one_tree_node_pod_delta3() {
        let des = Design::delta3(3);
        let f = node_pod(&des, 0);
        let mut c = vec![];
        let (g, sym, cs) = one_tree_scores(&des, &f, &edge_orbits(&des), &mut c);
        assert!((g - 36.0).abs() < 1e-9 && (sym - 6.0).abs() < 1e-9 && (cs - 6.0).abs() < 1e-9, "{} {} {}", g, sym, cs);
        // nine node-tripods as a 9-factor pod product: 6 per merge
        let nh = des.nhubs();
        let mut hubs = vec![CPoint::default(); nh];
        for node in 0..9 {
            for m in 0..3 {
                let h = des.hub(m, des.groups[m][node]) - des.nlegs();
                hubs[h].arm[node] = m as u8;
                hubs[h].t[node] = 1.0;
            }
        }
        let m = Model { arms: vec![3; 9], k: 0 };
        assert!((far_value(&des, &m, &hubs).0 / 3.0 - 6.0).abs() < 1e-9);
    }

    #[test]
    fn limit_index4_subgroup() {
        // theory agent: rows / columns / diagonals in the subgroup A of index 4 on arms 1, 2, 3 at radius 1,
        // all other hubs at the centre: Phi = 27/8 for Q = Z_4 and Z_2^2.
        for qn in ["4", "2x2"] {
            let net = LimitNet::new(qn, 3);
            let m = net.q.m;
            let mut lab = vec![0; 3 * m];
            for k in 0..3 {
                lab[k * m] = k + 1; // the identity element 0 = the trivial subgroup A of index 4
            }
            let f = net.pod01(&lab, 3);
            assert!((net.phi(&f) - 27.0 / 8.0).abs() < 1e-12, "{} {}", qn, net.phi(&f));
        }
    }

    #[test]
    fn cone_calibration() {
        // crossing: plane (circle:8), cone over K33, pods:4 -> one-factor value sqrt2 per merge
        let des = Design::crossing(1.0, 1.0);
        // plane: rows at +-a/2 (directions 0, pi), columns at +-b/2 (pi/2, 3pi/2): circle with 4 vertices
        // (directions at pi/4 are needed for the legs: circle with 8 vertices)
        let g = ConeGraph::named("circle:8", 1);
        let pl = ConePlacement { hv: vec![0, 4, 2, 6], r: vec![0.5; 4] };
        let (gm, _, _) = cone_gamma(&des, &g, &pl);
        assert!(((2.0 * gm).sqrt() / 2.0 - 2f64.sqrt()).abs() < 1e-9, "{}", gm);
        // direct product evaluation with one factor agrees (no symmetrisation needed here)
        let b = cone_product_b(&des, &[(&g, &pl)]);
        assert!((value(&b) - 2f64.sqrt()).abs() < 1e-9, "{:?}", b);
        // Delta3, pods:3 node-tripod: Gamma 36
        let d3 = Design::delta3(3);
        let g3 = ConeGraph::named("pods:3", 1);
        let mut pl3 = ConePlacement { hv: vec![0; 9], r: vec![0.0; 9] };
        for (m, &h) in [0usize, 3, 6].iter().enumerate() {
            pl3.hv[h] = m;
            pl3.r[h] = 1.0;
        }
        assert!((cone_gamma(&d3, &g3, &pl3).0 - 36.0).abs() < 1e-9);
        // nine tripods as an explicit 9-factor cone product: b = (6,6,6)
        let mut pls = vec![];
        for node in 0..9 {
            let mut q = ConePlacement { hv: vec![0; 9], r: vec![0.0; 9] };
            for m in 0..3 {
                let h = d3.hub(m, d3.groups[m][node]) - d3.nlegs();
                q.hv[h] = m;
                q.r[h] = 1.0;
            }
            pls.push(q);
        }
        let fs: Vec<(&ConeGraph, &ConePlacement)> = pls.iter().map(|q| (&g3, q)).collect();
        let b = cone_product_b(&d3, &fs);
        for x in &b {
            assert!((x - 6.0).abs() < 1e-9, "{:?}", b);
        }
        // graph sanity
        assert_eq!(ConeGraph::named("heawood", 1).n, 14);
        assert!((ConeGraph::named("heawood", 1).girth() - 2.0 * std::f64::consts::PI).abs() < 1e-9);
        assert_eq!(ConeGraph::named("gq22", 1).n, 30);
        assert!((ConeGraph::named("gq22", 2).girth() - 2.0 * std::f64::consts::PI).abs() < 1e-9);
        assert_eq!(ConeGraph::named("pg3", 1).n, 26);
    }

    #[test]
    fn filtrations_q1_values() {
        // q1-notes Theorem A: F_2^2 (g = 4) and F_2^3 (g = 8) nets: min_k b_k / E >= 0.4828, 0.5825
        let ms: Vec<(usize, f64)> = if std::env::var("PF_SLOW").is_ok() { vec![(2, 0.4828), (3, 0.5825)] } else { vec![(2, 0.4828)] };
        for (m, target) in ms {
            let des = Design::group_net(if m == 2 { "2x2" } else { "2x2x2" });
            let fs = FiltSpace::new(2, m + 2, 200_000, 1);
            assert!(fs.exhaustive);
            let pl = q1_placement(&des, &fs, m);
            let mut cache = Default::default();
            let sc = filt_scores(&des, &fs, &pl, &mut cache, true);
            let e = des.edges.len() as f64;
            // the per-edge optimum maximises sum_k; ties on rank-one edges are broken arbitrarily, so the
            // balanced value is the merge-average (attained by tie choices / the GL-orbit symmetrisation)
            assert!((sc.avg / e - target).abs() < 2e-4, "m={} avg b/E = {} (b = {:?})", m, sc.avg / e, sc.b);
            eprintln!("m={} avg b/E = {:.6} min b/E = {:.6} CS {:.6} frames {}", m, sc.avg / e, sc.minb / e, sc.cs / e, fs.nframes);
        }
        // in N = 2 a hyperplane is a point: ker(1,0) = <(0,1)>, ker(1,1) = <(1,1)>; edge values must agree
        let fs2 = FiltSpace::new(3, 2, 1000, 1);
        let p01 = fs2.point_index(&[0, 1]);
        let p10 = fs2.point_index(&[1, 0]);
        let p11 = fs2.point_index(&[1, 1]);
        let p12 = fs2.point_index(&[1, 2]);
        // ker(1,2) over F_3 = <(1,1)>, ker(1,1) = <(1,2)>
        let w = [1.0, 0.7];
        let a = filt_edge(&fs2, &[(p01, 0, 1.3, 0.2), (p11, 0, 0.8, -0.4)], &[(p12, 0, 1.0, 0.1), (p10, 0, 0.5, 0.0)], &w);
        let b = filt_edge(&fs2, &[(p10, 1, 1.3, 0.2), (p12, 1, 0.8, -0.4)], &[(p11, 1, 1.0, 0.1), (p01, 1, 0.5, 0.0)], &w);
        assert!((a.0 - b.0).abs() < 1e-9, "{} {}", a.0, b.0);
        assert!((filt_d2(&fs2, (p01, 0, 1.3, 0.2), (p11, 0, 0.8, -0.4)) - filt_d2(&fs2, (p10, 1, 1.3, 0.2), (p12, 1, 0.8, -0.4))).abs() < 1e-12);
        // MNP: hull of {e1 - e2} -> distance sqrt2
        let x = mnp_supports(3, &[(1, 1.0)], &[(2, 1.0)]);
        assert!(((x[0] * x[0] + x[1] * x[1]).sqrt() - 2f64.sqrt()).abs() < 1e-12);
    }

    #[test]
    fn group_sizes() {
        assert_eq!(gl(2).len(), 6);
        assert_eq!(gl(3).len(), 168);
        assert_eq!(linear_isometries(2).len(), 72);
    }
}
