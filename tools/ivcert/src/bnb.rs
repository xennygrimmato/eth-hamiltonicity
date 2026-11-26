//! Generic branch-and-bound prover for  f(x) >= c  on a box, and the leaf tests shared by the prover
//! and the checker.
//!
//! Leaf tests (each returns a rigorous lower bound of f on the closed float box B, or -inf / NaN):
//!   N  natural interval extension                     f(B)
//!   M  mean-value form at the centre c                f(c) + grad f(B) . (B - c)
//!   T  second-order Taylor form at c                  f(c) + grad f(c) . (B - c) + 1/2 (B-c)^T Hess f(B) (B-c)
//!   C  certified convexity with anchor x* in B:       Hess f(B) certified PD (congruence-Gershgorin with an
//!      explicit matrix P stored in the certificate, or interval Cholesky)  =>  f convex on B  =>
//!      f(x) >= f(x*) + grad f(x*) . (x - x*)  for x in B, bounded below by interval evaluation.
//!      With x* a critical point (exact zero gradient enclosure), the bound is f(x*) exactly, which is
//!      how equality points are closed.
//!   P  pruned by symmetry: the problem asserts the box misses a closed fundamental domain R of its
//!      symmetry group (every point of the domain has an image in R with the same value of f).
//! Splitting: bisection of the widest coordinate at the float midpoint, so children cover the parent
//! exactly. The certificate is the preorder traversal of the resulting tree.

use crate::ad::{Jet1, Jet2, Scalar};
use crate::interval::I;
use crate::linalg;
use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;

pub type BoxN<const N: usize> = [I; N];

pub trait Problem<const N: usize>: Sync + Send {
    /// Registry name, including parameters (the checker rebuilds the problem from it).
    fn name(&self) -> String;
    /// Human-readable statement.
    fn statement(&self) -> String;
    /// Float box containing the (true) domain.
    fn domain(&self) -> BoxN<N>;
    /// Claimed lower bound c: the claim is f >= c on the domain.
    fn bound(&self) -> f64;
    /// The function, generically over the scalar type.
    fn eval<T: Scalar<N>>(&self, x: &[T; N]) -> T;
    /// Known minimisers (anchor points for the convexity test). Must be exact floats.
    fn special_points(&self) -> Vec<[f64; N]> {
        vec![]
    }
    /// Return true only if the closed box contains no point of the problem's fundamental domain.
    fn outside_fundamental(&self, _b: &BoxN<N>) -> bool {
        false
    }
    /// Return true only if f >= c on the closed box is established elsewhere (an analytic lemma or a
    /// separate certificate named in `excluded_note`). Leaves closed this way are marked X.
    fn excluded(&self, _b: &BoxN<N>) -> bool {
        false
    }
    fn excluded_note(&self) -> String {
        String::new()
    }
    /// Coordinates forming the "linear block" L of the gain test (see `lb_gain_h`).
    fn linear_block(&self) -> [bool; N] {
        [false; N]
    }
    /// The problem asserts (with an analytic proof in its documentation) that the gradient vanishes
    /// exactly at every special point.
    fn anchors_critical(&self) -> bool {
        false
    }
    /// The problem asserts f is C^1 on its domain at every point where its Jet1 is valid.
    fn c1(&self) -> bool {
        false
    }
}

// ----------------------------------------------------------------- leaf tests

pub fn eval_box<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> I {
    p.eval::<I>(b)
}

pub fn eval_point<const N: usize, P: Problem<N>>(p: &P, x: &[f64; N]) -> I {
    let b: [I; N] = std::array::from_fn(|i| I::point(x[i]));
    p.eval::<I>(&b)
}

fn jet1_at<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> Jet1<N> {
    let x: [Jet1<N>; N] = std::array::from_fn(|i| Jet1::var(b[i], i));
    p.eval(&x)
}

fn jet2_at<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> Jet2<N> {
    let x: [Jet2<N>; N] = std::array::from_fn(|i| Jet2::var(b[i], i));
    p.eval(&x)
}

pub fn center<const N: usize>(b: &BoxN<N>) -> [f64; N] {
    std::array::from_fn(|i| b[i].mid())
}

fn lo_or_neg(x: I) -> f64 {
    if x.is_valid() {
        x.lo
    } else {
        f64::NEG_INFINITY
    }
}

pub fn lb_natural<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> f64 {
    lo_or_neg(eval_box(p, b))
}

pub fn lb_meanvalue<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> f64 {
    let c = center(b);
    let fc = eval_point(p, &c);
    let g = jet1_at(p, b);
    let mut s = fc;
    for i in 0..N {
        s = s + g.d[i] * (b[i] - I::point(c[i]));
    }
    // the natural bound is also valid; take the better
    lo_or_neg(s).max(lo_or_neg(g.v))
}

/// Taylor-2 bound given a precomputed Hessian enclosure over b.
fn lb_taylor2_h<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, h: &[[I; N]; N]) -> f64 {
    let c = center(b);
    let cp: [I; N] = std::array::from_fn(|i| I::point(c[i]));
    let jc = jet1_at(p, &cp);
    let d: [I; N] = std::array::from_fn(|i| b[i] - cp[i]);
    let mut s = jc.v;
    for i in 0..N {
        s = s + jc.d[i] * d[i];
    }
    let mut q = I::point(0.0);
    for i in 0..N {
        q = q + h[i][i].meet(&h[i][i]) * I::sqr(&d[i]);
        for j in i + 1..N {
            q = q + I::point(2.0) * h[i][j] * (d[i] * d[j]);
        }
    }
    lo_or_neg(s + I::point(0.5) * q)
}

pub fn lb_taylor2<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>) -> f64 {
    let j = jet2_at(p, b);
    lb_taylor2_h(p, b, &j.hessian())
}

/// Convexity leaf. `pm = None` means interval Cholesky.
pub fn lb_convex_h<const N: usize, P: Problem<N>>(
    p: &P,
    b: &BoxN<N>,
    h: &[[I; N]; N],
    xs: &[f64; N],
    pm: &Option<[[f64; N]; N]>,
) -> f64 {
    for i in 0..N {
        if !b[i].contains(xs[i]) {
            return f64::NEG_INFINITY;
        }
    }
    let pd = match pm {
        Some(pp) => linalg::congruence_gershgorin(h, pp),
        None => linalg::interval_cholesky(h),
    };
    if !pd {
        return f64::NEG_INFINITY;
    }
    anchor_bound(p, b, xs)
}

/// Supporting-hyperplane bound at the anchor, valid on b when f is convex on a convex set containing
/// b and x*: f(x*) + grad f(x*) . (b - x*). If the problem declares its anchors critical
/// (grad f(x*) = 0 exactly, proved analytically), the bound is f(x*), after checking that the computed
/// gradient enclosure contains 0.
pub fn anchor_bound<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, xs: &[f64; N]) -> f64 {
    let xp: [I; N] = std::array::from_fn(|i| I::point(xs[i]));
    let j = jet1_at(p, &xp);
    if p.anchors_critical() {
        if j.d.iter().all(|g| g.is_valid() && g.contains_zero()) {
            return lo_or_neg(j.v);
        }
        return f64::NEG_INFINITY;
    }
    let mut s = j.v;
    for i in 0..N {
        s = s + j.d[i] * (b[i] - xp[i]);
    }
    lo_or_neg(s)
}

/// Preorder token of a positive-definiteness cover: split coordinate d, or a leaf proved PD with the
/// preconditioner P (row-major) or by interval Cholesky (None).
#[derive(Clone, Debug)]
pub enum PdTok {
    Split(usize),
    Leaf(Option<Vec<f64>>),
}

fn pd_box<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, pm: &Option<Vec<f64>>) -> bool {
    let h = jet2_at(p, b).hessian();
    match pm {
        Some(v) => {
            if v.len() != N * N {
                return false;
            }
            let m: [[f64; N]; N] = std::array::from_fn(|i| std::array::from_fn(|j| v[i * N + j]));
            linalg::congruence_gershgorin(&h, &m)
        }
        None => linalg::interval_cholesky(&h),
    }
}

/// Search a PD cover of b by bisection (at most `budget` leaves).
pub fn find_pd_cover<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, budget: &mut i64, depth: u32) -> Option<Vec<PdTok>> {
    *budget -= 1;
    if *budget < 0 || depth > 40 {
        return None;
    }
    let h = jet2_at(p, b).hessian();
    if let Some(pp) = linalg::choose_p(&h) {
        if linalg::congruence_gershgorin(&h, &pp) {
            return Some(vec![PdTok::Leaf(Some(pp.iter().flat_map(|r| r.iter().copied()).collect()))]);
        }
    } else {
        // midpoint Hessian not PD: no hope on this box
        return None;
    }
    if linalg::interval_cholesky(&h) {
        return Some(vec![PdTok::Leaf(None)]);
    }
    let d = split_dim(b);
    let (l, r) = split(b, d)?;
    let mut a = find_pd_cover(p, &l, budget, depth + 1)?;
    let c = find_pd_cover(p, &r, budget, depth + 1)?;
    let mut out = vec![PdTok::Split(d)];
    out.append(&mut a);
    out.extend(c);
    Some(out)
}

/// Verify a PD cover of b given as preorder tokens; true iff every leaf box is certified PD and the
/// tokens are exactly consumed.
pub fn check_pd_cover<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, toks: &[PdTok]) -> bool {
    let mut stack = vec![*b];
    let mut k = 0;
    while let Some(bx) = stack.pop() {
        let Some(t) = toks.get(k) else { return false };
        k += 1;
        match t {
            PdTok::Split(d) => {
                if *d >= N {
                    return false;
                }
                let Some((l, r)) = split(&bx, *d) else { return false };
                stack.push(r);
                stack.push(l);
            }
            PdTok::Leaf(pm) => {
                if !pd_box(p, &bx, pm) {
                    return false;
                }
            }
        }
    }
    k == toks.len()
}

pub fn hull_with<const N: usize>(b: &BoxN<N>, xs: &[f64; N]) -> BoxN<N> {
    std::array::from_fn(|i| I::new(b[i].lo.min(xs[i]), b[i].hi.max(xs[i])))
}

/// Hull-convexity leaf: f convex on H = hull(b, x*) (Hessian PD on every box of a cover of H; for a
/// cover with more than one box the problem must declare f to be C^1 on its domain, so that a C^1
/// function, piecewise C^2 with PD Hessian, is convex along every segment), hence f >= anchor bound.
pub fn lb_hullconvex<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, xs: &[f64; N], toks: &[PdTok]) -> f64 {
    if toks.len() > 1 && !p.c1() {
        return f64::NEG_INFINITY;
    }
    let hb = hull_with(b, xs);
    if !check_pd_cover(p, &hb, toks) {
        return f64::NEG_INFINITY;
    }
    anchor_bound(p, b, xs)
}

pub fn lb_convex<const N: usize, P: Problem<N>>(
    p: &P,
    b: &BoxN<N>,
    xs: &[f64; N],
    pm: &Option<[[f64; N]; N]>,
) -> f64 {
    let j = jet2_at(p, b);
    lb_convex_h(p, b, &j.hessian(), xs, pm)
}

/// Gain test ("partial convexity + linear gain"), anchor x* in B, coordinates split into the convex
/// block C and the linear block L (problem's `linear_block`). Requirements: for k in L the box lies on
/// one side of x*_k (sign s_k); gamma := min_k inf( g_k(x*) s_k ) > 0. With d = x - x*, Taylor-2:
///   f(x) - f(x*) >= g.d + 1/2 d^T H d,  H in Hess f(B),
///   g_L.d_L >= gamma S1 (S1 = |d_L|_1),  1/2 d_C^T H_CC d_C >= 1/2 lam |d_C|^2 (lam certified),
///   |d_C^T H_CL d_L| <= beta |d_C| S2 (beta >= ||H_CL||_F, S2 = |d_L|_2),
///   1/2 d_L^T H_LL d_L >= 1/2 mu S2^2 (mu = Gershgorin lower bound),  |g_C.d_C| <= |g_C| |d_C|.
/// Minimising over |d_C| >= 0:  >= -(|g_C| + beta S2)^2 / (2 lam) + gamma S1 + mu S2^2 / 2, and
/// with S2^2 <= S1 w_L (w_L = max_k |d_k|):
///   g_C == 0 :  f(x) - f(x*) >= S1 (gamma - w_L (beta^2/(2 lam) + max(0,-mu)/2))
///   otherwise:  f(x) - f(x*) >= -|g_C|^2/lam + S1 (gamma - w_L (beta^2/lam + max(0,-mu)/2)).
/// If the bracket is >= 0 the bound is f(x*) (resp. f(x*) - |g_C|^2/lam).
pub fn lb_gain_h<const N: usize, P: Problem<N>>(
    p: &P,
    b: &BoxN<N>,
    h: &[[I; N]; N],
    xs: &[f64; N],
    pm: &[f64],
) -> f64 {
    let lmask = p.linear_block();
    for i in 0..N {
        if !b[i].contains(xs[i]) {
            return f64::NEG_INFINITY;
        }
    }
    let cidx: Vec<usize> = (0..N).filter(|&i| !lmask[i]).collect();
    let lidx: Vec<usize> = (0..N).filter(|&i| lmask[i]).collect();
    if lidx.is_empty() {
        return f64::NEG_INFINITY;
    }
    let xp: [I; N] = std::array::from_fn(|i| I::point(xs[i]));
    let j = jet1_at(p, &xp);
    if !j.v.is_valid() {
        return f64::NEG_INFINITY;
    }
    // gamma and w_L
    let mut gamma = f64::INFINITY;
    let mut wl = 0.0f64;
    for &k in &lidx {
        let d = b[k] - xp[k];
        if d.lo == 0.0 && d.hi == 0.0 {
            continue;
        }
        let sg = if d.lo >= 0.0 {
            1.0
        } else if d.hi <= 0.0 {
            -1.0
        } else {
            return f64::NEG_INFINITY;
        };
        let gk = j.d[k] * I::point(sg);
        if !gk.is_valid() {
            return f64::NEG_INFINITY;
        }
        gamma = gamma.min(gk.lo);
        wl = wl.max(d.mag());
    }
    if !(gamma > 0.0) {
        return f64::NEG_INFINITY;
    }
    // symmetric Hessian enclosure
    let mut hs = *h;
    for a in 0..N {
        for c in 0..N {
            hs[a][c] = h[a][c].meet(&h[c][a]);
            if !hs[a][c].is_valid() || hs[a][c].lo > hs[a][c].hi {
                return f64::NEG_INFINITY;
            }
        }
    }
    let hll: Vec<Vec<I>> = lidx.iter().map(|&a| lidx.iter().map(|&c| hs[a][c]).collect()).collect();
    let mu = linalg::gershgorin_lb_dyn(&hll);
    if !mu.is_finite() {
        return f64::NEG_INFINITY;
    }
    let negmu = I::point((-mu).max(0.0));
    let mut gc2 = I::point(0.0);
    let mut k_coef = I::point(0.5) * negmu; // max(0,-mu)/2
    let mut shift = I::point(0.0);
    if !cidx.is_empty() {
        let hcc: Vec<Vec<I>> = cidx.iter().map(|&a| cidx.iter().map(|&c| hs[a][c]).collect()).collect();
        let lam = linalg::lambda_min_lb_dyn(&hcc, pm);
        if !(lam > 0.0) {
            return f64::NEG_INFINITY;
        }
        let lam = I::new(lam, lam);
        let mut beta2 = I::point(0.0);
        for &a in &cidx {
            for &c in &lidx {
                beta2 = beta2 + I::sqr(&I::point(hs[a][c].mag()));
            }
        }
        for &a in &cidx {
            if !j.d[a].is_valid() {
                return f64::NEG_INFINITY;
            }
            gc2 = gc2 + I::sqr(&I::point(j.d[a].mag()));
        }
        if gc2.hi == 0.0 {
            k_coef = k_coef + beta2 / (I::point(2.0) * lam);
        } else {
            k_coef = k_coef + beta2 / lam;
            shift = gc2 / lam;
        }
    }
    let bracket = I::point(gamma) - I::point(wl) * k_coef;
    if !bracket.is_valid() || !(bracket.lo >= 0.0) {
        return f64::NEG_INFINITY;
    }
    lo_or_neg(j.v - shift)
}

pub fn lb_gain<const N: usize, P: Problem<N>>(p: &P, b: &BoxN<N>, xs: &[f64; N], pm: &[f64]) -> f64 {
    let j = jet2_at(p, b);
    lb_gain_h(p, b, &j.hessian(), xs, pm)
}

// ----------------------------------------------------------------- tree

#[derive(Clone, Debug)]
pub enum Leaf<const N: usize> {
    Natural(f64),
    MeanValue(f64),
    Taylor2(f64),
    Convex { lb: f64, xs: [f64; N], pm: Option<[[f64; N]; N]> },
    Gain { lb: f64, xs: [f64; N], pm: Vec<f64> },
    HullConvex { lb: f64, xs: [f64; N], toks: Vec<PdTok> },
    Pruned,
    Excluded,
    /// Not closed (depth limit): the run is not a proof.
    Fail { counterexample: Option<([f64; N], I)> },
}

#[derive(Debug)]
pub enum Node<const N: usize> {
    Split(usize, Box<Node<N>>, Box<Node<N>>),
    Leaf(Leaf<N>),
    /// A finished subtree already serialised to certificate lines (saves memory), with its stats and
    /// leaf count.
    Text(Vec<u8>, Stats, u64),
}

#[derive(Clone, Debug)]
pub struct Options {
    pub max_depth: u32,
    pub par_depth: u32,
    pub use_mv: bool,
    pub use_taylor2: bool,
    pub use_convex: bool,
    pub use_symmetry: bool,
    /// stop all work after the first confirmed counterexample
    pub stop_on_counterexample: bool,
    /// a counter of failing boxes after which the run is aborted
    pub max_fail: u64,
    /// hull-convexity test: try it for boxes whose hull with an anchor has every side <= this
    pub hull_max: f64,
    pub hull_budget: i64,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_depth: 64,
            par_depth: 22,
            use_mv: true,
            use_taylor2: true,
            use_convex: true,
            use_symmetry: true,
            stop_on_counterexample: true,
            max_fail: 1000,
            hull_max: 0.0,
            hull_budget: 256,
        }
    }
}

pub struct Ctx<'a, const N: usize, P: Problem<N>> {
    pub p: &'a P,
    pub opt: Options,
    pub c: f64,
    pub specials: Vec<[f64; N]>,
    pub abort: AtomicBool,
    pub nfail: AtomicU64,
    pub nodes: AtomicU64,
    pub fails: Mutex<Vec<(BoxN<N>, Option<([f64; N], I)>)>>,
}

fn closes(lb: f64, c: f64) -> bool {
    lb >= c // false for NaN
}

pub fn split<const N: usize>(b: &BoxN<N>, d: usize) -> Option<(BoxN<N>, BoxN<N>)> {
    let m = b[d].mid();
    if !(b[d].lo < m && m < b[d].hi) {
        return None;
    }
    let mut l = *b;
    let mut r = *b;
    l[d] = I::new(b[d].lo, m);
    r[d] = I::new(m, b[d].hi);
    Some((l, r))
}

pub fn split_dim<const N: usize>(b: &BoxN<N>) -> usize {
    let mut best = 0;
    let mut w = -1.0;
    for i in 0..N {
        let wi = b[i].hi - b[i].lo;
        if wi > w {
            w = wi;
            best = i;
        }
    }
    best
}

impl<'a, const N: usize, P: Problem<N>> Ctx<'a, N, P> {
    pub fn new(p: &'a P, opt: Options) -> Self {
        Ctx {
            p,
            opt,
            c: p.bound(),
            specials: p.special_points(),
            abort: AtomicBool::new(false),
            nfail: AtomicU64::new(0),
            nodes: AtomicU64::new(0),
            fails: Mutex::new(vec![]),
        }
    }

    fn fail(&self, b: &BoxN<N>, ce: Option<([f64; N], I)>) -> Node<N> {
        let n = self.nfail.fetch_add(1, Ordering::Relaxed) + 1;
        if n >= self.opt.max_fail || (ce.is_some() && self.opt.stop_on_counterexample) {
            self.abort.store(true, Ordering::Relaxed);
        }
        self.fails.lock().unwrap().push((*b, ce));
        Node::Leaf(Leaf::Fail { counterexample: ce })
    }

    /// Try to close the box without splitting.
    pub fn try_leaf(&self, b: &BoxN<N>) -> Option<Leaf<N>> {
        let p = self.p;
        if self.opt.use_symmetry && p.outside_fundamental(b) {
            return Some(Leaf::Pruned);
        }
        if p.excluded(b) {
            return Some(Leaf::Excluded);
        }
        let nat = lb_natural(p, b);
        if closes(nat, self.c) {
            return Some(Leaf::Natural(nat));
        }
        if self.opt.use_mv {
            let mv = lb_meanvalue(p, b);
            if closes(mv, self.c) {
                return Some(Leaf::MeanValue(mv));
            }
        }
        let anchor = self.specials.iter().find(|x| (0..N).all(|i| b[i].contains(x[i])));
        if self.opt.use_taylor2 || (self.opt.use_convex && anchor.is_some()) {
            let j = jet2_at(p, b);
            let h = j.hessian();
            if self.opt.use_convex {
                if let Some(xs) = anchor {
                    if let Some(pm) = linalg::choose_p(&h) {
                        let lb = lb_convex_h(p, b, &h, xs, &Some(pm));
                        if closes(lb, self.c) {
                            return Some(Leaf::Convex { lb, xs: *xs, pm: Some(pm) });
                        }
                    }
                    let lb = lb_convex_h(p, b, &h, xs, &None);
                    if closes(lb, self.c) {
                        return Some(Leaf::Convex { lb, xs: *xs, pm: None });
                    }
                }
            }
            if self.opt.use_convex {
                if let Some(xs) = anchor {
                    let lm = p.linear_block();
                    if lm.iter().any(|&x| x) {
                        let cidx: Vec<usize> = (0..N).filter(|&i| !lm[i]).collect();
                        let hcc: Vec<Vec<I>> = cidx.iter().map(|&a| cidx.iter().map(|&c| h[a][c]).collect()).collect();
                        let pm = if cidx.is_empty() { Some(vec![]) } else { linalg::choose_p_dyn(&hcc) };
                        if let Some(pm) = pm {
                            let lb = lb_gain_h(p, b, &h, xs, &pm);
                            if closes(lb, self.c) {
                                return Some(Leaf::Gain { lb, xs: *xs, pm });
                            }
                        }
                    }
                }
            }
            if self.opt.use_taylor2 {
                let t = lb_taylor2_h(p, b, &h);
                if closes(t, self.c) {
                    return Some(Leaf::Taylor2(t));
                }
            }
        }
        if self.opt.use_convex && self.opt.hull_max > 0.0 {
            for xs in &self.specials {
                let hb = hull_with(b, xs);
                if hb.iter().all(|x| x.hi - x.lo <= self.opt.hull_max) {
                    let mut budget = self.opt.hull_budget;
                    if let Some(toks) = find_pd_cover(p, &hb, &mut budget, 0) {
                        let lb = lb_hullconvex(p, b, xs, &toks);
                        if closes(lb, self.c) {
                            return Some(Leaf::HullConvex { lb, xs: *xs, toks });
                        }
                    }
                }
            }
        }
        None
    }

    pub fn solve(&self, b: &BoxN<N>, depth: u32) -> Node<N> {
        if self.abort.load(Ordering::Relaxed) {
            return Node::Leaf(Leaf::Fail { counterexample: None });
        }
        let k = self.nodes.fetch_add(1, Ordering::Relaxed) + 1;
        if k % (1 << 22) == 0 {
            eprintln!("[progress] {} nodes, {} failures, current box {:?}", k, self.nfail.load(Ordering::Relaxed), b);
        }
        if let Some(l) = self.try_leaf(b) {
            return Node::Leaf(l);
        }
        // counterexample check at the centre: f(c) < bound proved by exact evaluation
        let c = center(b);
        let fc = eval_point(self.p, &c);
        if fc.is_valid() && fc.hi < self.c {
            return self.fail(b, Some((c, fc)));
        }
        if depth >= self.opt.max_depth {
            return self.fail(b, None);
        }
        let d = split_dim(b);
        let Some((l, r)) = split(b, d) else {
            return self.fail(b, None);
        };
        if depth < self.opt.par_depth {
            let (a, bb) = rayon::join(|| self.solve(&l, depth + 1), || self.solve(&r, depth + 1));
            Node::Split(d, Box::new(a), Box::new(bb))
        } else {
            let a = self.solve(&l, depth + 1);
            let bb = self.solve(&r, depth + 1);
            let node = Node::Split(d, Box::new(a), Box::new(bb));
            if depth == self.opt.par_depth {
                let mut buf = Vec::new();
                let mut nl = 0u64;
                crate::cert::write_tree(&node, &mut buf, &mut nl).expect("write to memory");
                let st = stats(&node);
                return Node::Text(buf, st, nl);
            }
            node
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub natural: u64,
    pub meanvalue: u64,
    pub taylor2: u64,
    pub convex: u64,
    pub pruned: u64,
    pub excluded: u64,
    pub gain: u64,
    pub hullconvex: u64,
    pub fail: u64,
    pub splits: u64,
    pub max_depth: u32,
    /// minimum over closing leaves of their certified lower bound
    pub min_lb: f64,
    /// minimum certified lower bound over leaves that are not convexity leaves
    pub min_lb_nonconvex: f64,
}

pub fn stats<const N: usize>(n: &Node<N>) -> Stats {
    let mut s = Stats { min_lb: f64::INFINITY, min_lb_nonconvex: f64::INFINITY, ..Default::default() };
    fn go<const N: usize>(n: &Node<N>, d: u32, s: &mut Stats) {
        s.max_depth = s.max_depth.max(d);
        match n {
            Node::Text(_, t, _) => {
                s.natural += t.natural;
                s.meanvalue += t.meanvalue;
                s.taylor2 += t.taylor2;
                s.convex += t.convex;
                s.gain += t.gain;
                s.hullconvex += t.hullconvex;
                s.pruned += t.pruned;
                s.excluded += t.excluded;
                s.fail += t.fail;
                s.splits += t.splits;
                s.max_depth = s.max_depth.max(d + t.max_depth);
                s.min_lb = s.min_lb.min(t.min_lb);
                s.min_lb_nonconvex = s.min_lb_nonconvex.min(t.min_lb_nonconvex);
            }
            Node::Split(_, a, b) => {
                s.splits += 1;
                go(a, d + 1, s);
                go(b, d + 1, s);
            }
            Node::Leaf(l) => match l {
                Leaf::Natural(x) => {
                    s.natural += 1;
                    s.min_lb = s.min_lb.min(*x);
                    s.min_lb_nonconvex = s.min_lb_nonconvex.min(*x);
                }
                Leaf::MeanValue(x) => {
                    s.meanvalue += 1;
                    s.min_lb = s.min_lb.min(*x);
                    s.min_lb_nonconvex = s.min_lb_nonconvex.min(*x);
                }
                Leaf::Taylor2(x) => {
                    s.taylor2 += 1;
                    s.min_lb = s.min_lb.min(*x);
                    s.min_lb_nonconvex = s.min_lb_nonconvex.min(*x);
                }
                Leaf::Convex { lb, .. } => {
                    s.convex += 1;
                    s.min_lb = s.min_lb.min(*lb);
                }
                Leaf::Gain { lb, .. } => {
                    s.gain += 1;
                    s.min_lb = s.min_lb.min(*lb);
                }
                Leaf::HullConvex { lb, .. } => {
                    s.hullconvex += 1;
                    s.min_lb = s.min_lb.min(*lb);
                }
                Leaf::Pruned => s.pruned += 1,
                Leaf::Excluded => s.excluded += 1,
                Leaf::Fail { .. } => s.fail += 1,
            },
        }
    }
    go(n, 0, &mut s);
    s
}

pub struct Outcome<const N: usize> {
    pub tree: Node<N>,
    pub stats: Stats,
    pub fails: Vec<(BoxN<N>, Option<([f64; N], I)>)>,
    pub proved: bool,
    pub seconds: f64,
}

pub fn prove<const N: usize, P: Problem<N>>(p: &P, opt: Options) -> Outcome<N> {
    let t0 = std::time::Instant::now();
    let ctx = Ctx::new(p, opt);
    let tree = ctx.solve(&p.domain(), 0);
    let st = stats(&tree);
    let mut fails = ctx.fails.into_inner().unwrap();
    fails.sort_by(|a, b| {
        let ka: Vec<f64> = a.0.iter().map(|x| x.lo).collect();
        let kb: Vec<f64> = b.0.iter().map(|x| x.lo).collect();
        ka.partial_cmp(&kb).unwrap_or(std::cmp::Ordering::Equal)
    });
    let proved = st.fail == 0;
    Outcome { tree, stats: st, fails, proved, seconds: t0.elapsed().as_secs_f64() }
}

/// Re-verify every leaf of a tree (used by the checker after parsing): returns the number of
/// leaves and the list of offending leaves (index, reason).
pub fn verify_leaves<const N: usize, P: Problem<N>>(
    p: &P,
    leaves: &[(BoxN<N>, Leaf<N>)],
) -> Vec<(usize, String)> {
    let c = p.bound();
    let bad: Vec<(usize, String)> = leaves
        .par_iter()
        .enumerate()
        .filter_map(|(k, (b, l))| {
            let ok = match l {
                Leaf::Pruned => p.outside_fundamental(b),
                Leaf::Natural(_) => closes(lb_natural(p, b), c),
                Leaf::MeanValue(_) => closes(lb_meanvalue(p, b), c),
                Leaf::Taylor2(_) => closes(lb_taylor2(p, b), c),
                Leaf::Convex { xs, pm, .. } => closes(lb_convex(p, b, xs, pm), c),
                Leaf::Gain { xs, pm, .. } => closes(lb_gain(p, b, xs, pm), c),
                Leaf::HullConvex { xs, toks, .. } => closes(lb_hullconvex(p, b, xs, toks), c),
                Leaf::Excluded => p.excluded(b),
                Leaf::Fail { .. } => false,
            };
            if ok {
                None
            } else {
                Some((k, format!("leaf {k} ({:?}) not verified on box {:?}", l, b)))
            }
        })
        .collect();
    bad
}
