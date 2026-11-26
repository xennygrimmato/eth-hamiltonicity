//! Constrained minimisation of linear objectives (ratios of linear forms in the distances) over
//! sets cut out by `metric::Constraint`s, with parallel multistart and a KKT polishing step that
//! reports active constraints and multipliers (for hand / exact certification).
//!
//! Problem form:   minimise  N.x   subject to  D.x = 1,  g_k(x) <= 0,  lo <= x <= hi.
//! Because every constraint family in `metric` is homogeneous, this is the same as minimising the
//! ratio N.x / D.x over the cone {g <= 0}.

use crate::metric::Constraint;
use nalgebra::{DMatrix, DVector};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use rayon::prelude::*;

#[derive(Clone, Debug)]
pub struct RatioProblem {
    pub num: Vec<f64>,
    pub den: Vec<f64>,
    pub cons: Vec<Constraint>,
    pub lo: Vec<f64>,
    pub hi: Vec<f64>,
}

impl RatioProblem {
    pub fn new(num: Vec<f64>, den: Vec<f64>, cons: Vec<Constraint>) -> Self {
        let n = num.len();
        RatioProblem { num, den, cons, lo: vec![0.0; n], hi: vec![f64::INFINITY; n] }
    }
    pub fn nvar(&self) -> usize {
        self.num.len()
    }
    pub fn ratio(&self, x: &[f64]) -> f64 {
        dot(&self.num, x) / dot(&self.den, x)
    }
    pub fn max_violation(&self, x: &[f64]) -> f64 {
        let s = dot(&self.den, x);
        let xs: Vec<f64> = x.iter().map(|v| v / s).collect();
        let mut w = self.cons.iter().map(|c| c.value(&xs)).fold(f64::NEG_INFINITY, f64::max);
        for i in 0..x.len() {
            w = w.max(self.lo[i] - xs[i]).max(xs[i] - self.hi[i]);
        }
        w
    }
}

#[derive(Clone, Debug)]
pub struct Opts {
    pub outer: usize,
    pub inner: usize,
    pub mu0: f64,
    pub mu_growth: f64,
    pub tol: f64,
    pub active_tol: f64,
    pub polish: bool,
}

impl Default for Opts {
    fn default() -> Self {
        Opts { outer: 40, inner: 3000, mu0: 10.0, mu_growth: 3.0, tol: 1e-10, active_tol: 1e-6, polish: true }
    }
}

#[derive(Clone, Debug)]
pub struct Solution {
    pub x: Vec<f64>,
    pub value: f64,
    pub max_violation: f64,
    /// (constraint index, multiplier) for active constraints after polishing.
    pub active: Vec<(usize, f64)>,
    /// variables at their lower bound, with bound multipliers.
    pub at_lower: Vec<(usize, f64)>,
    pub kkt_residual: f64,
    pub polished: bool,
}

#[inline]
pub fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

/// Projected gradient with Barzilai-Borwein steps and Armijo backtracking on a box.
/// `fg` returns f(x) and writes the gradient into the slice.
pub fn minimize_box<F>(mut fg: F, x0: &[f64], lo: &[f64], hi: &[f64], iters: usize, tol: f64) -> (Vec<f64>, f64)
where
    F: FnMut(&[f64], &mut [f64]) -> f64,
{
    let n = x0.len();
    let proj = |x: &mut [f64]| {
        for i in 0..n {
            x[i] = x[i].max(lo[i]).min(hi[i]);
        }
    };
    let mut x = x0.to_vec();
    proj(&mut x);
    let mut g = vec![0.0; n];
    let mut f = fg(&x, &mut g);
    let mut step = 1e-2;
    let mut xn = vec![0.0; n];
    let mut gn = vec![0.0; n];
    for _ in 0..iters {
        // projected gradient norm
        let mut pg = 0.0;
        for i in 0..n {
            let t = (x[i] - g[i]).max(lo[i]).min(hi[i]) - x[i];
            pg += t * t;
        }
        if pg.sqrt() < tol {
            break;
        }
        let mut accepted = false;
        let mut s = step;
        for _ in 0..60 {
            for i in 0..n {
                xn[i] = x[i] - s * g[i];
            }
            proj(&mut xn);
            let fnew = fg(&xn, &mut gn);
            let mut dec = 0.0;
            for i in 0..n {
                dec += g[i] * (x[i] - xn[i]);
            }
            if fnew <= f - 1e-4 * dec || dec <= 1e-300 {
                accepted = fnew <= f || dec <= 1e-300;
                if accepted {
                    // BB step
                    let mut sy = 0.0;
                    let mut ss = 0.0;
                    for i in 0..n {
                        let si = xn[i] - x[i];
                        let yi = gn[i] - g[i];
                        sy += si * yi;
                        ss += si * si;
                    }
                    step = if sy > 1e-300 { (ss / sy).clamp(1e-12, 1e6) } else { (s * 2.0).min(1e6) };
                    x.copy_from_slice(&xn);
                    g.copy_from_slice(&gn);
                    f = fnew;
                }
                break;
            }
            s *= 0.5;
        }
        if !accepted {
            break;
        }
    }
    (x, f)
}

/// Augmented-Lagrangian solve from one start, followed by optional KKT polish.
pub fn solve_from(p: &RatioProblem, x0: &[f64], o: &Opts) -> Solution {
    let m = p.cons.len();
    let mut lam = vec![0.0; m];
    let mut nu = 0.0; // multiplier of D.x = 1
    let mut mu = o.mu0;
    let s0 = dot(&p.den, x0).max(1e-300);
    let mut x: Vec<f64> = x0.iter().map(|v| v / s0).collect();
    for _ in 0..o.outer {
        let lamc = lam.clone();
        let (xn, _) = minimize_box(
            |x, g| {
                for gi in g.iter_mut() {
                    *gi = 0.0;
                }
                let mut f = dot(&p.num, x);
                for (i, gi) in g.iter_mut().enumerate() {
                    *gi += p.num[i];
                }
                let h = dot(&p.den, x) - 1.0;
                f += nu * h + 0.5 * mu * h * h;
                for (i, gi) in g.iter_mut().enumerate() {
                    *gi += (nu + mu * h) * p.den[i];
                }
                for (k, c) in p.cons.iter().enumerate() {
                    let v = c.value(x);
                    let t = (lamc[k] + mu * v).max(0.0);
                    if t > 0.0 {
                        f += (t * t - lamc[k] * lamc[k]) / (2.0 * mu);
                        c.add_grad(x, t, g);
                    } else {
                        f -= lamc[k] * lamc[k] / (2.0 * mu);
                    }
                }
                f
            },
            &x,
            &p.lo,
            &p.hi,
            o.inner,
            o.tol,
        );
        x = xn;
        let mut viol: f64 = 0.0;
        for (k, c) in p.cons.iter().enumerate() {
            let v = c.value(&x);
            lam[k] = (lam[k] + mu * v).max(0.0);
            viol = viol.max(v);
        }
        let h = dot(&p.den, &x) - 1.0;
        nu += mu * h;
        viol = viol.max(h.abs());
        if viol < o.tol {
            break;
        }
        mu = (mu * o.mu_growth).min(1e9);
    }
    let mut sol = Solution {
        value: p.ratio(&x),
        max_violation: p.max_violation(&x),
        x,
        active: vec![],
        at_lower: vec![],
        kkt_residual: f64::NAN,
        polished: false,
    };
    // rough active set
    sol.active = p
        .cons
        .iter()
        .enumerate()
        .filter(|(_, c)| c.value(&sol.x) > -o.active_tol)
        .map(|(k, _)| (k, lam[k]))
        .collect();
    if o.polish {
        if let Some(s2) = kkt_polish(p, &sol, o) {
            if s2.max_violation < 1e-9 && s2.kkt_residual < 1e-8 {
                sol = s2;
            }
        }
    }
    sol
}

/// Newton / Gauss-Newton on the KKT system restricted to the active set of `s`.
/// Variables: x, lambda_A (active constraints), beta_B (lower bounds), nu.
/// Equations: N + sum lambda grad g - sum beta e_i + nu D = 0; g_A(x) = 0; x_B = lo_B; D.x = 1.
pub fn kkt_polish(p: &RatioProblem, s: &Solution, o: &Opts) -> Option<Solution> {
    let n = p.nvar();
    let act: Vec<usize> = s.active.iter().map(|a| a.0).collect();
    let bnd: Vec<usize> = (0..n).filter(|&i| s.x[i] - p.lo[i] < o.active_tol).collect();
    let na = act.len();
    let nb = bnd.len();
    let nv = n + na + nb + 1;
    let mut z = DVector::zeros(nv);
    for i in 0..n {
        z[i] = s.x[i];
    }
    for (a, k) in act.iter().enumerate() {
        z[n + a] = s.active.iter().find(|t| t.0 == *k).map(|t| t.1).unwrap_or(0.0);
    }
    z[nv - 1] = -s.value;
    let resid = |z: &DVector<f64>| -> DVector<f64> {
        let x: Vec<f64> = (0..n).map(|i| z[i]).collect();
        let neq = n + na + nb + 1;
        let mut r = DVector::zeros(neq);
        let mut g = p.num.clone();
        for (a, &k) in act.iter().enumerate() {
            p.cons[k].add_grad(&x, z[n + a], &mut g);
        }
        for (b, &i) in bnd.iter().enumerate() {
            g[i] -= z[n + na + b];
        }
        for i in 0..n {
            r[i] = g[i] + z[nv - 1] * p.den[i];
        }
        for (a, &k) in act.iter().enumerate() {
            r[n + a] = p.cons[k].value(&x);
        }
        for (b, &i) in bnd.iter().enumerate() {
            r[n + na + b] = x[i] - p.lo[i];
        }
        r[n + na + nb] = dot(&p.den, &x) - 1.0;
        r
    };
    let mut r = resid(&z);
    for _ in 0..60 {
        if r.norm() < 1e-15 {
            break;
        }
        // numerical Jacobian (small systems)
        let h = 1e-7;
        let mut j = DMatrix::zeros(r.len(), nv);
        for c in 0..nv {
            let mut zp = z.clone();
            zp[c] += h;
            let mut zm = z.clone();
            zm[c] -= h;
            let col = (resid(&zp) - resid(&zm)) / (2.0 * h);
            j.set_column(c, &col);
        }
        let svd = j.svd(true, true);
        let dz = svd.solve(&(-&r), 1e-12).ok()?;
        let mut t = 1.0;
        let mut improved = false;
        for _ in 0..30 {
            let zn = &z + &dz * t;
            let rn = resid(&zn);
            if rn.norm() < r.norm() {
                z = zn;
                r = rn;
                improved = true;
                break;
            }
            t *= 0.5;
        }
        if !improved {
            break;
        }
    }
    let x: Vec<f64> = (0..n).map(|i| z[i]).collect();
    let active: Vec<(usize, f64)> = act.iter().enumerate().map(|(a, &k)| (k, z[n + a])).collect();
    let at_lower: Vec<(usize, f64)> = bnd.iter().enumerate().map(|(b, &i)| (i, z[n + na + b])).collect();
    // dual feasibility: multipliers must be >= 0
    let dual_ok = active.iter().all(|a| a.1 > -1e-7) && at_lower.iter().all(|b| b.1 > -1e-7);
    Some(Solution {
        value: p.ratio(&x),
        max_violation: p.max_violation(&x),
        x,
        active,
        at_lower,
        kkt_residual: if dual_ok { r.norm() } else { f64::INFINITY },
        polished: true,
    })
}

/// Parallel multistart from given starting points; results sorted by value (feasible first).
pub fn multistart(p: &RatioProblem, starts: &[Vec<f64>], o: &Opts) -> Vec<Solution> {
    let mut sols: Vec<Solution> = starts.par_iter().map(|x0| solve_from(p, x0, o)).collect();
    sols.sort_by(|a, b| {
        let fa = a.max_violation < 1e-7;
        let fb = b.max_violation < 1e-7;
        fb.cmp(&fa).then(a.value.partial_cmp(&b.value).unwrap_or(std::cmp::Ordering::Equal))
    });
    sols
}

/// Random starting distance vectors from random Euclidean point sets in dimension 1..=maxdim,
/// and random tree-like (l1 of random cuts) metrics.
pub fn random_metric_starts(npts: usize, count: usize, seed: u64) -> Vec<Vec<f64>> {
    let mut rng = SmallRng::seed_from_u64(seed);
    (0..count)
        .map(|t| {
            if t % 3 == 2 {
                // random l1 combination of cuts
                let mut m = crate::metric::Metric::zeros(npts);
                for _ in 0..6 {
                    let mask = rng.gen_range(1..(1u64 << (npts - 1)));
                    let w: f64 = rng.gen::<f64>();
                    let c = crate::metric::Metric::cut(npts, mask);
                    for (a, b) in m.d.iter_mut().zip(&c.d) {
                        *a += w * b;
                    }
                }
                m.d
            } else {
                let dim = rng.gen_range(1..=4);
                let pts: Vec<Vec<f64>> =
                    (0..npts).map(|_| (0..dim).map(|_| rng.gen::<f64>() * 2.0 - 1.0).collect()).collect();
                crate::metric::Metric::euclidean(&pts).d
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metric::*;
    #[test]
    fn simple_lp_like() {
        // minimise d01 / (d02) over triangle-inequality metrics on 3 points: min is 0 (d01=0,d02=d12).
        let n = 3;
        let num = weights(n, &[(0, 1, 1.0), (1, 2, 1.0)]);
        let den = weights(n, &[(0, 2, 1.0)]);
        let p = RatioProblem::new(num, den, triangle_family(n));
        let starts = random_metric_starts(n, 8, 1);
        let s = multistart(&p, &starts, &Opts::default());
        assert!((s[0].value - 1.0).abs() < 1e-7, "{:?}", s[0]);
    }
}
