//! Search for restrictions T <= S, S a wire network (EPR graph tensor), T a dense target, by
//! alternating least squares over R or C with parallel multistart; flattening-rank precheck; a
//! border diagnostic (residual vs. map norms under vanishing regularisation).
//!
//! Party p gets a map A_p : C^{in_p} -> C^{out_p}, in_p = product of p's supply legs (wire order,
//! mixed radix, first leg most significant, as in `Network::dense`).

use crate::tensor::{random_matrix, Network, Scalar, Tensor};
use nalgebra::DMatrix;
use rand::rngs::SmallRng;
use rand::SeedableRng;
use rayon::prelude::*;
use num_complex::Complex64;

const OUT: usize = 1 << 20; // label offset for output legs

/// Greedy pairwise contraction of a list of tensors (smallest intermediate first).
pub fn contract_all<T: Scalar>(mut ts: Vec<Tensor<T>>) -> Tensor<T> {
    while ts.len() > 1 {
        let mut best = (usize::MAX, 0, 1);
        for i in 0..ts.len() {
            for j in i + 1..ts.len() {
                let shared: Vec<usize> = ts[i].labels.iter().cloned().filter(|l| ts[j].labels.contains(l)).collect();
                let mut sz = 1usize;
                for (k, &l) in ts[i].labels.iter().enumerate() {
                    if !shared.contains(&l) {
                        sz = sz.saturating_mul(ts[i].shape[k]);
                    }
                }
                for (k, &l) in ts[j].labels.iter().enumerate() {
                    if !shared.contains(&l) {
                        sz = sz.saturating_mul(ts[j].shape[k]);
                    }
                }
                // prefer pairs that share bonds
                let key = if shared.is_empty() { sz.saturating_mul(1 << 8) } else { sz };
                if key < best.0 {
                    best = (key, i, j);
                }
            }
        }
        let (_, i, j) = best;
        let b = ts.remove(j);
        let a = ts.remove(i);
        ts.push(a.contract(&b));
    }
    ts.pop().unwrap()
}

/// Node tensor of party p for map A (out_p x in_p): axes [OUT+p, bond labels...].
pub fn node<T: Scalar>(net: &Network, p: usize, a: &DMatrix<T>) -> Tensor<T> {
    let legs = net.legs(p);
    let mut shape = vec![a.nrows()];
    shape.extend(legs.iter().map(|l| l.1));
    let mut labels = vec![OUT + p];
    labels.extend(legs.iter().map(|l| l.0));
    // row-major data of A
    Tensor::from_vec(shape, labels, a.transpose().as_slice().to_vec())
}

/// (tensor_p A_p) S as a dense tensor with labels = parties.
pub fn apply_maps<T: Scalar>(net: &Network, maps: &[DMatrix<T>]) -> Tensor<T> {
    let nodes: Vec<Tensor<T>> = (0..net.nparties).map(|p| node(net, p, &maps[p])).collect();
    let mut r = contract_all(nodes);
    for l in r.labels.iter_mut() {
        *l -= OUT;
    }
    let order: Vec<usize> = (0..net.nparties).collect();
    r.permute_to(&order)
}

/// Environment matrix of party p: rows in_p, columns = other parties' outputs (party order).
pub fn environment<T: Scalar>(net: &Network, maps: &[DMatrix<T>], p: usize) -> DMatrix<T> {
    let nodes: Vec<Tensor<T>> = (0..net.nparties).filter(|&q| q != p).map(|q| node(net, q, &maps[q])).collect();
    let e = contract_all(nodes);
    let rows: Vec<usize> = net.legs(p).iter().map(|l| l.0).collect();
    let mut order = rows.clone();
    order.extend((0..net.nparties).filter(|&q| q != p).map(|q| OUT + q));
    let ep = e.permute_to(&order);
    let (m, _) = ep.matricize(&rows);
    m
}

#[derive(Clone, Debug)]
pub struct AlsOpts {
    pub sweeps: usize,
    pub starts: usize,
    pub complex: bool,
    pub seed: u64,
    /// initial Tikhonov regularisation (relative to trace(G)/n); decays by `reg_decay` per sweep.
    pub reg0: f64,
    pub reg_decay: f64,
    pub reg_min: f64,
    pub tol: f64,
}
impl Default for AlsOpts {
    fn default() -> Self {
        AlsOpts { sweeps: 500, starts: 16, complex: false, seed: 1, reg0: 1e-3, reg_decay: 0.9, reg_min: 1e-15, tol: 1e-14 }
    }
}

#[derive(Clone, Debug)]
pub struct AlsResult<T: Scalar> {
    pub rel_residual: f64,
    pub maps: Vec<DMatrix<T>>,
    pub history: Vec<f64>,
    /// max Frobenius norm of the maps after each sweep (border diagnostic: residual -> 0 while
    /// norms -> infinity suggests a degeneration, not a restriction)
    pub norm_history: Vec<f64>,
    pub max_map_norm: f64,
    pub start: usize,
}

/// One ALS run from random maps.
pub fn als_run<T: Scalar>(net: &Network, target: &Tensor<T>, o: &AlsOpts, start: usize) -> AlsResult<T> {
    let mut rng = SmallRng::seed_from_u64(o.seed.wrapping_mul(1000003).wrapping_add(start as u64));
    let np = net.nparties;
    let outd: Vec<usize> = target.shape.clone();
    let mut maps: Vec<DMatrix<T>> =
        (0..np).map(|p| random_matrix::<T, _>(outd[p], net.local_dim(p), &mut rng, o.complex)).collect();
    let tn = target.norm2().sqrt();
    let tmats: Vec<DMatrix<T>> = (0..np).map(|p| target.matricize(&[p]).0).collect();
    let mut hist = vec![];
    let mut nhist = vec![];
    let mut reg = o.reg0;
    let mut res = f64::INFINITY;
    for _sweep in 0..o.sweeps {
        for p in 0..np {
            let e = environment(net, &maps, p);
            let eh = e.adjoint();
            let mut g = &e * &eh;
            let tr: f64 = (0..g.nrows()).map(|i| g[(i, i)].real()).sum::<f64>() / g.nrows() as f64;
            for i in 0..g.nrows() {
                g[(i, i)] += T::sc(reg * tr + 1e-300);
            }
            let c = &tmats[p] * &eh;
            // A = C G^{-1}  <=>  G^T A^T = C^T ; G Hermitian so solve G^H X = C^H, A = X^H
            let chol = g.clone().cholesky();
            let a = match chol {
                Some(ch) => ch.solve(&c.adjoint()).adjoint(),
                None => match g.clone().lu().solve(&c.adjoint()) {
                    Some(x) => x.adjoint(),
                    None => continue,
                },
            };
            maps[p] = a;
            if p == np - 1 {
                let r = &maps[p] * &e - &tmats[p];
                res = r.iter().map(|x| x.abs2()).sum::<f64>().sqrt() / tn;
            }
        }
        // balance norms across parties (gauge)
        let norms: Vec<f64> = maps.iter().map(|m| m.norm()).collect();
        let geo = norms.iter().map(|x| x.ln()).sum::<f64>() / np as f64;
        for (m, n) in maps.iter_mut().zip(&norms) {
            let s = (geo - n.ln()).exp();
            *m *= T::sc(s);
        }
        hist.push(res);
        nhist.push(maps.iter().map(|m| m.norm()).fold(0.0, f64::max));
        reg = (reg * o.reg_decay).max(o.reg_min);
        if res < o.tol {
            break;
        }
    }
    let max_map_norm = maps.iter().map(|m| m.norm()).fold(0.0, f64::max);
    AlsResult { rel_residual: res, maps, history: hist, norm_history: nhist, max_map_norm, start }
}

/// Parallel multistart ALS; results sorted by residual.
pub fn als_multistart<T: Scalar>(net: &Network, target: &Tensor<T>, o: &AlsOpts) -> Vec<AlsResult<T>> {
    let mut r: Vec<AlsResult<T>> = (0..o.starts).into_par_iter().map(|s| als_run(net, target, o, s)).collect();
    r.sort_by(|a, b| a.rel_residual.partial_cmp(&b.rel_residual).unwrap());
    r
}

/// Independent residual check: dense S, explicit Kronecker-free application of each map.
pub fn residual_dense<T: Scalar>(net: &Network, maps: &[DMatrix<T>], target: &Tensor<T>) -> f64 {
    let mut s: Tensor<T> = net.dense();
    for p in 0..net.nparties {
        s = s.apply(p, &maps[p]);
    }
    (s.sub_norm2(target) / target.norm2()).sqrt()
}

/// Flattening-rank necessary condition: for every cut, log rank(T) <= log rank(S).
/// Returns violated cuts (mask, log2 rank S, log2 rank T) where T is a wire network too.
pub fn cut_check(supply: &Network, demand: &Network) -> Vec<(u64, f64, f64)> {
    let n = supply.nparties;
    let mut bad = vec![];
    for m in 1..(1u64 << (n - 1)) {
        let s = supply.cut_log_rank(m);
        let t = demand.cut_log_rank(m);
        if t > s + 1e-12 {
            bad.push((m, s, t));
        }
    }
    bad
}

/// Single-cut and local-dimension report for every party subset: (mask, log2 rank S, log2 rank T).
pub fn cut_table(supply: &Network, demand: &Network) -> Vec<(u64, f64, f64)> {
    let n = supply.nparties;
    (1..(1u64 << (n - 1))).map(|m| (m, supply.cut_log_rank(m), demand.cut_log_rank(m))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn route_epr_through_middle() {
        // S: wires 0-1, 1-2 (dim 2). T: wire 0-2 (dim 2). Restriction exists (entanglement swapping).
        let s = Network::new(3, vec![(0, 1, 2), (1, 2, 2)]);
        let t: Tensor<f64> = Network::new(3, vec![(0, 2, 2)]).dense();
        let o = AlsOpts { sweeps: 300, starts: 4, ..Default::default() };
        let r = als_multistart(&s, &t, &o);
        assert!(r[0].rel_residual < 1e-8, "{}", r[0].rel_residual);
        assert!(residual_dense(&s, &r[0].maps, &t) < 1e-8);
    }
    #[test]
    fn impossible_triangle() {
        // S: single wire 0-1 cannot give wire 0-2.
        let s = Network::new(3, vec![(0, 1, 2), (1, 2, 1)]);
        let d = Network::new(3, vec![(0, 2, 2)]);
        assert!(!cut_check(&s, &d).is_empty());
    }
}

/// Global row-major index (party order) of the entry (o_p = o, others = column c of the
/// matricisation at p, others in party order).
fn global_index_table(shape: &[usize], p: usize) -> Vec<Vec<usize>> {
    let str_ = crate::tensor::strides(shape);
    let others: Vec<usize> = (0..shape.len()).filter(|&q| q != p).collect();
    let ncol: usize = others.iter().map(|&q| shape[q]).product();
    let mut colbase = vec![0usize; ncol];
    for (c, cb) in colbase.iter_mut().enumerate() {
        let mut rem = c;
        let mut off = 0;
        for &q in others.iter().rev() {
            off += (rem % shape[q]) * str_[q];
            rem /= shape[q];
        }
        *cb = off;
    }
    (0..shape[p]).map(|o| colbase.iter().map(|b| b + o * str_[p]).collect()).collect()
}

/// Levenberg-Marquardt refinement (real case) of ALS maps: minimises ||(x A_p) S - T||^2 over all
/// map entries jointly. Returns (refined maps, relative residual, iterations used).
pub fn lm_refine(net: &Network, target: &Tensor<f64>, maps0: &[DMatrix<f64>], iters: usize) -> (Vec<DMatrix<f64>>, f64, usize) {
    let np = net.nparties;
    let mut maps = maps0.to_vec();
    let tn = target.norm2().sqrt();
    let nres = target.data.len();
    let sizes: Vec<usize> = maps.iter().map(|m| m.len()).collect();
    let nvar: usize = sizes.iter().sum();
    let tables: Vec<Vec<Vec<usize>>> = (0..np).map(|p| global_index_table(&target.shape, p)).collect();
    let resid = |maps: &[DMatrix<f64>]| -> Vec<f64> {
        let x = apply_maps(net, maps);
        x.data.iter().zip(&target.data).map(|(a, b)| a - b).collect()
    };
    let mut r = resid(&maps);
    let mut f = r.iter().map(|x| x * x).sum::<f64>();
    let mut lambda = 1e-3;
    let mut used = 0;
    for it in 0..iters {
        used = it + 1;
        // Jacobian
        let mut j = DMatrix::<f64>::zeros(nres, nvar);
        let mut off = 0;
        for p in 0..np {
            let e = environment(net, &maps, p); // in_p x ncol
            let (outd, ind) = (maps[p].nrows(), maps[p].ncols());
            for o in 0..outd {
                for i in 0..ind {
                    let col = off + i * outd + o; // column-major index of A_p[(o,i)]
                    for (c, &g) in tables[p][o].iter().enumerate() {
                        j[(g, col)] = e[(i, c)];
                    }
                }
            }
            off += sizes[p];
        }
        let jt = j.transpose();
        let jtj = &jt * &j;
        let rv = nalgebra::DVector::from_vec(r.clone());
        let g = &jt * &rv;
        let mut improved = false;
        for _ in 0..20 {
            let mut a = jtj.clone();
            for k in 0..nvar {
                a[(k, k)] += lambda * (1.0 + jtj[(k, k)]);
            }
            let Some(ch) = a.cholesky() else { lambda *= 10.0; continue };
            let step = ch.solve(&g);
            let mut trial = maps.clone();
            let mut off = 0;
            for p in 0..np {
                let sl = trial[p].as_mut_slice();
                for k in 0..sizes[p] {
                    sl[k] -= step[off + k];
                }
                off += sizes[p];
            }
            let rt = resid(&trial);
            let ft = rt.iter().map(|x| x * x).sum::<f64>();
            if ft < f {
                maps = trial;
                r = rt;
                f = ft;
                lambda = (lambda * 0.3).max(1e-15);
                improved = true;
                break;
            }
            lambda *= 10.0;
        }
        if !improved || f.sqrt() / tn < 1e-15 {
            break;
        }
    }
    (maps, f.sqrt() / tn, used)
}

/// Result of the border (degeneration) search.
#[derive(Clone, Debug)]
pub struct BorderResult {
    /// sqrt(sum_{m<h} |C_m|^2 + |C_h - T|^2) / |T| where C_m = coefficient of eps^m in (x A(eps)) S.
    pub rel_residual: f64,
    /// maps[p][k] = coefficient of eps^k in A_p(eps)
    pub maps: Vec<Vec<DMatrix<f64>>>,
    pub history: Vec<f64>,
    pub max_coef_norm: f64,
}

/// Coefficients E^{(j)}, j = 0..=(P-1)K, of the environment polynomial of party p (real case),
/// via evaluation at N-th roots of unity and inverse DFT.
fn env_coeffs(net: &Network, maps: &[Vec<DMatrix<f64>>], p: usize, k: usize) -> Vec<DMatrix<f64>> {
    let np = net.nparties;
    let n = (np - 1) * k + 1;
    let mut acc: Vec<DMatrix<Complex64>> = vec![];
    for t in 0..n {
        let w = Complex64::from_polar(1.0, 2.0 * std::f64::consts::PI * t as f64 / n as f64);
        let mq: Vec<DMatrix<Complex64>> = (0..np)
            .map(|q| {
                let mut m = maps[q][0].map(|x| Complex64::new(x, 0.0));
                let mut wp = Complex64::new(1.0, 0.0);
                for kk in 1..=k {
                    wp *= w;
                    m += maps[q][kk].map(|x| Complex64::new(x, 0.0) * wp);
                }
                m
            })
            .collect();
        let e = environment(net, &mq, p);
        if acc.is_empty() {
            acc = (0..n).map(|_| DMatrix::zeros(e.nrows(), e.ncols())).collect();
        }
        for (j, a) in acc.iter_mut().enumerate() {
            let c = Complex64::from_polar(1.0 / n as f64, -2.0 * std::f64::consts::PI * (t * j) as f64 / n as f64);
            *a += &e * c;
        }
    }
    acc.into_iter().map(|m| m.map(|z| z.re)).collect()
}

/// Border ALS: maps A_p(eps) = sum_{k<=K} eps^k A_p^{(k)}; fit (x A(eps)) S = eps^h T + O(eps^{h+1}).
/// A zero residual gives an approximation of degree h, i.e. T is a degeneration of S.
pub fn border_als(net: &Network, target: &Tensor<f64>, k: usize, h: usize, o: &AlsOpts, start: usize) -> BorderResult {
    use crate::tensor::Scalar as _;
    let mut rng = SmallRng::seed_from_u64(o.seed.wrapping_mul(7777777).wrapping_add(start as u64));
    let np = net.nparties;
    let outd = target.shape.clone();
    let mut maps: Vec<Vec<DMatrix<f64>>> = (0..np)
        .map(|p| (0..=k).map(|_| random_matrix::<f64, _>(outd[p], net.local_dim(p), &mut rng, false)).collect())
        .collect();
    let tn = target.norm2().sqrt();
    let tmats: Vec<DMatrix<f64>> = (0..np).map(|p| target.matricize(&[p]).0).collect();
    let mut reg = o.reg0;
    let mut hist = vec![];
    let mut res = f64::INFINITY;
    let dmax = (np - 1) * k;
    for _ in 0..o.sweeps {
        for p in 0..np {
            let ec = env_coeffs(net, &maps, p, k);
            let ind = net.local_dim(p);
            let ncol = ec[0].ncols();
            // Ebig_m: ((k+1) ind) x ncol, block kk = E^{(m-kk)}
            let mut g = DMatrix::<f64>::zeros((k + 1) * ind, (k + 1) * ind);
            let mut ebigs = vec![];
            for m in 0..=h {
                let mut eb = DMatrix::<f64>::zeros((k + 1) * ind, ncol);
                for kk in 0..=k {
                    if m >= kk && m - kk <= dmax {
                        eb.view_mut((kk * ind, 0), (ind, ncol)).copy_from(&ec[m - kk]);
                    }
                }
                g += &eb * eb.transpose();
                ebigs.push(eb);
            }
            let tr = (0..g.nrows()).map(|i| g[(i, i)]).sum::<f64>() / g.nrows() as f64;
            for i in 0..g.nrows() {
                g[(i, i)] += reg * tr + 1e-300;
            }
            let c = &tmats[p] * ebigs[h].transpose();
            let x = match g.clone().cholesky() {
                Some(ch) => ch.solve(&c.transpose()).transpose(),
                None => continue,
            };
            for kk in 0..=k {
                maps[p][kk] = x.columns(kk * ind, ind).into_owned();
            }
            if p == np - 1 {
                let mut tot = 0.0;
                for (m, eb) in ebigs.iter().enumerate() {
                    let mut r = &x * eb;
                    if m == h {
                        r -= &tmats[p];
                    }
                    tot += r.iter().map(|v| v.abs2()).sum::<f64>();
                }
                res = tot.sqrt() / tn;
            }
        }
        // gauge: balance overall norms across parties
        let norms: Vec<f64> = maps.iter().map(|ms| ms.iter().map(|m| m.norm_squared()).sum::<f64>().sqrt()).collect();
        let geo = norms.iter().map(|x| x.ln()).sum::<f64>() / np as f64;
        for (ms, nn) in maps.iter_mut().zip(&norms) {
            let s = (geo - nn.ln()).exp();
            for m in ms.iter_mut() {
                *m *= s;
            }
        }
        hist.push(res);
        reg = (reg * o.reg_decay).max(o.reg_min);
        if res < o.tol {
            break;
        }
    }
    let max_coef_norm = maps.iter().flat_map(|ms| ms.iter().map(|m| m.norm())).fold(0.0, f64::max);
    BorderResult { rel_residual: res, maps, history: hist, max_coef_norm }
}

/// Independent check of a border solution: evaluate (x A(eps)) S / eps^h at small eps through the
/// dense S and return the relative distance to T for each eps given.
pub fn border_check(net: &Network, target: &Tensor<f64>, maps: &[Vec<DMatrix<f64>>], h: usize, eps: &[f64]) -> Vec<f64> {
    eps.iter()
        .map(|&e| {
            let m: Vec<DMatrix<f64>> = maps
                .iter()
                .map(|ms| {
                    let mut a = ms[0].clone();
                    for (kk, mk) in ms.iter().enumerate().skip(1) {
                        a += mk * e.powi(kk as i32);
                    }
                    a
                })
                .collect();
            let mut s: Tensor<f64> = net.dense();
            for p in 0..net.nparties {
                s = s.apply(p, &m[p]);
            }
            s.scale(1.0 / e.powi(h as i32));
            (s.sub_norm2(target) / target.norm2()).sqrt()
        })
        .collect()
}

/// Parallel multistart border ALS, sorted by residual.
pub fn border_multistart(net: &Network, target: &Tensor<f64>, k: usize, h: usize, o: &AlsOpts) -> Vec<BorderResult> {
    let mut r: Vec<BorderResult> = (0..o.starts).into_par_iter().map(|s| border_als(net, target, k, h, o, s)).collect();
    r.sort_by(|a, b| a.rel_residual.partial_cmp(&b.rel_residual).unwrap());
    r
}

#[cfg(test)]
mod border_tests {
    use super::*;
    #[test]
    fn border_reduces_to_restriction() {
        let s = Network::new(3, vec![(0, 1, 2), (1, 2, 2)]);
        let t: Tensor<f64> = Network::new(3, vec![(0, 2, 2)]).dense();
        let o = AlsOpts { sweeps: 400, starts: 4, ..Default::default() };
        let r = border_multistart(&s, &t, 1, 1, &o);
        assert!(r[0].rel_residual < 1e-8, "{}", r[0].rel_residual);
        let chk = border_check(&s, &t, &r[0].maps, 1, &[1e-4]);
        assert!(chk[0] < 1e-3, "{:?}", chk);
    }
}
