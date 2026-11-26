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
        reg = (reg * o.reg_decay).max(o.reg_min);
        if res < o.tol {
            break;
        }
    }
    let max_map_norm = maps.iter().map(|m| m.norm()).fold(0.0, f64::max);
    AlsResult { rel_residual: res, maps, history: hist, max_map_norm, start }
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
