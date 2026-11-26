//! PyO3 bindings: module `tensorlab`. Distances are flat lists in pair order (0,1),(0,2),...
use crate::metric::{self, Constraint, Metric};
use crate::{k23, models, opt, restrict, tensor};
use num_complex::Complex64;
use pyo3::prelude::*;
use pyo3::types::PyDict;

fn family(n: usize, names: &[String]) -> PyResult<Vec<Constraint>> {
    let mut v = vec![];
    for f in names {
        match f.as_str() {
            "triangle" => v.extend(metric::triangle_family(n)),
            "euler" => v.extend(metric::euler_family(n)),
            "reshetnyak" => v.extend(metric::reshetnyak_family(n)),
            "box" => v.extend(metric::box_family(n)),
            _ => return Err(pyo3::exceptions::PyValueError::new_err(format!("unknown family {f}"))),
        }
    }
    Ok(v)
}

#[pyfunction]
fn pairs(n: usize) -> Vec<(usize, usize)> {
    metric::pairs(n)
}

#[pyfunction]
fn pair_index(n: usize, i: usize, j: usize) -> usize {
    metric::pair_index(n, i, j)
}

/// Report on a metric: max violations of each family (<= 0 means satisfied), l1 / Euclidean tests.
#[pyfunction]
fn metric_report<'py>(py: Python<'py>, n: usize, d: Vec<f64>) -> PyResult<Bound<'py, PyDict>> {
    let m = Metric::new(n, d);
    let r = PyDict::new_bound(py);
    r.set_item("triangle", m.max_triangle_violation())?;
    if n >= 4 {
        r.set_item("euler", m.max_violation(&metric::euler_family(n)).0)?;
        r.set_item("reshetnyak", m.max_violation(&metric::reshetnyak_family(n)).0)?;
        r.set_item("box", m.max_violation(&metric::box_family_all_orders(n)).0)?;
    }
    r.set_item("gram_min_eig", m.euclidean_gram_min_eig())?;
    if n <= 10 {
        let (res, coef) = m.l1_nnls();
        r.set_item("l1_residual", res)?;
        r.set_item("l1_cuts", coef)?;
    }
    if n <= 9 {
        let (v, b) = m.max_hypermetric_violation(n.min(7));
        r.set_item("hypermetric", v)?;
        r.set_item("hypermetric_b", b)?;
    }
    Ok(r)
}

/// Exact minimum over [0,1]^2 of the box quadratic for squared distances [xy,yz,zw,wx,xz,yw].
#[pyfunction]
fn box_min(q: [f64; 6]) -> (f64, f64, f64) {
    metric::box_min(&q)
}

/// sqrt(rank(a-b)) on Mat_mu(F_2) (2^(mu^2) points; index = row-major bit pattern).
#[pyfunction]
fn sqrt_rank_f2(mu: usize) -> Vec<f64> {
    Metric::sqrt_rank_f2(mu).d
}

#[pyfunction]
fn k23_w5(l: f64, h: f64) -> Vec<f64> {
    k23::w5(l, h).d
}

#[pyfunction]
fn k23_weights() -> (Vec<f64>, Vec<f64>) {
    (k23::num(), k23::den())
}

/// Multistart minimisation of num.d / den.d over n-point metrics satisfying the families
/// (any of "triangle","euler","reshetnyak","box"). Returns the `keep` best solutions as dicts.
#[pyfunction]
#[pyo3(signature = (n, num, den, families, starts=200, seed=1, keep=5))]
fn min_ratio<'py>(py: Python<'py>, n: usize, num: Vec<f64>, den: Vec<f64>, families: Vec<String>, starts: usize,
    seed: u64, keep: usize) -> PyResult<Vec<Bound<'py, PyDict>>> {
    let cons = family(n, &families)?;
    let p = opt::RatioProblem::new(num, den, cons.clone());
    let st = opt::random_metric_starts(n, starts, seed);
    let sols = py.allow_threads(|| opt::multistart(&p, &st, &opt::Opts::default()));
    let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let mut out = vec![];
    for s in sols.iter().take(keep) {
        let r = PyDict::new_bound(py);
        r.set_item("value", s.value)?;
        r.set_item("d", s.x.clone())?;
        r.set_item("max_violation", s.max_violation)?;
        r.set_item("kkt_residual", s.kkt_residual)?;
        r.set_item("polished", s.polished)?;
        let act: Vec<(String, f64)> = s.active.iter().map(|(k, l)| (cons[*k].describe(n, &names), *l)).collect();
        r.set_item("active", act)?;
        r.set_item("at_lower", s.at_lower.clone())?;
        out.push(r);
    }
    Ok(out)
}

/// Minimise the ratio over n points in a product of k metric trees; returns [(value, d, label)].
#[pyfunction]
#[pyo3(signature = (n, k, num, den, starts=20, iters=4000, seed=7, keep=5))]
fn min_ratio_tree_products(py: Python<'_>, n: usize, k: usize, num: Vec<f64>, den: Vec<f64>, starts: usize, iters: usize,
    seed: u64, keep: usize) -> Vec<(f64, Vec<f64>, String)> {
    let r = py.allow_threads(|| models::min_ratio_tree_products(n, k, &num, &den, starts, iters, seed));
    r.into_iter().take(keep).map(|m| (m.value, m.metric.d, m.label)).collect()
}

/// log2 flattening ranks of supply and demand networks across every cut: [(mask, logS, logT)].
#[pyfunction]
fn cut_table(nparties: usize, supply: Vec<(usize, usize, usize)>, demand: Vec<(usize, usize, usize)>) -> Vec<(u64, f64, f64)> {
    restrict::cut_table(&tensor::Network::new(nparties, supply), &tensor::Network::new(nparties, demand))
}

/// ALS search for a restriction demand <= supply (wire networks). Returns a dict with the best
/// relative residual, an independent dense recheck, max map norm, residual history, all start
/// residuals, and the maps (real: nested lists; complex: [re, im] nested lists).
#[pyfunction]
#[pyo3(signature = (nparties, supply, demand, starts=16, sweeps=500, complex=false, seed=1, reg0=1e-3))]
fn als<'py>(py: Python<'py>, nparties: usize, supply: Vec<(usize, usize, usize)>, demand: Vec<(usize, usize, usize)>,
    starts: usize, sweeps: usize, complex: bool, seed: u64, reg0: f64) -> PyResult<Bound<'py, PyDict>> {
    let s = tensor::Network::new(nparties, supply);
    let d = tensor::Network::new(nparties, demand);
    let o = restrict::AlsOpts { sweeps, starts, complex, seed, reg0, ..Default::default() };
    let r = PyDict::new_bound(py);
    r.set_item("violated_cuts", restrict::cut_check(&s, &d))?;
    if complex {
        let t: tensor::Tensor<Complex64> = d.dense();
        let res = py.allow_threads(|| restrict::als_multistart(&s, &t, &o));
        let b = &res[0];
        r.set_item("residual", b.rel_residual)?;
        r.set_item("dense_residual", restrict::residual_dense(&s, &b.maps, &t))?;
        r.set_item("max_map_norm", b.max_map_norm)?;
        r.set_item("history", b.history.clone())?;
        r.set_item("all_residuals", res.iter().map(|x| x.rel_residual).collect::<Vec<_>>())?;
        let maps: Vec<Vec<Vec<[f64; 2]>>> = b.maps.iter().map(|m| (0..m.nrows()).map(|i| (0..m.ncols()).map(|j| [m[(i, j)].re, m[(i, j)].im]).collect()).collect()).collect();
        r.set_item("maps", maps)?;
    } else {
        let t: tensor::Tensor<f64> = d.dense();
        let res = py.allow_threads(|| restrict::als_multistart(&s, &t, &o));
        let b = &res[0];
        r.set_item("residual", b.rel_residual)?;
        r.set_item("dense_residual", restrict::residual_dense(&s, &b.maps, &t))?;
        r.set_item("max_map_norm", b.max_map_norm)?;
        r.set_item("history", b.history.clone())?;
        r.set_item("all_residuals", res.iter().map(|x| x.rel_residual).collect::<Vec<_>>())?;
        let maps: Vec<Vec<Vec<f64>>> = b.maps.iter().map(|m| (0..m.nrows()).map(|i| (0..m.ncols()).map(|j| m[(i, j)]).collect()).collect()).collect();
        r.set_item("maps", maps)?;
    }
    Ok(r)
}

/// Dense graph-state tensor of a wire network (real), returned as (shape, flat row-major data).
#[pyfunction]
fn network_dense(nparties: usize, wires: Vec<(usize, usize, usize)>) -> (Vec<usize>, Vec<f64>) {
    let t: tensor::Tensor<f64> = tensor::Network::new(nparties, wires).dense();
    (t.shape, t.data)
}

#[pymodule]
fn tensorlab(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(pairs, m)?)?;
    m.add_function(wrap_pyfunction!(pair_index, m)?)?;
    m.add_function(wrap_pyfunction!(metric_report, m)?)?;
    m.add_function(wrap_pyfunction!(box_min, m)?)?;
    m.add_function(wrap_pyfunction!(sqrt_rank_f2, m)?)?;
    m.add_function(wrap_pyfunction!(k23_w5, m)?)?;
    m.add_function(wrap_pyfunction!(k23_weights, m)?)?;
    m.add_function(wrap_pyfunction!(min_ratio, m)?)?;
    m.add_function(wrap_pyfunction!(min_ratio_tree_products, m)?)?;
    m.add_function(wrap_pyfunction!(cut_table, m)?)?;
    m.add_function(wrap_pyfunction!(als, m)?)?;
    m.add_function(wrap_pyfunction!(network_dense, m)?)?;
    Ok(())
}
