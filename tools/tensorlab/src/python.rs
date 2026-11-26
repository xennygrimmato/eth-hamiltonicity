//! PyO3 bindings: module `tensorlab`. Distances are flat lists in pair order (0,1),(0,2),...
use crate::metric::{self, Constraint, Metric};
use crate::{k23, models, opt, rankplace, restrict, tensor};
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

// ---------------- rankplace ----------------
// Graphs are passed as (n, d, adj) with adj the flat neighbour list (length n*d, each edge twice).
// Placements are lists of u64 (byte-row bit-packed mu x mu matrices over F_2, mu <= 8).

fn rp_graph(n: usize, d: usize, adj: Vec<u32>) -> PyResult<rankplace::graph::Graph> {
    if adj.len() != n * d {
        return Err(pyo3::exceptions::PyValueError::new_err("adj must have length n*d"));
    }
    Ok(rankplace::graph::Graph { n, d, adj, name: "py".into() })
}

/// Rank over F_2 of a bit-packed matrix (row i = byte i, column j = bit j).
#[pyfunction]
fn rp_rank(x: u64) -> u32 {
    rankplace::f2::rank(x)
}

/// Random d-regular simple connected graph -> (n, d, adj).
#[pyfunction]
fn rp_random_regular(n: usize, d: usize, seed: u64) -> (usize, usize, Vec<u32>) {
    let g = rankplace::graph::random_regular(n, d, seed);
    (g.n, g.d, g.adj)
}

/// Cayley graph of SL_m(F_2[x]/(p)) with generators e_ab(1), e_ab(x) -> (n, d, adj, mu, f) where f is the
/// conjugated-projection placement (j = k/2) if m*k <= 8, else empty.
#[pyfunction]
fn rp_sl_cayley(m: usize, k: usize, modulus: u32) -> (usize, usize, Vec<u32>, usize, Vec<u64>) {
    let gr = rankplace::groups::sl_elementary(m, k, modulus);
    let (mu, f) = if m * k <= 8 { gr.conj_projection_placement((k / 2).max(1)) } else { (0, vec![]) };
    (gr.graph.n, gr.graph.d, gr.graph.adj, mu, f)
}

/// LPS graph X^{p,q} -> (n, d, adj).
#[pyfunction]
fn rp_lps(p: u64, q: u64) -> (usize, usize, Vec<u32>) {
    let g = rankplace::groups::lps(p, q).graph;
    (g.n, g.d, g.adj)
}

/// (lambda_2, lambda_min) of the normalised adjacency matrix.
#[pyfunction]
fn rp_spectrum(n: usize, d: usize, adj: Vec<u32>) -> PyResult<(f64, f64)> {
    let s = rankplace::spectral::spectrum(&rp_graph(n, d, adj)?);
    Ok((s.lambda2, s.lambda_min))
}

/// beta_cut: (ratio, side, exact) (exact for n <= 24).
#[pyfunction]
fn rp_beta_cut(n: usize, d: usize, adj: Vec<u32>) -> PyResult<(f64, Vec<bool>, bool)> {
    let g = rp_graph(n, d, adj)?;
    let s = rankplace::spectral::spectrum(&g);
    let c = rankplace::cut::beta_cut(&g, s.vec2.as_deref());
    Ok((c.ratio, c.side, c.exact))
}

/// (ratio, E_pairs, E_edges) of a placement.
#[pyfunction]
fn rp_evaluate(n: usize, d: usize, adj: Vec<u32>, f: Vec<u64>) -> PyResult<(f64, f64, f64)> {
    Ok(rankplace::anneal::evaluate(&rp_graph(n, d, adj)?, &f))
}

/// Parallel annealing. objective: "ratio" | "lagrange" (uses gamma) | "pairs" (use with max_edge_rank).
/// f0: optional start placement (otherwise random rank-one starts). Returns [(value, ratio, E_pairs, E_edges, f)], best first.
#[pyfunction]
#[pyo3(signature = (n, d, adj, mu, objective="ratio", gamma=1.0, max_edge_rank=None, iters=200000, chains=4, seed=1, f0=None))]
#[allow(clippy::too_many_arguments)]
fn rp_anneal(py: Python<'_>, n: usize, d: usize, adj: Vec<u32>, mu: usize, objective: &str, gamma: f64, max_edge_rank: Option<u32>,
    iters: u64, chains: usize, seed: u64, f0: Option<Vec<u64>>) -> PyResult<Vec<(f64, f64, f64, f64, Vec<u64>)>> {
    use rankplace::anneal::{run_chains, Init, Objective, Opts};
    let g = rp_graph(n, d, adj)?;
    let obj = match objective {
        "ratio" => Objective::Ratio,
        "lagrange" => Objective::Lagrange(gamma),
        "pairs" => Objective::Pairs,
        _ => return Err(pyo3::exceptions::PyValueError::new_err("objective: ratio | lagrange | pairs")),
    };
    let init = match f0 {
        Some(f) => Init::Given(f),
        None if max_edge_rank.is_some() => Init::Given(vec![0; n]),
        None => Init::Random { rank: 1 },
    };
    let opts = Opts { iters, seed, max_edge_rank, ..Default::default() };
    let res = py.allow_threads(|| run_chains(&g, mu, obj, &opts, &[init], chains));
    Ok(res.into_iter().map(|r| (r.value, r.ratio, r.epairs, r.eedges, r.f)).collect())
}

/// Kernel inequality and consequences (a)-(c) for a placement, given lambda_2 and lambda_min.
#[pyfunction]
fn rp_verify<'py>(py: Python<'py>, n: usize, d: usize, adj: Vec<u32>, f: Vec<u64>, lambda2: f64, lambda_min: f64) -> PyResult<Bound<'py, PyDict>> {
    let r = rankplace::verify::verify(&rp_graph(n, d, adj)?, &f, lambda2, lambda_min);
    let out = PyDict::new_bound(py);
    out.set_item("ratio", r.ratio)?;
    out.set_item("epairs", r.epairs)?;
    out.set_item("eedges", r.eedges)?;
    out.set_item("max_edge", r.max_edge)?;
    out.set_item("hist_pairs", r.hist_pairs)?;
    out.set_item("hist_edges", r.hist_edges)?;
    out.set_item("kernel", r.kernel)?;
    out.set_item("kernel_ok", r.kernel_ok)?;
    out.set_item("lambda2_lower", r.lambda2_lower)?;
    out.set_item("cons_a", r.cons_a)?;
    out.set_item("cons_b", r.cons_b)?;
    out.set_item("cons_c", r.cons_c)?;
    out.set_item("cut_cone_ratio", r.cut_cone_ratio)?;
    Ok(out)
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
    m.add_function(wrap_pyfunction!(rp_rank, m)?)?;
    m.add_function(wrap_pyfunction!(rp_random_regular, m)?)?;
    m.add_function(wrap_pyfunction!(rp_sl_cayley, m)?)?;
    m.add_function(wrap_pyfunction!(rp_lps, m)?)?;
    m.add_function(wrap_pyfunction!(rp_spectrum, m)?)?;
    m.add_function(wrap_pyfunction!(rp_beta_cut, m)?)?;
    m.add_function(wrap_pyfunction!(rp_evaluate, m)?)?;
    m.add_function(wrap_pyfunction!(rp_anneal, m)?)?;
    m.add_function(wrap_pyfunction!(rp_verify, m)?)?;
    Ok(())
}
