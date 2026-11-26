//! Spectrum of the normalised adjacency matrix A of a regular graph: Lanczos on the complement of
//! the constant vector (gives lambda_2 and lambda_n), with full reorthogonalisation when the Krylov
//! basis fits in memory, plain three-term recurrence otherwise (extreme Ritz values still converge;
//! spurious copies do not affect them).

use super::graph::Graph;
use nalgebra::DMatrix;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use rayon::prelude::*;

pub fn matvec(g: &Graph, x: &[f64], y: &mut [f64]) {
    let d = g.d;
    let inv = 1.0 / d as f64;
    y.par_chunks_mut(4096).enumerate().for_each(|(c, ys)| {
        for (i, yv) in ys.iter_mut().enumerate() {
            let v = c * 4096 + i;
            let mut s = 0.0;
            for &w in &g.adj[v * d..(v + 1) * d] {
                s += x[w as usize];
            }
            *yv = s * inv;
        }
    });
}

fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.par_iter().zip(b.par_iter()).map(|(x, y)| x * y).sum()
}

fn deflate(x: &mut [f64]) {
    let m = x.par_iter().sum::<f64>() / x.len() as f64;
    x.par_iter_mut().for_each(|v| *v -= m);
}

#[derive(Clone, Debug)]
pub struct Spectrum {
    pub lambda2: f64,
    pub lambda_min: f64,
    /// lambda_2 estimates after 1/4, 1/2, 3/4 and all of the steps (convergence monitor)
    pub history: Vec<f64>,
    pub steps: usize,
    /// approximate eigenvector for lambda_2 (only with reorthogonalisation)
    pub vec2: Option<Vec<f64>>,
}

fn tridiag_eigs(alpha: &[f64], beta: &[f64]) -> (Vec<f64>, DMatrix<f64>) {
    let k = alpha.len();
    let mut t = DMatrix::zeros(k, k);
    for i in 0..k {
        t[(i, i)] = alpha[i];
        if i + 1 < k {
            t[(i, i + 1)] = beta[i];
            t[(i + 1, i)] = beta[i];
        }
    }
    let e = t.symmetric_eigen();
    (e.eigenvalues.iter().cloned().collect(), e.eigenvectors)
}

/// Lanczos with `steps` iterations on 1^perp. `reortho`: keep the basis (memory steps * n * 8 bytes).
pub fn lanczos(g: &Graph, steps: usize, reortho: bool, seed: u64) -> Spectrum {
    let n = g.n;
    let steps = steps.min(n - 1);
    let mut rng = SmallRng::seed_from_u64(seed);
    let mut v: Vec<f64> = (0..n).map(|_| rng.gen::<f64>() - 0.5).collect();
    deflate(&mut v);
    let nv = dot(&v, &v).sqrt();
    v.par_iter_mut().for_each(|x| *x /= nv);
    let mut basis: Vec<Vec<f64>> = vec![];
    let mut vprev = vec![0.0; n];
    let mut w = vec![0.0; n];
    let (mut alpha, mut beta) = (vec![], vec![]);
    let mut history = vec![];
    let mut b_prev = 0.0;
    for it in 0..steps {
        matvec(g, &v, &mut w);
        let a = dot(&w, &v);
        w.par_iter_mut().zip(v.par_iter()).zip(vprev.par_iter()).for_each(|((wi, vi), pi)| *wi -= a * vi + b_prev * pi);
        deflate(&mut w);
        if reortho {
            basis.push(v.clone());
            for _ in 0..2 {
                for b in &basis {
                    let c = dot(&w, b);
                    w.par_iter_mut().zip(b.par_iter()).for_each(|(wi, bi)| *wi -= c * bi);
                }
            }
        }
        alpha.push(a);
        let b = dot(&w, &w).sqrt();
        if [steps / 4, steps / 2, 3 * steps / 4].contains(&(it + 1)) {
            let (e, _) = tridiag_eigs(&alpha, &beta);
            history.push(e.iter().cloned().fold(f64::MIN, f64::max));
        }
        if b < 1e-12 || it + 1 == steps {
            break;
        }
        beta.push(b);
        std::mem::swap(&mut vprev, &mut v);
        v.par_iter_mut().zip(w.par_iter()).for_each(|(vi, wi)| *vi = wi / b);
        b_prev = b;
    }
    let (e, vecs) = tridiag_eigs(&alpha, &beta[..alpha.len() - 1]);
    let (imax, &l2) = e.iter().enumerate().max_by(|a, b| a.1.partial_cmp(b.1).unwrap()).unwrap();
    let lmin = e.iter().cloned().fold(f64::MAX, f64::min);
    history.push(l2);
    let vec2 = if reortho {
        let mut x = vec![0.0; n];
        for (j, b) in basis.iter().enumerate() {
            let c = vecs[(j, imax)];
            x.iter_mut().zip(b.iter()).for_each(|(xi, bi)| *xi += c * bi);
        }
        Some(x)
    } else {
        None
    };
    Spectrum { lambda2: l2, lambda_min: lmin, history, steps: alpha.len(), vec2 }
}

/// lambda_2 / lambda_min with a sensible default number of steps.
pub fn spectrum(g: &Graph) -> Spectrum {
    if g.n <= 2000 {
        // dense exact
        let n = g.n;
        let mut a = DMatrix::zeros(n, n);
        for v in 0..n {
            for &w in g.nb(v) {
                a[(v, w as usize)] += 1.0 / g.d as f64;
            }
        }
        let e = a.clone().symmetric_eigen();
        let mut idx: Vec<usize> = (0..n).collect();
        idx.sort_by(|&i, &j| e.eigenvalues[j].partial_cmp(&e.eigenvalues[i]).unwrap());
        let l2 = e.eigenvalues[idx[1]];
        let vec2: Vec<f64> = (0..n).map(|i| e.eigenvectors[(i, idx[1])]).collect();
        return Spectrum { lambda2: l2, lambda_min: e.eigenvalues[idx[n - 1]], history: vec![l2], steps: n, vec2: Some(vec2) };
    }
    let reortho = g.n * 300 * 8 < 4_000_000_000;
    lanczos(g, 300, reortho, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rankplace::graph::*;
    #[test]
    fn cycle_spectrum() {
        let g = cycle(3000);
        let s = lanczos(&g, 600, true, 3);
        let exact = (2.0 * std::f64::consts::PI / 3000.0).cos();
        assert!((s.lambda2 - exact).abs() < 1e-5, "{} {}", s.lambda2, exact);
        assert!((s.lambda_min + 1.0).abs() < 1e-6);
        let g = random_regular(1500, 4, 3);
        let d = spectrum(&g);
        let l = lanczos(&g, 300, true, 3);
        assert!((d.lambda2 - l.lambda2).abs() < 1e-8);
        let l = lanczos(&g, 300, false, 3);
        assert!((d.lambda2 - l.lambda2).abs() < 1e-6);
    }
}
