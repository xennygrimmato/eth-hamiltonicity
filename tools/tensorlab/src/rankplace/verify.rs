//! Verification of found placements against the theorems of notes §4:
//! Proposition S (kernel inequality) E_edges 2^{-kD} <= lam + (1-lam) E_pairs 2^{-kD}, lam = max(lambda_2, 0),
//! for k = 1, 2, 3 (a violation is a bug, or an unconverged lambda_2); consequence (a) (gradient r and
//! lambda* <= 2^{-r-1} => E_pairs <= 6r+4), (b) (E_edges <= (1-lambda_2)/4 => E_pairs <= (4/3) E_edges/(1-lambda_2)),
//! (c) (mean edge rank e < log2(1/lambda_2) => E_pairs <= 2e/(c(1-lambda_2)) + 2 ceil(log2(1/c))), and the
//! spectral bound (e): lambda_2 >= (E_edges 2^{-D} - E_pairs 2^{-D}) / (1 - E_pairs 2^{-D}).

use super::f2;
use super::graph::Graph;
use rayon::prelude::*;

/// Histograms over ordered pairs (n^2 entries, diagonal included) and over the n*d edge slots.
pub fn histograms(g: &Graph, f: &[u64]) -> ([u64; 9], [u64; 9]) {
    let hp = (0..g.n)
        .into_par_iter()
        .map(|u| {
            let mut h = [0u64; 9];
            let a = f[u];
            for &b in f {
                h[f2::rank(a ^ b) as usize] += 1;
            }
            h
        })
        .reduce(|| [0u64; 9], |mut a, b| {
            for i in 0..9 {
                a[i] += b[i]
            }
            a
        });
    let mut he = [0u64; 9];
    for u in 0..g.n {
        for &w in g.nb(u) {
            he[f2::rank(f[u] ^ f[w as usize]) as usize] += 1;
        }
    }
    (hp, he)
}

#[derive(Clone, Debug)]
pub struct Report {
    pub epairs: f64,
    pub eedges: f64,
    pub ratio: f64,
    pub max_edge: u32,
    pub hist_pairs: Vec<u64>,
    pub hist_edges: Vec<u64>,
    /// (k, lhs, rhs) of Proposition S
    pub kernel: Vec<(u32, f64, f64)>,
    pub kernel_ok: bool,
    /// lambda_2 lower bound from 4.2(e)
    pub lambda2_lower: f64,
    /// (hypothesis holds, conclusion holds) for (a), (b), (c)
    pub cons_a: (bool, bool),
    pub cons_b: (bool, bool),
    pub cons_c: (bool, bool, f64),
}

pub fn mean_kernel(h: &[u64], k: u32) -> f64 {
    let tot: u64 = h.iter().sum();
    h.iter().enumerate().map(|(r, &c)| c as f64 * 2f64.powi(-((k as i32) * r as i32))).sum::<f64>() / tot as f64
}

pub fn report_from_hist(hp: &[u64], he: &[u64], lambda2: f64, lambda_min: f64) -> Report {
    let mean = |h: &[u64]| {
        let t: u64 = h.iter().sum();
        h.iter().enumerate().map(|(r, &c)| r as f64 * c as f64).sum::<f64>() / t as f64
    };
    let (ep, ee) = (mean(hp), mean(he));
    let max_edge = he.iter().rposition(|&c| c > 0).unwrap_or(0) as u32;
    let lam = lambda2.max(0.0);
    let mut kernel = vec![];
    let mut ok = true;
    for k in 1..=3 {
        let lhs = mean_kernel(he, k);
        let rhs = lam + (1.0 - lam) * mean_kernel(hp, k);
        if lhs > rhs + 1e-9 {
            ok = false;
        }
        kernel.push((k, lhs, rhs));
    }
    let kp = mean_kernel(hp, 1);
    let ke = mean_kernel(he, 1);
    let l2low = (ke - kp) / (1.0 - kp);
    let lstar = lambda2.abs().max(lambda_min.abs());
    let r = max_edge.max(1);
    let ha = lstar <= 2f64.powi(-(r as i32) - 1);
    let ca = ep <= 6.0 * r as f64 + 4.0;
    let hb = ee <= (1.0 - lambda2) / 4.0;
    let cb = ep <= 4.0 / 3.0 * ee / (1.0 - lambda2) + 1e-12;
    let hc = lambda2 > 0.0 && ee < (1.0 / lambda2).log2();
    let (cc, bound_c) = if hc {
        let c = (2f64.powf(-ee) - lambda2) / (1.0 - lambda2);
        let b = 2.0 * ee / (c * (1.0 - lambda2)) + 2.0 * (1.0 / c).log2().ceil();
        (ep <= b + 1e-12, b)
    } else {
        (true, f64::INFINITY)
    };
    Report {
        epairs: ep,
        eedges: ee,
        ratio: ep / ee,
        max_edge,
        hist_pairs: hp.to_vec(),
        hist_edges: he.to_vec(),
        kernel,
        kernel_ok: ok,
        lambda2_lower: l2low,
        cons_a: (ha, ca),
        cons_b: (hb, cb),
        cons_c: (hc, cc, bound_c),
    }
}

pub fn verify(g: &Graph, f: &[u64], lambda2: f64, lambda_min: f64) -> Report {
    let (hp, he) = histograms(g, f);
    report_from_hist(&hp, &he, lambda2, lambda_min)
}

impl Report {
    pub fn summary(&self) -> String {
        let k = &self.kernel[0];
        format!(
            "ratio={:.4} Ep={:.4} Ee={:.4} maxedge={} kernel(k=1) {:.4}<={:.4} ok={} lam2>={:.4} (a){:?} (b){:?} (c)hyp={} ok={}",
            self.ratio, self.epairs, self.eedges, self.max_edge, k.1, k.2, self.kernel_ok, self.lambda2_lower, self.cons_a, self.cons_b, self.cons_c.0, self.cons_c.1
        )
    }
}

/// Minimal JSON writer for a placement together with its graph (edge list) and report.
pub fn placement_json(g: &Graph, mu: usize, f: &[u64], rep: &Report, extra: &str) -> String {
    let edges: Vec<String> = g.edges().iter().map(|(u, v)| format!("[{u},{v}]")).collect();
    let fs: Vec<String> = f.iter().map(|a| format!("\"{a:016x}\"")).collect();
    format!(
        "{{\"graph\":\"{}\",\"n\":{},\"d\":{},\"mu\":{},\"layout\":\"u64 per matrix, row i = byte i, column j = bit j\",\
\"ratio\":{},\"epairs\":{},\"eedges\":{},\"max_edge_rank\":{},\"hist_pairs\":{:?},\"hist_edges\":{:?},\"kernel_ok\":{},\
\"extra\":{{{}}},\"f\":[{}],\"edges\":[{}]}}\n",
        g.name, g.n, g.d, mu, rep.ratio, rep.epairs, rep.eedges, rep.max_edge, rep.hist_pairs, rep.hist_edges, rep.kernel_ok,
        extra, fs.join(","), edges.join(",")
    )
}
