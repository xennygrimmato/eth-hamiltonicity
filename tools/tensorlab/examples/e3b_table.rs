//! Calibration table on K_{2,3}: supply wires of dim Ds, all demand vectors (d12,d23,d13,duu) in
//! [1..dmax]^4. For each: is it inside the fractional routing region (f_flow >= 1), the CAT(0)-5 bound
//! (min over box-feasible metrics >= 1), the cut bound; then ALS(+LM) for the ones outside routing.
//! Usage: e3b_table Ds dmax starts sweeps lm
use tensorlab::{k23, metric::*, opt::*, restrict::*, tensor::*};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p = |i: usize| a[i].parse::<usize>().unwrap();
    let (ds, dmax, starts, sweeps, lm) = (p(1), p(2), p(3), p(4), p(5));
    let cuts: Vec<Metric> = (1..16u64).map(|m| Metric::cut(5, m)).collect();
    let mut rays = cuts.clone();
    for x in 0..5 { for y in x + 1..5 {
        rays.push(Metric::from_fn(5, |i, j| { let s = |k: usize| k == x || k == y; if s(i) == s(j) { 2.0 } else { 1.0 } }));
    } }
    let num: Vec<f64> = k23::num().iter().map(|w| w * (ds as f64).ln()).collect();
    let dem_pairs = [(2usize, 3usize), (3, 4), (2, 4), (0, 1)];
    let mut fam = triangle_family(5); fam.extend(box_family(5));
    for code in 0..dmax.pow(4) {
        let mut c = code; let mut dv = [0usize; 4];
        for k in 0..4 { dv[k] = c % dmax + 1; c /= dmax; }
        if dv.iter().all(|&x| x == 1) { continue; }
        let den = weights(5, &dem_pairs.iter().zip(&dv).map(|(&(i, j), &x)| (i, j, (x as f64).ln())).collect::<Vec<_>>());
        let r = |m: &Metric| m.ratio(&num, &den);
        let fcut = cuts.iter().map(|m| r(m)).fold(f64::INFINITY, f64::min);
        let fflow = rays.iter().map(|m| r(m)).fold(f64::INFINITY, f64::min);
        if fflow >= 1.0 - 1e-9 || fcut < 1.0 - 1e-9 { continue; } // routable, or cut-excluded
        let pr = RatioProblem::new(num.clone(), den.clone(), fam.clone());
        let sols = multistart(&pr, &random_metric_starts(5, 40, 9), &Opts { inner: 1500, ..Default::default() });
        let fcat = sols[0].value;
        // [R]1 obstruction: all v-cuts tight and duu >= 2
        let tight = [(0usize, 2usize), (0, 1), (1, 2)].iter().all(|&(x, y)| dv[x] * dv[y] == ds * ds);
        let s = Network::new(5, vec![(0, 2, ds), (0, 3, ds), (0, 4, ds), (1, 2, ds), (1, 3, ds), (1, 4, ds)]);
        let wires: Vec<(usize, usize, usize)> = dem_pairs.iter().zip(&dv).filter(|(_, &x)| x > 1).map(|(&(i, j), &x)| (i, j, x)).collect();
        let d = Network::new(5, wires);
        let mut res = f64::NAN;
        if !(tight && dv[3] >= 2) {
            let t: Tensor<f64> = d.dense();
            let o = AlsOpts { sweeps, starts, seed: 3, ..Default::default() };
            let rr = als_multistart(&s, &t, &o);
            res = rr[0].rel_residual;
            if lm > 0 {
                for b in rr.iter().take(2) { let (_, x, _) = lm_refine(&s, &t, &b.maps, lm); res = res.min(x); }
            }
        }
        let fw5 = r(&k23::w5(3.0, 1.0));
        println!("Ds={} demand={:?}: f_flow={:.4} f_CAT5={:.4} f_W5={:.4} f_cut={:.4} R1-excluded={} best residual={:.3e}",
            ds, dv, fflow, fcat, fw5, fcut, tight && dv[3] >= 2, res);
    }
}
