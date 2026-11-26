//! Border search on K_{2,3}: maps polynomial in eps of degree K, target eps^h T.
//! Usage: e3b_border Ds d12 d23 d13 duu K h starts sweeps [seed]
use std::time::Instant;
use tensorlab::restrict::*;
use tensorlab::tensor::*;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p = |i: usize| a[i].parse::<usize>().unwrap();
    let (ds, d12, d23, d13, duu, k, h, starts, sweeps) = (p(1), p(2), p(3), p(4), p(5), p(6), p(7), p(8), p(9));
    let seed: u64 = a.get(10).and_then(|s| s.parse().ok()).unwrap_or(1);
    let s = Network::new(5, vec![(0, 2, ds), (0, 3, ds), (0, 4, ds), (1, 2, ds), (1, 3, ds), (1, 4, ds)]);
    let d = Network::new(5, vec![(2, 3, d12), (3, 4, d23), (2, 4, d13), (0, 1, duu)]);
    let t: Tensor<f64> = d.dense();
    let o = AlsOpts { sweeps, starts, seed, ..Default::default() };
    let t0 = Instant::now();
    let r = border_multistart(&s, &t, k, h, &o);
    let b = &r[0];
    let chk = border_check(&s, &t, &b.maps, h, &[1e-1, 1e-2, 1e-3]);
    let top: Vec<String> = r.iter().take(6).map(|x| format!("{:.2e}", x.rel_residual)).collect();
    println!("Ds={} demand=({},{},{},{}) K={} h={} starts={} sweeps={}: best border residual {:.3e} (top {:?}), max coef norm {:.2e}, dense check |T_eps/eps^h - T| at eps=1e-1,1e-2,1e-3: {:.2e} {:.2e} {:.2e} ({:.1}s)",
        ds, d12, d23, d13, duu, k, h, starts, sweeps, b.rel_residual, top, b.max_coef_norm, chk[0], chk[1], chk[2], t0.elapsed().as_secs_f64());
}
