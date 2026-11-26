//! E3(b): ALS search for restrictions T <= S on K_{2,3}.
//! Usage: e3b_als <Ds> <d12> <d23> <d13> <duu> <starts> <sweeps> [r|c] [seed]
//! Supply: six wires u_i v_j of dim Ds. Demand: v1v2:d12, v2v3:d23, v1v3:d13, u1u2:duu.
use std::time::Instant;
use tensorlab::restrict::*;
use tensorlab::tensor::*;
use num_complex::Complex64;

fn run<T: Scalar>(s: &Network, d: &Network, o: &AlsOpts) {
    let t: Tensor<T> = d.dense();
    let t0 = Instant::now();
    let r = als_multistart(s, &t, o);
    let el = t0.elapsed().as_secs_f64();
    let best = &r[0];
    let dense = residual_dense(s, &best.maps, &t);
    let resids: Vec<String> = r.iter().take(8).map(|x| format!("{:.2e}", x.rel_residual)).collect();
    println!("time {:.1}s | best rel residual {:.3e} (dense recheck {:.3e}) | max map norm {:.3e} | top residuals {:?}",
        el, best.rel_residual, dense, best.max_map_norm, resids);
    let h = &best.history;
    let pick: Vec<String> = [0usize, h.len() / 10, h.len() / 4, h.len() / 2, 3 * h.len() / 4, h.len() - 1]
        .iter().map(|&i| format!("{}:{:.2e}", i, h[i.min(h.len() - 1)])).collect();
    println!("  history(best) {:?}", pick);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p = |i: usize| a[i].parse::<usize>().unwrap();
    let (ds, d12, d23, d13, duu, starts, sweeps) = (p(1), p(2), p(3), p(4), p(5), p(6), p(7));
    let cplx = a.get(8).map(|s| s == "c").unwrap_or(false);
    let seed: u64 = a.get(9).and_then(|s| s.parse().ok()).unwrap_or(1);
    // parties: 0 u1, 1 u2, 2 v1, 3 v2, 4 v3
    let s = Network::new(5, vec![(0, 2, ds), (0, 3, ds), (0, 4, ds), (1, 2, ds), (1, 3, ds), (1, 4, ds)]);
    let d = Network::new(5, vec![(2, 3, d12), (3, 4, d23), (2, 4, d13), (0, 1, duu)]);
    let bad = cut_check(&s, &d);
    let rate = [d12, d23, d13, duu].iter().map(|&x| (x as f64).ln()).fold(f64::INFINITY, f64::min) / (ds as f64).ln();
    println!("Ds={} demand=({},{},{},{}) field={} starts={} sweeps={} | uniform rate {:.4} | violated cuts {:?}",
        ds, d12, d23, d13, duu, if cplx { "C" } else { "R" }, starts, sweeps, rate, bad);
    if !bad.is_empty() { return; }
    let o = AlsOpts { sweeps, starts, complex: cplx, seed, ..Default::default() };
    if cplx { run::<Complex64>(&s, &d, &o) } else { run::<f64>(&s, &d, &o) }
}
