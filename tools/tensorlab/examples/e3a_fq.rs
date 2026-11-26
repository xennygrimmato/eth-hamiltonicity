//! E3(a): f_Q = min sum_S d / sum_T d over 5-point metrics with triangle + quadrilateral inequalities.
//! Usage: cargo run --release --example e3a_fq -- [family: euler|resh] [starts]
use tensorlab::{k23, metric::*, opt::*};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let fam = args.get(1).map(|s| s.as_str()).unwrap_or("resh");
    let starts: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(2000);
    let n = 5;
    let mut cons = triangle_family(n);
    match fam {
        "euler" => cons.extend(euler_family(n)),
        "resh" => cons.extend(reshetnyak_family(n)),
        "tri" => {}
        "box" => cons.extend(box_family(n)),
        "all" => { cons.extend(reshetnyak_family(n)); cons.extend(box_family(n)); }
        _ => panic!("family"),
    }
    let p = RatioProblem::new(k23::num(), k23::den(), cons.clone());
    let t0 = Instant::now();
    let st = random_metric_starts(n, starts, 12345);
    let sols = multistart(&p, &st, &Opts::default());
    println!("family={} constraints={} starts={} time={:.2}s", fam, cons.len(), starts, t0.elapsed().as_secs_f64());
    let names = k23::names();
    let feas: Vec<&Solution> = sols.iter().filter(|s| s.max_violation < 1e-7).collect();
    println!("feasible: {}  polished: {}", feas.len(), feas.iter().filter(|s| s.polished).count());
    // distinct values histogram
    let mut vals: Vec<f64> = feas.iter().map(|s| (s.value * 1e6).round() / 1e6).collect();
    vals.dedup();
    let mut uniq: Vec<(f64, usize)> = vec![];
    for s in &feas {
        let v = (s.value * 1e6).round() / 1e6;
        if let Some(u) = uniq.iter_mut().find(|u| (u.0 - v).abs() < 1e-9) { u.1 += 1 } else { uniq.push((v, 1)) }
    }
    uniq.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    println!("distinct local optima (value, count): {:?}", &uniq[..uniq.len().min(12)]);
    for s in feas.iter().take(3) {
        println!("--- value {:.15}  viol {:.2e}  kkt {:.2e} polished {}", s.value, s.max_violation, s.kkt_residual, s.polished);
        let pr = pairs(n);
        let scale = 1.0 / s.x.iter().cloned().fold(0.0, f64::max);
        for (k, &(i, j)) in pr.iter().enumerate() {
            print!("{}{}={:.6} ", names[i], names[j], s.x[k] * scale);
        }
        println!();
        for (k, lam) in &s.active {
            println!("   active [{:.3e}] {}", lam, cons[*k].describe(n, &names));
        }
        for (i, b) in &s.at_lower { let (a, c) = pr[*i]; println!("   bound d({}{})=0 [{:.3e}]", names[a], names[c], b); }
    }
    println!("3/sqrt(10) = {:.15}", 3.0 / 10f64.sqrt());
    // check the best point against every family, all orderings
    let b = &feas[0].x;
    let m = Metric::new(n, b.clone());
    println!("best point: tri {:.3e} euler {:.3e} resh {:.3e} box(all 24 orders) {:.3e}", m.max_triangle_violation(),
        m.max_violation(&euler_family(n)).0, m.max_violation(&reshetnyak_family(n)).0, m.max_violation(&box_family_all_orders(n)).0);
    for c in box_family(n) { if let Constraint::BoxQ{p} = &c { let q=[0,1,2,3,4,5].map(|k| b[p[k]].powi(2)); let (t,s,v)=box_min(&q);
        if v < 1e-6 { println!("   box {} min Q={:.3e} at (t,s)=({:.12},{:.12})", c.describe(n,&names), v, t, s); } } }
    println!("best point full precision: {:?}", b);
}
