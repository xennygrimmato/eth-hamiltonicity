//! E3(a): search CAT(0) model spaces for 5-point configurations with small R = sum_S d / sum_T d.
//! Usage: cargo run --release --example e3a_cat -- <trees k starts | euclid dim starts | cone line_dim starts | w5>
use tensorlab::{k23, metric::*, models::*};
use std::time::Instant;

fn report(r: &ModelResult) {
    let names = k23::names();
    let fam: Vec<Constraint> = triangle_family(5).into_iter().chain(reshetnyak_family(5)).collect();
    let mx = r.metric.d.iter().cloned().fold(0.0, f64::max);
    print!("  R={:.12} [{}]  ", r.value, r.label);
    for (k, (i, j)) in pairs(5).into_iter().enumerate() {
        print!("{}{}={:.5} ", names[i], names[j], r.metric.d[k] / mx);
    }
    println!("\n    max(tri,resh) violation={:.2e}  l1 residual={:.2e}", r.metric.max_violation(&fam).0, r.metric.l1_nnls().0);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (num, den) = (k23::num(), k23::den());
    let t0 = Instant::now();
    match a[1].as_str() {
        "trees" => {
            let k: usize = a[2].parse().unwrap();
            let starts: usize = a[3].parse().unwrap();
            let res = min_ratio_tree_products(5, k, &num, &den, starts, 4000, 7);
            println!("products of {} trees: {} topology tuples, {:.1}s", k, res.len(), t0.elapsed().as_secs_f64());
            for r in res.iter().take(4) { report(r); println!("    lengths {:?}", r.params.iter().map(|x| (x*1e5).round()/1e5).collect::<Vec<_>>()); }
        }
        "euclid" => {
            let dim: usize = a[2].parse().unwrap();
            let starts: usize = a[3].parse().unwrap();
            let res = min_ratio_euclidean(5, dim, &num, &den, starts, 20000, 3);
            println!("R^{}: {:.1}s", dim, t0.elapsed().as_secs_f64());
            for r in res.iter().take(2) { report(r); }
        }
        "cone" => {
            let ld: usize = a[2].parse().unwrap();
            let starts: usize = a[3].parse().unwrap();
            let cone = GraphCone::new(14, heawood_edges(std::f64::consts::PI / 3.0));
            let res = min_ratio_graph_cone(&cone, 5, ld, &num, &den, starts, 3000, 11);
            println!("cone(Heawood, edge pi/3) x R^{}: {:.1}s, girth {:.6}", ld, t0.elapsed().as_secs_f64(), cone.girth());
            for r in res.iter().take(3) { report(r); }
        }
        "w5" => {
            let m = k23::w5(3.0, 1.0);
            let fam: Vec<Constraint> = triangle_family(5).into_iter().chain(reshetnyak_family(5)).collect();
            println!("W5 (l=3,h=1): R={:.15} 3/sqrt10={:.15}", m.ratio(&num, &den), 3.0/10f64.sqrt());
            println!("  tri viol {:.3e}  resh viol {:.3e}  euler viol {:.3e}", m.max_triangle_violation(),
                m.max_violation(&reshetnyak_family(5)).0, m.max_violation(&euler_family(5)).0);
            let (r, _) = m.l1_nnls();
            let (hv, b) = m.max_hypermetric_violation(5);
            println!("  l1 (cut cone NNLS) relative residual {:.4e}; max hypermetric (pentagonal) violation {:.6} at b={:?}", r, hv, b);
            println!("  min cut ratio {:?}; Gram min eig {:.4}", Metric::min_cut_ratio(5, &num, &den), m.euclidean_gram_min_eig());
            let _ = fam;
        }
        _ => panic!(),
    }
}
