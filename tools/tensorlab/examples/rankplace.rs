//! Driver for the rank-placement experiments of research/ports/middle/notes.md §9 (E-M1, E-M3, E-M4).
//!
//!   cargo run --release --example rankplace -- bench
//!   cargo run --release --example rankplace -- named <iters> <mus>            # small cubic graphs
//!   cargo run --release --example rankplace -- em1 <d> <n,n,..> <seeds> <mus> <iters> <chains>
//!   cargo run --release --example rankplace -- lagr <d> <n> <seed> <mu> <iters> <g1,g2,..>
//!   cargo run --release --example rankplace -- control <sl2|sl3> <k> <iters> <chains> [mus]
//!   cargo run --release --example rankplace -- cayley <lps p q | slrand m k count seed | psl2rand q count seed> <iters> <chains> <mus>
//!   cargo run --release --example rankplace -- em3 <d> <n> <seed> <mu> <r,r,..> <iters> <chains>
//!   cargo run --release --example rankplace -- em4 <k> <modulus-binary> <steps>
//!   cargo run --release --example rankplace -- nonexp <cycle n | torus a b> <iters> <chains> <mus>
//! Best placements are written to $RANKPLACE_OUT (default research/ports/middle/data/rankplace).

use std::time::Instant;
use tensorlab::rankplace::{anneal::*, cut, f2, graph::*, groups, spectral, verify};

fn out_dir() -> String {
    std::env::var("RANKPLACE_OUT").unwrap_or_else(|_| "../../research/ports/middle/data/rankplace".to_string())
}

fn save(name: &str, body: &str) {
    let dir = out_dir();
    std::fs::create_dir_all(&dir).unwrap();
    let path = format!("{dir}/{name}.json");
    std::fs::write(&path, body).unwrap();
    eprintln!("  saved {path}");
}

fn list<T: std::str::FromStr>(s: &str) -> Vec<T>
where
    T::Err: std::fmt::Debug,
{
    s.split(',').map(|x| x.parse().unwrap()).collect()
}

struct GraphInfo {
    l2: f64,
    lmin: f64,
    cut: cut::CutResult,
}

fn info(g: &Graph) -> GraphInfo {
    let t = Instant::now();
    let sp = spectral::spectrum(g);
    let c = cut::beta_cut(g, sp.vec2.as_deref());
    eprintln!("  [{}] lambda2={:.5} lmin={:.4} beta_cut={:.4}{} ({:.1}s)", g.name, sp.lambda2, sp.lambda_min, c.ratio, if c.exact { "" } else { "(lb)" }, t.elapsed().as_secs_f64());
    GraphInfo { l2: sp.lambda2, lmin: sp.lambda_min, cut: c }
}

/// Ratio search on one graph for several mu; prints one markdown row per mu.
fn study(g: &Graph, gi: &GraphInfo, mus: &[usize], iters: u64, chains: usize, extra: &[(String, usize, Vec<u64>)]) -> f64 {
    let mut best_all = 0.0f64;
    let mut best_save: Option<(usize, Vec<u64>, String)> = None;
    for &mu in mus {
        let t = Instant::now();
        let inits = vec![Init::Random { rank: 1 }, Init::Random { rank: 0 }, Init::Cut(gi.cut.side.clone()), Init::Random { rank: 2 }];
        let opts = Opts { iters, seed: 1000 + mu as u64, ..Default::default() };
        let res = run_chains(g, mu, Objective::Ratio, &opts, &inits, chains);
        let b = &res[0];
        let rep = verify::verify(g, &b.f, gi.l2, gi.lmin);
        let vals: Vec<f64> = res.iter().map(|r| r.ratio).collect();
        let worst = vals.iter().cloned().fold(f64::MAX, f64::min);
        println!(
            "| {} | {} | {} | {:.4} | {:.4} | {:.4}{} | {} | {:.4} | {:.3} | {:.3} | {:.3} | {:.4} | {} | {:.1} |",
            g.name, g.n, g.d, gi.l2, 1.0 / (1.0 - gi.l2), gi.cut.ratio, if gi.cut.exact { "" } else { "*" }, mu, b.ratio,
            b.ratio / gi.cut.ratio, rep.epairs, rep.eedges, worst, if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
        );
        assert!(rep.kernel_ok, "kernel inequality violated: {}", rep.summary());
        if b.ratio > best_all {
            best_all = b.ratio;
            best_save = Some((mu, b.f.clone(), verify::placement_json(g, mu, &b.f, &rep, &format!("\"beta_cut\":{},\"lambda2\":{}", gi.cut.ratio, gi.l2))));
        }
    }
    for (label, mu, f0) in extra {
        let t = Instant::now();
        let opts = Opts { iters, seed: 77, ..Default::default() };
        let res = run_chains(g, *mu, Objective::Ratio, &opts, &[Init::Given(f0.clone())], chains);
        let b = &res[0];
        let rep = verify::verify(g, &b.f, gi.l2, gi.lmin);
        let (r0, _, _) = evaluate(g, f0);
        println!(
            "| {} (from {label}, start {:.4}) | {} | {} | {:.4} | {:.4} | {:.4} | {} | {:.4} | {:.3} | {:.3} | {:.3} | - | {} | {:.1} |",
            g.name, r0, g.n, g.d, gi.l2, 1.0 / (1.0 - gi.l2), gi.cut.ratio, mu, b.ratio, b.ratio / gi.cut.ratio, rep.epairs, rep.eedges,
            if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
        );
        if b.ratio > best_all {
            best_all = b.ratio;
            best_save = Some((*mu, b.f.clone(), verify::placement_json(g, *mu, &b.f, &rep, &format!("\"beta_cut\":{},\"lambda2\":{},\"start\":\"{label}\"", gi.cut.ratio, gi.l2))));
        }
    }
    if let Some((mu, _, js)) = best_save {
        save(&format!("{}_best_mu{mu}", g.name), &js);
    }
    best_all
}

fn header() {
    println!("| graph | n | d | λ₂ | 1/(1−λ₂) | β_cut | μ | best ratio | ratio/β_cut | E_pairs | E_edges | worst chain | kernel | s |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
}

fn bench() {
    use rand::{rngs::SmallRng, SeedableRng};
    let mut rng = SmallRng::seed_from_u64(1);
    for mu in [3usize, 6, 8] {
        let v: Vec<u64> = (0..1 << 16).map(|_| f2::random_matrix(&mut rng, mu)).collect();
        let t = Instant::now();
        let mut s = 0u64;
        for _ in 0..100 {
            for i in 0..v.len() {
                s += f2::rank(v[i] ^ v[(i * 7 + 3) & 0xFFFF]) as u64;
            }
        }
        let ns = t.elapsed().as_nanos() as f64 / (100.0 * 65536.0);
        println!("rank mu={mu}: {ns:.2} ns per rank(a^b) (checksum {s})");
    }
    for n in [128usize, 1024] {
        let g = random_regular(n, 4, 1);
        let t = Instant::now();
        let r = anneal(&g, 6, Objective::Ratio, &Opts { iters: 200_000, ..Default::default() }, make_init(&Init::Random { rank: 1 }, n, 6, 1));
        let s = t.elapsed().as_secs_f64();
        println!("anneal n={n} mu=6: {:.2} us per move, accepted {} , ratio {:.3}", s * 1e6 / 200_000.0, r.accepted, r.ratio);
    }
}

fn structured_report(gr: &groups::SlGroup, gi: &GraphInfo) -> Vec<(String, usize, Vec<u64>)> {
    let k = gr.field.k;
    let mut extra = vec![];
    for j in 1..=(k / 2).max(1) {
        let w = gr.w_basis(j);
        let ee: f64 = gr.gens.iter().map(|s| gr.d_j(s, &w) as f64).sum::<f64>() / gr.gens.len() as f64;
        let n = gr.n();
        let mut hist = vec![0u64; w.len() + 1];
        for g in &gr.elems {
            hist[gr.d_j(g, &w) as usize] += 1;
        }
        let ep = hist.iter().enumerate().map(|(r, &c)| r as f64 * c as f64).sum::<f64>() / n as f64;
        let kp = hist.iter().enumerate().map(|(r, &c)| c as f64 * 2f64.powi(-(r as i32))).sum::<f64>() / n as f64;
        let ke: f64 = gr.gens.iter().map(|s| 2f64.powi(-(gr.d_j(s, &w) as i32))).sum::<f64>() / gr.gens.len() as f64;
        println!(
            "  Grassmann placement gW, W = U^{}, dim U = j = {j}: E_edges d_J = {ee:.4}, E_pairs d_J = {ep:.4}, ratio = {:.4}; hist {:?}; lambda2 >= {:.4} (4.2(e)); kernel {:.4} <= {:.4}",
            gr.m, ep / ee, hist, (ke - kp) / (1.0 - kp), ke, gi.l2.max(0.0) + (1.0 - gi.l2.max(0.0)) * kp
        );
        if gr.m * k <= 8 {
            let (mu, f) = gr.conj_projection_placement(j);
            let rep = verify::verify(&gr.graph, &f, gi.l2, gi.lmin);
            println!("  matrix placement M_g P M_g^-1 (mu = {mu}), j = {j}: {}", rep.summary());
            println!("    hist pairs {:?} edges {:?}", rep.hist_pairs, rep.hist_edges);
            save(&format!("{}_conjproj_j{j}", gr.graph.name), &verify::placement_json(&gr.graph, mu, &f, &rep, "\"kind\":\"conj_projection\""));
            extra.push((format!("conjproj j={j}"), mu, f));
        }
    }
    extra
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let cmd = a.first().map(|s| s.as_str()).unwrap_or("bench");
    let t0 = Instant::now();
    match cmd {
        "bench" => bench(),
        "named" => {
            let iters: u64 = a[1].parse().unwrap();
            let mus: Vec<usize> = list(&a[2]);
            header();
            for nm in ["k33", "petersen", "cube", "heawood", "pappus", "mcgee", "tutte-coxeter"] {
                let g = named(nm).unwrap();
                let gi = info(&g);
                study(&g, &gi, &mus, iters, 8, &[]);
            }
        }
        "em1" => {
            let d: usize = a[1].parse().unwrap();
            let ns: Vec<usize> = list(&a[2]);
            let seeds: Vec<u64> = list(&a[3]);
            let mus: Vec<usize> = list(&a[4]);
            let iters: u64 = a[5].parse().unwrap();
            let chains: usize = a[6].parse().unwrap();
            header();
            for &n in &ns {
                for &s in &seeds {
                    let g = random_regular(n, d, s);
                    let gi = info(&g);
                    study(&g, &gi, &mus, iters, chains, &[]);
                }
            }
        }
        "lagr" => {
            let d: usize = a[1].parse().unwrap();
            let n: usize = a[2].parse().unwrap();
            let s: u64 = a[3].parse().unwrap();
            let mu: usize = a[4].parse().unwrap();
            let iters: u64 = a[5].parse().unwrap();
            let gammas: Vec<f64> = list(&a[6]);
            let g = random_regular(n, d, s);
            let gi = info(&g);
            println!("| graph | μ | γ | best Lagrangian | ratio of that placement | E_pairs | E_edges | β_cut |");
            println!("|---|---|---|---|---|---|---|---|");
            for &gm in &gammas {
                let opts = Opts { iters, seed: 5, ..Default::default() };
                let res = run_chains(&g, mu, Objective::Lagrange(gm), &opts, &[Init::Random { rank: 1 }, Init::Cut(gi.cut.side.clone())], 8);
                let b = &res[0];
                println!("| {} | {mu} | {gm} | {:.4} | {:.4} | {:.4} | {:.4} | {:.4} |", g.name, b.value, b.ratio, b.epairs, b.eedges, gi.cut.ratio);
            }
        }
        "control" => {
            let m: usize = if a[1] == "sl2" { 2 } else { 3 };
            let k: usize = a[2].parse().unwrap();
            let iters: u64 = a[3].parse().unwrap();
            let chains: usize = a[4].parse().unwrap();
            let gr = groups::sl_elementary(m, k, groups::default_modulus(k));
            eprintln!("  group {} n = {}", gr.graph.name, gr.n());
            let gi = info(&gr.graph);
            let extra = structured_report(&gr, &gi);
            let mus: Vec<usize> = if a.len() > 5 { list(&a[5]) } else { vec![(m * k).min(8)] };
            header();
            study(&gr.graph, &gi, &mus, iters, chains, &extra);
        }
        "cayley" => {
            let (g, rest) = match a[1].as_str() {
                "lps" => (groups::lps(a[2].parse().unwrap(), a[3].parse().unwrap()).graph, 4),
                "slrand" => {
                    let (m, k, c, s): (usize, usize, usize, u64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap());
                    let f = groups::Gf2k::new(k, groups::default_modulus(k));
                    let gens = groups::random_gens(&f, m, c, s);
                    let gr = groups::sl_cayley(f, m, gens, &format!("SL{m}(F{})_rand{c}_s{s}", 1 << k));
                    (gr.graph, 6)
                }
                "psl2rand" => (groups::psl2_random(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()).graph, 5),
                _ => panic!(),
            };
            assert!(g.is_symmetric());
            eprintln!("  {} n = {} d = {} simple = {}", g.name, g.n, g.d, g.is_simple());
            let iters: u64 = a[rest].parse().unwrap();
            let chains: usize = a[rest + 1].parse().unwrap();
            let mus: Vec<usize> = list(&a[rest + 2]);
            let gi = info(&g);
            header();
            study(&g, &gi, &mus, iters, chains, &[]);
        }
        "nonexp" => {
            let (g, rest) = match a[1].as_str() {
                "cycle" => (cycle(a[2].parse().unwrap()), 3),
                "torus" => (torus(a[2].parse().unwrap(), a[3].parse().unwrap()), 4),
                _ => panic!(),
            };
            let iters: u64 = a[rest].parse().unwrap();
            let chains: usize = a[rest + 1].parse().unwrap();
            let mus: Vec<usize> = list(&a[rest + 2]);
            let gi = info(&g);
            header();
            study(&g, &gi, &mus, iters, chains, &[]);
        }
        "em3" => {
            let d: usize = a[1].parse().unwrap();
            let n: usize = a[2].parse().unwrap();
            let s: u64 = a[3].parse().unwrap();
            let mu: usize = a[4].parse().unwrap();
            let rs: Vec<u32> = list(&a[5]);
            let iters: u64 = a[6].parse().unwrap();
            let chains: usize = a[7].parse().unwrap();
            let g = random_regular(n, d, s);
            let sp = spectral::spectrum(&g);
            // graph-metric bound: an r-Lipschitz placement has D <= min(mu, r d_G)
            let mut lip = vec![0.0; 9];
            let samp = n.min(200);
            for u in 0..samp {
                let dist = g.bfs(u);
                for r in 1..9usize {
                    lip[r] += dist.iter().map(|&x| (mu as f64).min((r as u32 * x) as f64)).sum::<f64>() / n as f64;
                }
            }
            for &r in &rs {
                let t = Instant::now();
                let opts = Opts { iters, seed: 31 + r as u64, max_edge_rank: Some(r), ..Default::default() };
                // feasible starts: constant, and the identity-like "copy neighbour" growth happens through moves
                let res = run_chains(&g, mu, Objective::Pairs, &opts, &[Init::Given(vec![0; n])], chains);
                let b = &res[0];
                let rep = verify::verify(&g, &b.f, sp.lambda2, sp.lambda_min);
                let worst = res.iter().map(|x| x.epairs).fold(f64::MAX, f64::min);
                println!(
                    "| {} | {n} | {d} | {:.4} | {:.2} | {mu} | {r} | {:.4} | {:.4} | {:.3} | {:.3} | {:.3} | {:?} | {} | {:.1} |",
                    g.name, sp.lambda2, (1.0 / sp.lambda2).log2(), b.epairs, worst, b.eedges, rep.max_edge as f64, lip[r as usize] / samp as f64,
                    &rep.hist_pairs[..=mu], if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
                );
                assert!(rep.kernel_ok);
                save(&format!("em3_{}_mu{mu}_r{r}", g.name), &verify::placement_json(&g, mu, &b.f, &rep, &format!("\"r\":{r},\"lambda2\":{}", sp.lambda2)));
            }
        }
        "em4" => {
            let k: usize = a[1].parse().unwrap();
            let modulus = u32::from_str_radix(&a[2], 2).unwrap();
            let steps: usize = a[3].parse().unwrap();
            let t = Instant::now();
            let gr = groups::sl_elementary(3, k, modulus);
            eprintln!("  {} n = {} built in {:.1}s", gr.graph.name, gr.n(), t.elapsed().as_secs_f64());
            let reortho = gr.n() * steps * 8 < 6_000_000_000;
            let sp = spectral::lanczos(&gr.graph, steps, reortho, 7);
            let j = k / 2;
            let w = gr.w_basis(j);
            let ee: f64 = gr.gens.iter().map(|s| gr.d_j(s, &w) as f64).sum::<f64>() / gr.gens.len() as f64;
            use rayon::prelude::*;
            let hist = gr
                .elems
                .par_iter()
                .fold(|| vec![0u64; w.len() + 1], |mut h, g| {
                    h[gr.d_j(g, &w) as usize] += 1;
                    h
                })
                .reduce(|| vec![0u64; w.len() + 1], |mut a, b| {
                    for i in 0..a.len() {
                        a[i] += b[i]
                    }
                    a
                });
            let n = gr.n() as f64;
            let ep = hist.iter().enumerate().map(|(r, &c)| r as f64 * c as f64).sum::<f64>() / n;
            let kp = hist.iter().enumerate().map(|(r, &c)| c as f64 * 2f64.powi(-(r as i32))).sum::<f64>() / n;
            let ke: f64 = gr.gens.iter().map(|s| 2f64.powi(-(gr.d_j(s, &w) as i32))).sum::<f64>() / gr.gens.len() as f64;
            println!(
                "| {} | {} | {} | {:.6} | {:?} | {:.6} | {:.4} | {:.4} | {:.4} | {:.4} | {:?} | {:.0} |",
                gr.graph.name, gr.n(), gr.graph.d, sp.lambda2, sp.history.iter().map(|x| (x * 1e6).round() / 1e6).collect::<Vec<_>>(), sp.lambda_min,
                0.75 - 2f64.powi(1 - 3 * j as i32), (ke - kp) / (1.0 - kp), ee, ep, hist, t.elapsed().as_secs_f64()
            );
        }
        _ => panic!("unknown command"),
    }
    eprintln!("total {:.1}s", t0.elapsed().as_secs_f64());
}
