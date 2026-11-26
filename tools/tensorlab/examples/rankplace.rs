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

/// Annealing options with overrides from the environment: RP_T0, RP_T1, RP_CYCLES, RP_BALL (prob. of ball moves).
fn opts(iters: u64, seed: u64) -> Opts {
    let mut o = Opts { iters, seed, ..Default::default() };
    let env = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<f64>().ok());
    if let Some(x) = env("RP_T0") {
        o.t0 = x;
    }
    if let Some(x) = env("RP_T1") {
        o.t1 = x;
    }
    if let Some(x) = env("RP_CYCLES") {
        o.cycles = x as usize;
    }
    if let Some(x) = env("RP_BALL") {
        o.p_moves[3] = x;
    }
    o
}

/// Embed a mu-placement into Mat_mu2 (mu2 >= mu): the layout already does this (zero padding).
fn embed(f: &[u64]) -> Vec<u64> {
    f.to_vec()
}

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
    cuts: Vec<Vec<bool>>,
}

fn info(g: &Graph) -> GraphInfo {
    let t = Instant::now();
    let sp = spectral::spectrum(g);
    let c = cut::beta_cut(g, sp.vec2.as_deref());
    eprintln!("  [{}] lambda2={:.5} lmin={:.4} beta_cut={:.4}{} ({:.1}s)", g.name, sp.lambda2, sp.lambda_min, c.ratio, if c.exact { "" } else { "(lb)" }, t.elapsed().as_secs_f64());
    let cuts = cut::good_cuts(g, &c, 8, 99);
    GraphInfo { l2: sp.lambda2, lmin: sp.lambda_min, cut: c, cuts }
}

/// Ratio search on one graph for several mu; prints one markdown row per mu.
fn study(g: &Graph, gi: &GraphInfo, mus: &[usize], iters: u64, chains: usize, extra: &[(String, usize, Vec<u64>)]) -> f64 {
    let mut best_all = 0.0f64;
    let mut best_mu = 0usize;
    let mut xy_cuts: Vec<Vec<bool>> = vec![];
    let mut best_save: Option<(usize, Vec<u64>, String)> = None;
    let mut prev: Option<Vec<u64>> = None;
    // RP_ONLY_STRUCTURED=1: skip the random/cut-start runs (only the runs from structured placements)
    let skip = std::env::var("RP_ONLY_STRUCTURED").is_ok();
    for &mu in mus.iter().filter(|_| !skip) {
        let t = Instant::now();
        // chain c starts from inits[c % 8]: 0, 1, 3 random; 2 best cut; 4, 6 direct sums of good cuts;
        // 5, 7 the best placement of the previous (smaller) mu, embedded (or more cut sums)
        let diag = Init::Diag(gi.cuts.clone());
        let mut rot = gi.cuts.clone();
        rot.rotate_left(1);
        let diag2 = Init::Diag(rot);
        let pv = match &prev {
            Some(p) => Init::Given(embed(p)),
            None => Init::Cut(gi.cut.side.clone()),
        };
        let inits = vec![Init::Random { rank: 1 }, Init::Random { rank: 0 }, Init::Cut(gi.cut.side.clone()), Init::Random { rank: 2 }, diag, pv.clone(), diag2, pv];
        let o = opts(iters, 1000 + mu as u64);
        let res = run_chains(g, mu, Objective::Ratio, &o, &inits, chains);
        let b = &res[0];
        let rep = verify::verify(g, &b.f, gi.l2, gi.lmin);
        // cuts read off the best placement (a check on the beta_cut lower bound)
        let xy = cut::cuts_from_placement(g, mu, &b.f, 3000, 5);
        if xy.ratio > 0.0 {
            xy_cuts.push(xy.side.clone());
        }
        let vals: Vec<f64> = res.iter().map(|r| r.ratio).collect();
        let worst = vals.iter().cloned().fold(f64::MAX, f64::min);
        // best chain among random starts (inits 0, 1, 3), i.e. without any cut or smaller-mu seed
        let best_rand = res.iter().filter(|r| r.init == 0 || r.init == 1 || r.init == 3).map(|r| r.ratio).fold(0.0, f64::max);
        println!(
            "| {} | {} | {} | {:.4} | {:.4} | {:.4}{} | {} | {:.4} | {:.3} | {:.3} | {:.3} | {:.4} | {:.4} | {:.4} / {:.4} | {} | {:.1} |",
            g.name, g.n, g.d, gi.l2, 1.0 / (1.0 - gi.l2), gi.cut.ratio, if gi.cut.exact { "" } else { "*" }, mu, b.ratio,
            b.ratio / gi.cut.ratio, rep.epairs, rep.eedges, best_rand, worst, xy.ratio, rep.cut_cone_ratio, if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
        );
        assert!(rep.kernel_ok, "kernel inequality violated: {}", rep.summary());
        if xy.ratio > gi.cut.ratio + 1e-9 {
            println!("  NOTE: a cut S_xy read off the placement beats the beta_cut lower bound: {:.4} > {:.4}", xy.ratio, gi.cut.ratio);
        }
        prev = Some(b.f.clone());
        if b.ratio > best_all {
            best_all = b.ratio;
            best_mu = mu;
            best_save = Some((mu, b.f.clone(), verify::placement_json(g, mu, &b.f, &rep, &format!("\"beta_cut\":{},\"lambda2\":{}", gi.cut.ratio, gi.l2))));
        }
    }
    // RP_PERTURB=p: replace a fraction p of the structured placement by random matrices first (basin test)
    let perturb = std::env::var("RP_PERTURB").ok().and_then(|v| v.parse::<f64>().ok()).unwrap_or(0.0);
    for (label, mu, f0) in extra {
        let t = Instant::now();
        let mut f0 = f0.clone();
        let label = if perturb > 0.0 {
            use rand::{rngs::SmallRng, Rng, SeedableRng};
            let mut rng = SmallRng::seed_from_u64(99);
            for x in f0.iter_mut() {
                if rng.gen::<f64>() < perturb {
                    *x = f2::random_matrix(&mut rng, *mu);
                }
            }
            format!("{label}, {:.0}% randomised", perturb * 100.0)
        } else {
            label.clone()
        };
        let f0 = &f0;
        // structured starts are annealed cold (the default schedule melts them; calibration on Cay(Mat_3, rank one))
        let mut o = opts(iters, 77);
        o.t0 = o.t0.min(0.01);
        o.t1 = o.t1.min(0.0005);
        let res = run_chains(g, *mu, Objective::Ratio, &o, &[Init::Given(f0.clone())], chains);
        let b = &res[0];
        let rep = verify::verify(g, &b.f, gi.l2, gi.lmin);
        let (r0, _, _) = evaluate(g, f0);
        println!(
            "| {} (from {label}, start {:.4}) | {} | {} | {:.4} | {:.4} | {:.4} | {} | {:.4} | {:.3} | {:.3} | {:.3} | - | - | - | {} | {:.1} |",
            g.name, r0, g.n, g.d, gi.l2, 1.0 / (1.0 - gi.l2), gi.cut.ratio, mu, b.ratio, b.ratio / gi.cut.ratio, rep.epairs, rep.eedges,
            if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
        );
        let xy = cut::cuts_from_placement(g, *mu, &b.f, 3000, 5);
        if xy.ratio > 0.0 {
            xy_cuts.push(xy.side.clone());
        }
        if b.ratio > best_all {
            best_all = b.ratio;
            best_mu = *mu;
            best_save = Some((*mu, b.f.clone(), verify::placement_json(g, *mu, &b.f, &rep, &format!("\"beta_cut\":{},\"lambda2\":{},\"start\":\"{label}\"", gi.cut.ratio, gi.l2))));
        }
    }
    if let Some((mu, _, js)) = best_save {
        save(&format!("{}_best_mu{mu}", g.name), &js);
    }
    // final beta_cut lower bound: the cut search, and the cuts S_xy read off the best placements, polished
    let mut bc = gi.cut.ratio;
    let mut bc_src = "cut search";
    for (i, side) in xy_cuts.into_iter().enumerate() {
        let (r, _) = cut::polish(g, side, (5_000 * g.n as u64).clamp(100_000, 20_000_000), 3 + i as u64);
        if r > bc + 1e-12 {
            bc = r;
            bc_src = "S_xy cut of a placement, polished";
        }
    }
    println!(
        "SUMMARY | {} | {} | {} | {:.4} | {:.4} | {:.4}{} | {:.4} | {} | {:.4} | {} |",
        g.name, g.n, g.d, gi.l2, 1.0 / (1.0 - gi.l2), bc, if gi.cut.exact { " (exact)" } else { "" }, best_all, best_mu, best_all / bc, bc_src
    );
    best_all
}

/// Graph from a spec: rr d n seed | named NAME | lps p q | sl m k [modulus-binary] | slrand m k count seed |
/// psl2rand q count seed | mat mu count seed | cycle n | torus a b. Returns the graph and, for the
/// families with one, the structured placement (label, mu, f) (mu <= 8 only).
fn graph_from_spec(sp: &[String]) -> (Graph, Vec<(String, usize, Vec<u64>)>) {
    let p = |i: usize| sp[i].parse::<u64>().unwrap();
    let mut st = vec![];
    let g = match sp[0].as_str() {
        "rr" => random_regular(p(2) as usize, p(1) as usize, p(3)),
        "named" => named(&sp[1]).unwrap(),
        "lps" => groups::lps(p(1), p(2)).graph,
        "sl" => {
            let (m, k) = (p(1) as usize, p(2) as usize);
            let md = if sp.len() > 3 { u32::from_str_radix(&sp[3], 2).unwrap() } else { groups::default_modulus(k) };
            let gr = groups::sl_elementary(m, k, md);
            if m * k <= 8 {
                for j in 1..=(k / 2).max(1) {
                    let (mu, f) = gr.conj_projection_placement(j);
                    st.push((format!("conjproj j={j}"), mu, f));
                }
            }
            gr.graph
        }
        "slrand" => {
            let (m, k, c, s) = (p(1) as usize, p(2) as usize, p(3) as usize, p(4));
            let f = groups::Gf2k::new(k, groups::default_modulus(k));
            let gens = groups::random_gens(&f, m, c, s);
            groups::sl_cayley(f, m, gens, &format!("SL{m}(F{})_rand{c}_s{s}", 1 << k)).graph
        }
        "psl2rand" => groups::psl2_random(p(1), p(2) as usize, p(3)).graph,
        "mat" => {
            let (mu, c, s) = (p(1) as usize, p(2) as usize, p(3));
            use rand::{rngs::SmallRng, SeedableRng};
            let mut rng = SmallRng::seed_from_u64(s);
            let mut gens: Vec<u64> = vec![];
            while gens.len() < c {
                let x = f2::random_rank_one(&mut rng, mu);
                if !gens.contains(&x) {
                    gens.push(x);
                }
            }
            let (g, f) = groups::mat_cayley(mu, &gens, &format!("MatCay{mu}_r1x{}_s{s}", if c == 0 { "all".to_string() } else { c.to_string() }));
            st.push((format!("identity mu={mu}"), mu, f));
            g
        }
        "cycle" => cycle(p(1) as usize),
        "torus" => torus(p(1) as usize, p(2) as usize),
        x => panic!("unknown graph spec {x}"),
    };
    assert!(g.is_symmetric() && g.is_connected(), "{}: not symmetric/connected", g.name);
    (g, st)
}

fn split_spec(a: &[String]) -> (Vec<String>, Vec<String>) {
    let k = a.iter().position(|x| x == "--").expect("spec -- params");
    (a[1..k].to_vec(), a[k + 1..].to_vec())
}

/// Gradient-bounded search: maximise E_pairs D subject to D <= r on every edge. One row per r.
fn grad_study(g: &Graph, l2: f64, lmin: f64, mu: usize, rs: &[u32], iters: u64, chains: usize, structured: &[(String, usize, Vec<u64>)]) {
    let n = g.n;
    let mut lip = vec![0.0; 9];
    let samp = n.min(200);
    for u in 0..samp {
        let dist = g.bfs(u * (n / samp));
        for r in 1..9usize {
            lip[r] += dist.iter().map(|&x| (mu as f64).min((r as u32 * x) as f64)).sum::<f64>() / n as f64;
        }
    }
    for &r in rs {
        let t = Instant::now();
        let mut o = opts(iters, 31 + r as u64);
        o.max_edge_rank = Some(r);
        let mut inits = vec![Init::Given(vec![0; n])];
        for (_, m2, f) in structured {
            if *m2 == mu && max_edge_rank(g, f) <= r {
                inits.push(Init::Given(f.clone()));
            }
        }
        let res = run_chains(g, mu, Objective::Pairs, &o, &inits, chains);
        let b = &res[0];
        let rep = verify::verify(g, &b.f, l2, lmin);
        let from0 = res.iter().filter(|x| x.init == 0).map(|x| x.epairs).fold(0.0, f64::max);
        // commutative baseline: the same search restricted to diagonal (Boolean) placements
        let mut od = o.clone();
        od.diag_only = true;
        let resd = run_chains(g, mu, Objective::Pairs, &od, &[Init::Given(vec![0; n])], chains);
        let diag = resd[0].epairs;
        println!(
            "| {} | {n} | {} | {:.4} | {:.2} | {mu} | {r} | {:.4} | {:.4} | {:.4} | {:.3} | {:.3} | {:.3} | {:?} | {} | {:.1} |",
            g.name, g.d, l2, (1.0 / l2).log2(), b.epairs, from0, diag, b.eedges, b.epairs / b.eedges.max(1e-12), lip[r as usize] / samp as f64,
            &rep.hist_pairs[..=mu], if rep.kernel_ok { "ok" } else { "VIOLATED" }, t.elapsed().as_secs_f64()
        );
        assert!(rep.kernel_ok);
        save(&format!("grad_{}_mu{mu}_r{r}", g.name), &verify::placement_json(g, mu, &b.f, &rep, &format!("\"r\":{r},\"lambda2\":{l2}")));
    }
}

fn grad_header() {
    println!("| graph | n | d | λ₂ | log₂(1/λ₂) | μ | r | max E_pairs | from-zero chains | diagonal-only (Boolean) max | E_edges | ratio | r·d_G bound (min μ) | pair-rank histogram | kernel | s |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
}

fn header() {
    println!("| graph | n | d | λ₂ | 1/(1−λ₂) | β_cut | μ | best ratio | ratio/β_cut | E_pairs | E_edges | best random-start chain | worst chain | best S_xy cut / cut-cone ratio of 1−2^(−D) | kernel | s |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
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
        let mut out = vec![0u8; v.len()];
        let t = Instant::now();
        let mut s2 = 0i64;
        for i in 0..100 {
            s2 += f2::ranks_against(v[i], &v, &mut out);
        }
        let ns = t.elapsed().as_nanos() as f64 / (100.0 * 65536.0);
        println!("  batched ranks_against: {ns:.2} ns per rank (checksum {s2})");
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
            let mut structured: Option<(String, usize, Vec<u64>)> = None;
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
                "mat" => {
                    // Cay(Mat_mu(F_2), +) with `count` random rank-one generators (0 = all rank-one matrices)
                    let (mu, c, s): (usize, usize, u64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
                    use rand::{rngs::SmallRng, SeedableRng};
                    let mut rng = SmallRng::seed_from_u64(s);
                    let mut gens: Vec<u64> = vec![];
                    while gens.len() < c {
                        let x = f2::random_rank_one(&mut rng, mu);
                        if !gens.contains(&x) {
                            gens.push(x);
                        }
                    }
                    let (g, f) = groups::mat_cayley(mu, &gens, &format!("MatCay{mu}_r1x{}_s{s}", if c == 0 { "all".to_string() } else { c.to_string() }));
                    structured = Some((format!("identity placement mu={mu}"), mu, f));
                    (g, 5)
                }
                _ => panic!(),
            };
            assert!(g.is_symmetric());
            eprintln!("  {} n = {} d = {} simple = {}", g.name, g.n, g.d, g.is_simple());
            let iters: u64 = a[rest].parse().unwrap();
            let chains: usize = a[rest + 1].parse().unwrap();
            let mus: Vec<usize> = list(&a[rest + 2]);
            assert!(g.is_connected(), "generators do not generate");
            let gi = info(&g);
            let mut extra = vec![];
            if let Some((label, mu, f)) = structured {
                let rep = verify::verify(&g, &f, gi.l2, gi.lmin);
                println!("  structured {label}: {}", rep.summary());
                extra.push((label, mu, f));
            }
            header();
            study(&g, &gi, &mus, iters, chains, &extra);
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
            // em3 d n seed mu rs iters chains
            let d: usize = a[1].parse().unwrap();
            let n: usize = a[2].parse().unwrap();
            let s: u64 = a[3].parse().unwrap();
            let g = random_regular(n, d, s);
            let sp = spectral::spectrum(&g);
            grad_header();
            grad_study(&g, sp.lambda2, sp.lambda_min, a[4].parse().unwrap(), &list(&a[5]), a[6].parse().unwrap(), a[7].parse().unwrap(), &[]);
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
        // generic forms:  gstudy SPEC -- iters chains mus ;  glagr SPEC -- mu iters gammas chains ;
        //                 ggrad SPEC -- mu rs iters chains
        "gstudy" => {
            let (spec, par) = split_spec(&a);
            let (g, st) = graph_from_spec(&spec);
            eprintln!("  {} n = {} d = {}", g.name, g.n, g.d);
            let gi = info(&g);
            for (label, mu, f) in &st {
                let rep = verify::verify(&g, f, gi.l2, gi.lmin);
                println!("  structured {label} (mu={mu}): {}", rep.summary());
            }
            header();
            study(&g, &gi, &list(&par[2]), par[0].parse().unwrap(), par[1].parse().unwrap(), &st);
        }
        "glagr" => {
            let (spec, par) = split_spec(&a);
            let (g, st) = graph_from_spec(&spec);
            let gi = info(&g);
            let mu: usize = par[0].parse().unwrap();
            let iters: u64 = par[1].parse().unwrap();
            let gammas: Vec<f64> = list(&par[2]);
            let chains: usize = par[3].parse().unwrap();
            println!("| graph | μ | γ | best Lagrangian | ratio of that placement | E_pairs | E_edges | best ratio over chains | β_cut | s |");
            println!("|---|---|---|---|---|---|---|---|---|---|");
            for &gm in &gammas {
                let t = Instant::now();
                let o = opts(iters, 5);
                let res = run_chains(&g, mu, Objective::Lagrange(gm), &o, &[Init::Random { rank: 1 }, Init::Random { rank: 0 }, Init::Cut(gi.cut.side.clone()), Init::Diag(gi.cuts.clone())], chains);
                let b = &res[0];
                let br = res.iter().map(|r| r.ratio).fold(0.0, f64::max);
                println!("| {} | {mu} | {gm} | {:.4} | {:.4} | {:.4} | {:.4} | {:.4} | {:.4} | {:.1} |", g.name, b.value, b.ratio, b.epairs, b.eedges, br, gi.cut.ratio, t.elapsed().as_secs_f64());
            }
            for (label, m2, f) in &st {
                let (r, ep, ee) = evaluate(&g, f);
                println!("  structured {label} (mu={m2}): ratio {r:.4}, E_pairs {ep:.4}, E_edges {ee:.4}; Lagrangian at each gamma: {:?}",
                    gammas.iter().map(|gm| ((ep - gm * ee) * 1e4).round() / 1e4).collect::<Vec<_>>());
            }
        }
        "ggrad" => {
            let (spec, par) = split_spec(&a);
            let (g, st) = graph_from_spec(&spec);
            let sp = spectral::spectrum(&g);
            grad_header();
            grad_study(&g, sp.lambda2, sp.lambda_min, par[0].parse().unwrap(), &list(&par[1]), par[2].parse().unwrap(), par[3].parse().unwrap(), &st);
        }
        _ => panic!("unknown command"),
    }
    eprintln!("total {:.1}s", t0.elapsed().as_secs_f64());
}
