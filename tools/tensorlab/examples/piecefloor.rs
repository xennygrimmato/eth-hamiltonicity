//! Driver for `piecefloor` (spec S3 of research/ports/c1d1/notes.md; notebook research/sat3/s3-experiments.md).
//!
//!   piecefloor exh DESIGN MU [HUBPTS] [SPLIT]        exhaustive hub orbits in Mat_MU (MU <= 3), exact legs
//!   piecefloor anneal DESIGN MU ITERS CHAINS [SEED]  annealing over full placements in Mat_MU (MU <= 8)
//!   piecefloor hubanneal DESIGN MU ITERS CHAINS [SEED]  hub annealing with exact legs (MU <= 3)
//!   piecefloor model DESIGN ARMS K ITERS CHAINS [SEED]  spider^j x R^K (ARMS = "-" or e.g. "3" / "3,3" / "4,3,3")
//!   piecefloor far DESIGN ARMS K ITERS CHAINS [SEED]    far-leg (Busemann) limit in spider^j x R^K, hubs annealed
//!
//! DESIGN: crossing | crossing-half | crossing-tenth | k4 | delta3 | delta3-2.
//! Value printed = (sum_m b_m^+)/p (per merge, units of lambda); rho = value / total edge weight.
//! Best configurations are written as JSON to $PF_OUT (default research/sat3/data).
use std::io::Write;
use std::time::Instant;
use tensorlab::piecefloor::*;
use tensorlab::rankplace::f2;

fn out_dir() -> String {
    std::env::var("PF_OUT").unwrap_or_else(|_| "../../research/sat3/data".into())
}

fn save(name: &str, json: String) {
    let dir = out_dir();
    std::fs::create_dir_all(&dir).ok();
    let path = format!("{}/{}.json", dir, name);
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(json.as_bytes()).unwrap();
    println!("wrote {}", path);
}

fn mats_json(pts: &[u64], mu: usize) -> String {
    let v: Vec<String> = pts.iter().map(|&a| format!("\"{}\"", f2::to_string(a, mu))).collect();
    format!("[{}]", v.join(","))
}

fn fmt_b(b: &[f64]) -> String {
    let v: Vec<String> = b.iter().map(|x| format!("{:.6}", x)).collect();
    format!("[{}]", v.join(", "))
}

/// Minimal reader for a far-pod JSON written by `far` (hubs with arm/t/x lists) -> TreeModel, padded to nv vertices.
fn load_pod_start(path: &str, nf: usize, nv: usize, k: usize) -> TreeModel {
    let txt = std::fs::read_to_string(path).unwrap();
    let hubs_txt = &txt[txt.find("\"hubs\":[").unwrap() + 8..];
    let mut hubs = vec![];
    let mut arms_n = 0;
    for chunk in hubs_txt.split("{\"arm\":").skip(1) {
        let nums = |key: &str| -> Vec<f64> {
            let i = chunk.find(key).map(|i| i + key.len()).unwrap_or(0);
            let j = chunk[i..].find(']').unwrap() + i;
            chunk[i..j].trim_start_matches('[').split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect()
        };
        let arm = nums("");
        let tt = nums("\"t\":");
        let xx = nums("\"x\":");
        let mut cp = CPoint::default();
        arms_n = arm.len();
        for f in 0..arm.len() {
            cp.arm[f] = arm[f] as u8;
            cp.t[f] = tt[f];
        }
        for c in 0..xx.len().min(k) {
            cp.x[c] = xx[c];
        }
        hubs.push(cp);
    }
    let model = Model { arms: vec![3; arms_n], k };
    let mut tm = pods_to_trees(&model, &hubs);
    while tm.factors.len() < nf {
        // extra factor: everything at one point
        let n = 1;
        let mut f = TreeFactor { parent: vec![0; n], len: vec![0.0; n], hv: vec![0; hubs.len()], dist: vec![] };
        f.recompute();
        tm.factors.push(f);
    }
    for f in tm.factors.iter_mut() {
        while f.parent.len() < nv {
            f.parent.push(0);
            f.len.push(0.0);
        }
        f.recompute();
    }
    tm
}

fn tree_json(f: &TreeFactor) -> String {
    format!("{{\"parent\":{:?},\"len\":{:?},\"hv\":{:?}}}", f.parent, f.len, f.hv)
}

/// limitexh Q P ARMS            exhaustive pod labellings, radii in {0,1}, <= ARMS arms
/// limit Q P NV ITERS CHAINS [SEED]   annealing over one general tree (NV vertices), seeded by the
///                                    index-|Q| point labelling and by the exhaustive optimum if present
fn limit_cmd(a: &[String]) {
    let t = Instant::now();
    let net = LimitNet::new(&a[2], a[3].parse().unwrap());
    let p = net.p() as f64;
    let m = net.q.m;
    if a[1] == "limitexh" {
        let arms: usize = a[4].parse().unwrap();
        let (v, lab, cnt) = limit_exhaustive_pod01(&net, arms);
        println!("Q={} p={} pods01 arms<={}: {} labellings, time {:.1}s", net.q.name, net.p(), arms, cnt, t.elapsed().as_secs_f64());
        println!("BEST Phi = {:.9}  level = {:.6}  (flat Phi = {}, level {:.6}; cap Phi = {})", v, v.sqrt() / p, net.p(), 1.0 / p.sqrt(), p * p / 2.0);
        for k in 0..net.p() {
            println!("  merge {}: arms of classes q=0..{}: {:?}", k, m - 1, &lab[k * m..(k + 1) * m]);
        }
        save(&format!("limitexh_{}_p{}_a{}", net.q.name, net.p(), arms),
             format!("{{\"Q\":\"{}\",\"p\":{},\"phi\":{},\"tree\":{}}}", net.q.name, net.p(), v, tree_json(&net.pod01(&lab, arms))));
    } else {
        let nv: usize = a[4].parse().unwrap();
        let iters: usize = a[5].parse().unwrap();
        let chains: usize = a[6].parse().unwrap();
        let seed: u64 = a.get(7).map(|s| s.parse().unwrap()).unwrap_or(1);
        // seeds: subgroup labellings (classes q in H on arm k+1 at radius 1, others at the centre), for
        // every subgroup H of Q generated by <= 2 elements
        let mut subs: Vec<Vec<usize>> = vec![];
        for g1 in 0..m {
            for g2 in g1..m {
                let mut h = vec![0usize];
                loop {
                    let mut grew = false;
                    for &x in &h.clone() {
                        for &g in &[g1, g2] {
                            let y = net.q.add[x * m + g];
                            if !h.contains(&y) {
                                h.push(y);
                                grew = true;
                            }
                        }
                    }
                    if !grew {
                        break;
                    }
                }
                h.sort_unstable();
                if !subs.contains(&h) {
                    subs.push(h);
                }
            }
        }
        let mut starts = vec![];
        let mut seedvals = vec![];
        for h in &subs {
            let mut lab = vec![0; net.nhubs()];
            for k in 0..net.p() {
                for &x in h {
                    lab[k * m + x] = k + 1;
                }
            }
            let f = net.pod01(&lab, net.p());
            seedvals.push((net.phi(&f), h.len()));
            starts.push((net.phi(&f), f));
        }
        seedvals.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        // best seeds first; PF_NOSTART: random chains only
        starts.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        let starts: Vec<TreeFactor> = if std::env::var("PF_NOSTART").is_ok() { vec![] } else { starts.into_iter().map(|x| x.1).collect() };
        println!("subgroup seeds (Phi, |H|): {:?}", seedvals.iter().map(|(v, h)| format!("{:.6}/{}", v, h)).collect::<Vec<_>>());
        let r = anneal_limit(&net, nv, iters, chains, 0.05, 1e-6, seed, &starts);
        let v = r[0].0;
        println!("Q={} p={} one tree NV={} iters={} chains={} time {:.1}s", net.q.name, net.p(), nv, iters, chains, t.elapsed().as_secs_f64());
        println!("BEST Phi = {:.9}  level = {:.6}  (flat {}, cap {})", v, v.sqrt() / p, net.p(), p * p / 2.0);
        let q: Vec<String> = r.iter().map(|x| format!("{:.5}", x.0)).collect();
        println!("chains: {:?}", q);
        let f = &r[0].1;
        println!("tree: parent {:?}\n      len {:?}\n      hv {:?}", f.parent, f.len.iter().map(|x| (x * 1e4).round() / 1e4).collect::<Vec<_>>(), f.hv);
        save(&format!("limit_{}_p{}_n{}_s{}", net.q.name, net.p(), nv, seed),
             format!("{{\"Q\":\"{}\",\"p\":{},\"phi\":{},\"tree\":{}}}", net.q.name, net.p(), v, tree_json(f)));
    }
    eprintln!("elapsed {:.2}s", t.elapsed().as_secs_f64());
}

/// cone TARGET GRAPH SUBDIV ITERS CHAINS [SEED]
///   TARGET: a design name (delta3, crossing, ...) or limit:Q:P; GRAPH: see ConeGraph::named, or
///   free:N0:NE[:K] (random free link, N0 vertices, NE edges, K extra isolated points; lengths annealed)
fn cone_cmd(a: &[String]) {
    let t = Instant::now();
    let tname = &a[2];
    let gspec = &a[3];
    let sub: usize = a[4].parse().unwrap();
    let iters: usize = a[5].parse().unwrap();
    let chains: usize = a[6].parse().unwrap();
    let seed: u64 = a.get(7).map(|s| s.parse().unwrap()).unwrap_or(1);
    let des;
    let net;
    let target = if let Some(r) = tname.strip_prefix("limit:") {
        let v: Vec<&str> = r.split(':').collect();
        net = LimitNet::new(v[0], v[1].parse().unwrap());
        ConeTarget::Limit(&net)
    } else {
        des = Design::by_name(tname).unwrap();
        ConeTarget::Design(&des)
    };
    let free = gspec.starts_with("free:");
    let g = if free {
        let v: Vec<usize> = gspec[5..].split(':').map(|x| x.parse().unwrap()).collect();
        let mut rng = rand::SeedableRng::seed_from_u64(seed);
        let _: &mut rand::rngs::SmallRng = &mut rng;
        ConeGraph::random_free(&mut rng, v[0], v[1], sub, *v.get(2).unwrap_or(&0))
    } else {
        ConeGraph::named(gspec, sub)
    };
    // seeds: "one node / one class per merge" at p mutually far vertices (greedy), radius 1
    let p = match &target { ConeTarget::Design(d) => d.p(), ConeTarget::Limit(l) => l.p() };
    let nh = match &target { ConeTarget::Design(d) => d.nhubs(), ConeTarget::Limit(l) => l.nhubs() };
    let mut far = vec![0usize];
    while far.len() < p {
        let nx = (0..g.n).max_by(|&x, &y| {
            let fx = far.iter().map(|&f| g.dist[f * g.n + x]).fold(f64::INFINITY, f64::min);
            let fy = far.iter().map(|&f| g.dist[f * g.n + y]).fold(f64::INFINITY, f64::min);
            fx.partial_cmp(&fy).unwrap()
        }).unwrap();
        far.push(nx);
    }
    let mut seedpl = ConePlacement { hv: vec![0; nh], r: vec![0.0; nh] };
    match &target {
        ConeTarget::Design(d) => {
            for m in 0..p {
                let h = d.hub(m, d.groups[m][0]) - d.nlegs();
                seedpl.hv[h] = far[m];
                seedpl.r[h] = 1.0;
            }
        }
        ConeTarget::Limit(l) => {
            for k in 0..p {
                seedpl.hv[k * l.q.m] = far[k];
                seedpl.r[k * l.q.m] = 1.0;
            }
        }
    }
    let s0 = target.score(&g, &seedpl);
    let starts = if std::env::var("PF_NOSTART").is_ok() { vec![] } else { vec![seedpl] };
    let r = anneal_cone(&target, &g, free, iters, chains, 0.05, 1e-6, seed, &starts);
    let best = r[0].0;
    let (vname, v, v0) = match &target {
        ConeTarget::Design(d) => ("value per merge (1/p)sqrt(E Gamma)", (d.total_weight() * best).sqrt() / p as f64, (d.total_weight() * s0).sqrt() / p as f64),
        ConeTarget::Limit(_) => ("level sqrt(Phi)/p", best.sqrt() / p as f64, s0.sqrt() / p as f64),
    };
    println!("cone {} over {} (n = {}, girth {:.4}) iters={} chains={} time {:.1}s", tname, g.name, g.n, g.girth(), iters, chains, t.elapsed().as_secs_f64());
    println!("seed score {:.6} ({} {:.6});  BEST score (Gamma or Phi) = {:.6}   {} = {:.6}", s0, vname, v0, best, vname, v);
    let q: Vec<String> = r.iter().map(|x| format!("{:.4}", x.0)).collect();
    println!("chains: {:?}", q);
    if let ConeTarget::Design(d) = &target {
        let b = cone_product_b(d, &[(&r[0].1, &r[0].2)]);
        println!("single factor (unsymmetrised) b = {}  (min {:.4})", fmt_b(&b), b.iter().cloned().fold(f64::INFINITY, f64::min));
    }
    println!("hubs: vertex {:?}\n      radius {:?}", r[0].2.hv, r[0].2.r.iter().map(|x| (x * 1e4).round() / 1e4).collect::<Vec<_>>());
    if free {
        println!("free link base edges: {:?}", r[0].1.chains.iter().map(|c| { let e = r[0].1.edges[c[0]]; (e.0, r[0].1.edges[*c.last().unwrap()].1, (c.iter().map(|&i| r[0].1.edges[i].2).sum::<f64>() * 1e4).round() / 1e4) }).collect::<Vec<_>>());
    }
    let gj = format!("{{\"n\":{},\"edges\":{:?}}}", r[0].1.n, r[0].1.edges.iter().map(|&(x, y, l)| (x, y, l)).collect::<Vec<_>>());
    save(&format!("cone_{}_{}_s{}_seed{}", tname.replace(':', "-"), gspec.replace(':', "-"), sub, seed),
         format!("{{\"target\":\"{}\",\"graph\":{},\"score\":{},\"value\":{},\"hv\":{:?},\"r\":{:?}}}", tname, gj, best, v, r[0].2.hv, r[0].2.r));
    eprintln!("elapsed {:.2}s", t.elapsed().as_secs_f64());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let cmd = a.get(1).map(|s| s.as_str()).unwrap_or("help");
    if cmd == "cone" {
        cone_cmd(&a);
        return;
    }
    if cmd == "limitexh" || cmd == "limit" {
        limit_cmd(&a);
        return;
    }
    let des = a.get(2).and_then(|s| Design::by_name(s));
    let t = Instant::now();
    match (cmd, des) {
        ("exh", Some(des)) => {
            let mu: usize = a[3].parse().unwrap();
            let hub_pts: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(1 << (mu * mu));
            let split: usize = a.get(5).map(|s| s.parse().unwrap()).unwrap_or(3);
            let sp = MatSpace::new(mu);
            // group: linear isometries of Mat_mu if hubs range over all of it, else of Mat_2 (block)
            let group = if hub_pts == sp.n {
                linear_isometries(mu)
            } else {
                assert!(hub_pts == 16 && mu == 3, "HUBPTS must be 2^(mu^2), or 16 with mu = 3");
                let g2 = linear_isometries(2);
                // extend each Mat_2 isometry blockwise: only valid on indices < 16 (top-left 2x2 block
                // = indices whose matrix lies in that block). Indices of Mat_2 inside Mat_3:
                let emb: Vec<usize> = (0..16).map(|i| mat2idx(idx2mat(i, 2), 3)).collect();
                // relabel: hubs use point indices emb[i]; we pass a group on 0..16 and map later
                let _ = emb;
                g2
            };
            println!("{} mu={} hub_pts={} group={} nhubs={}", des.name, mu, hub_pts, group.len(), des.nhubs());
            let r = if hub_pts == sp.n {
                exhaustive_hubs(&des, &sp, &group, hub_pts, split)
            } else {
                exhaustive_hubs_sub(&des, &sp, &group, split)
            };
            let v = r.best / des.p() as f64;
            println!("leaves (hub orbits) = {}", r.leaves);
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6})  subset {:b}", v, v / des.total_weight(), des.flat_value(), r.subset);
            let mut pts: Vec<u64> = r.legs.iter().map(|&i| sp.mats[i]).collect();
            pts.extend(r.hubs.iter().map(|&i| sp.mats[i]));
            let b = b_mat(&des, &pts);
            println!("b = {}  value(b) = {:.6}", fmt_b(&b), value(&b));
            println!("points (legs then hubs) = {}", mats_json(&pts, mu));
            println!("top values (p*value, #orbits): {:?}", r.top.iter().map(|(v, c)| (format!("{:.4}", v / des.p() as f64), *c)).collect::<Vec<_>>());
            save(&format!("exh_{}_mu{}_h{}", des.name, mu, hub_pts),
                 format!("{{\"design\":\"{}\",\"space\":\"mat\",\"mu\":{},\"value\":{},\"b\":{:?},\"points\":{},\"leaves\":{}}}",
                         des.name, mu, v, b, mats_json(&pts, mu), r.leaves));
        }
        ("anneal", Some(des)) => {
            let mu: usize = a[3].parse().unwrap();
            let iters: usize = a[4].parse().unwrap();
            let chains: usize = a[5].parse().unwrap();
            let seed: u64 = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(1);
            let o = AnnealOpts { iters, chains, t0: 0.3, t1: 1e-4, seed, polish: mu <= 4 };
            let mut sols = anneal_mat(&des, mu, &o);
            if mu <= 3 {
                // exact legs for the best hubs of each chain
                let sp = MatSpace::new(mu);
                let mut scratch = vec![];
                for s in sols.iter_mut() {
                    let nl = des.nlegs();
                    let hubs: Vec<usize> = s.pts[nl..].iter().map(|&x| mat2idx(x, mu)).collect();
                    let (v, _, legs) = sp.best_legs(&des, &hubs, true, &mut scratch);
                    if v / des.p() as f64 > s.value + 1e-9 {
                        for (i, &l) in legs.iter().enumerate() {
                            s.pts[i] = sp.mats[l];
                        }
                        s.b = b_mat(&des, &s.pts);
                        s.value = value(&s.b);
                    }
                }
                sols.sort_by(|x, y| y.value.partial_cmp(&x.value).unwrap());
            }
            let vals: Vec<f64> = sols.iter().map(|s| s.value).collect();
            let hits = vals.iter().filter(|&&v| v > vals[0] - 1e-9).count();
            println!("{} mu={} iters={} chains={} seed={}  time {:.1}s", des.name, mu, iters, chains, seed, t.elapsed().as_secs_f64());
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6})  hit by {}/{} chains", vals[0], vals[0] / des.total_weight(), des.flat_value(), hits, chains);
            println!("b = {}", fmt_b(&sols[0].b));
            println!("points = {}", mats_json(&sols[0].pts, mu));
            let mut q = vals.clone();
            q.dedup_by(|x, y| (*x - *y).abs() < 1e-6);
            println!("distinct chain values (top 12): {:?}", q.iter().take(12).map(|v| format!("{:.4}", v)).collect::<Vec<_>>());
            save(&format!("anneal_{}_mu{}_s{}", des.name, mu, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"mat\",\"mu\":{},\"value\":{},\"b\":{:?},\"points\":{}}}",
                         des.name, mu, vals[0], sols[0].b, mats_json(&sols[0].pts, mu)));
        }
        ("hubanneal", Some(des)) => {
            let mu: usize = a[3].parse().unwrap();
            let iters: usize = a[4].parse().unwrap();
            let chains: usize = a[5].parse().unwrap();
            let seed: u64 = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(1);
            let sp = MatSpace::new(mu);
            let r = anneal_hubs_exact(&des, &sp, iters, chains, 0.3, 1e-4, seed, None);
            let v = r[0].0 / des.p() as f64;
            let hits = r.iter().filter(|x| x.0 > r[0].0 - 1e-9).count();
            let mut pts: Vec<u64> = r[0].2.iter().map(|&i| sp.mats[i]).collect();
            pts.extend(r[0].1.iter().map(|&i| sp.mats[i]));
            let b = b_mat(&des, &pts);
            println!("{} mu={} hub-anneal iters={} chains={}  time {:.1}s", des.name, mu, iters, chains, t.elapsed().as_secs_f64());
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6}) hit by {}/{}", v, v / des.total_weight(), des.flat_value(), hits, chains);
            println!("b = {}  points = {}", fmt_b(&b), mats_json(&pts, mu));
            let mut q: Vec<f64> = r.iter().map(|x| x.0 / des.p() as f64).collect();
            q.dedup_by(|x, y| (*x - *y).abs() < 1e-6);
            println!("distinct chain values (top 12): {:?}", q.iter().take(12).map(|v| format!("{:.4}", v)).collect::<Vec<_>>());
            save(&format!("hubanneal_{}_mu{}_s{}", des.name, mu, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"mat\",\"mu\":{},\"value\":{},\"b\":{:?},\"points\":{}}}",
                         des.name, mu, v, b, mats_json(&pts, mu)));
        }
        ("modelfrom", Some(des)) => {
            // modelfrom DESIGN FILE ITERS CHAINS [SEED]; FILE: first line "nf k", then one line per point:
            // nf arms, nf radii, k coordinates (whitespace separated)
            let txt = std::fs::read_to_string(&a[3]).unwrap();
            let mut lines = txt.lines();
            let hd: Vec<usize> = lines.next().unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
            let (nf, k) = (hd[0], hd[1]);
            let pts: Vec<CPoint> = lines
                .filter(|l| !l.trim().is_empty())
                .map(|l| {
                    let v: Vec<f64> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
                    let mut p = CPoint::default();
                    for f in 0..nf {
                        p.arm[f] = v[f] as u8;
                        p.t[f] = v[nf + f];
                    }
                    for c in 0..k {
                        p.x[c] = v[2 * nf + c];
                    }
                    p
                })
                .collect();
            let m = Model { arms: vec![3; nf], k };
            let iters: usize = a[4].parse().unwrap();
            let chains: usize = a[5].parse().unwrap();
            let seed: u64 = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(1);
            let v0 = value(&m.b(&des, &pts));
            let sols = anneal_model_start(&des, &m, iters, chains, 1e-3, 1e-7, seed, Some(&pts));
            println!("{} finite configuration in {} from {}: start value {:.6}, after annealing {:.6} (b = {})  time {:.1}s",
                     des.name, m.label(), a[3], v0, sols[0].value, fmt_b(&sols[0].b), t.elapsed().as_secs_f64());
        }
        ("model", Some(des)) => {
            let arms: Vec<usize> = if a[3] == "-" { vec![] } else { a[3].split(',').map(|s| s.parse().unwrap()).collect() };
            let k: usize = a[4].parse().unwrap();
            let iters: usize = a[5].parse().unwrap();
            let chains: usize = a[6].parse().unwrap();
            let seed: u64 = a.get(7).map(|s| s.parse().unwrap()).unwrap_or(1);
            let m = Model { arms, k };
            let sols = anneal_model(&des, &m, iters, chains, 0.3, 1e-5, seed);
            let v = sols[0].value;
            println!("{} model {} iters={} chains={}  time {:.1}s", des.name, m.label(), iters, chains, t.elapsed().as_secs_f64());
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6})", v, v / des.total_weight(), des.flat_value());
            println!("b = {}", fmt_b(&sols[0].b));
            let q: Vec<String> = sols.iter().take(10).map(|s| format!("{:.4}", s.value)).collect();
            println!("top chains: {:?}", q);
            let pj: Vec<String> = sols[0]
                .pts
                .iter()
                .map(|p| format!("{{\"arm\":{:?},\"t\":{:?},\"x\":{:?}}}", &p.arm[..m.arms.len()], &p.t[..m.arms.len()], &p.x[..m.k]))
                .collect();
            save(&format!("model_{}_{}_k{}_s{}", des.name, m.arms.iter().map(|x| x.to_string()).collect::<Vec<_>>().join("-"), k, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"model\",\"arms\":{:?},\"k\":{},\"value\":{},\"b\":{:?},\"points\":[{}]}}",
                         des.name, m.arms, k, v, sols[0].b, pj.join(",")));
        }
        ("far", Some(des)) => {
            let arms: Vec<usize> = if a[3] == "-" { vec![] } else { a[3].split(',').map(|s| s.parse().unwrap()).collect() };
            let k: usize = a[4].parse().unwrap();
            let iters: usize = a[5].parse().unwrap();
            let chains: usize = a[6].parse().unwrap();
            let seed: u64 = a.get(7).map(|s| s.parse().unwrap()).unwrap_or(1);
            let m = Model { arms, k };
            let r = anneal_far(&des, &m, iters, chains, 0.3, 1e-6, seed);
            let v = r[0].0;
            let hits = r.iter().filter(|x| x.0 > v - 1e-6).count();
            println!("{} far-leg limit in {} iters={} chains={}  time {:.1}s", des.name, m.label(), iters, chains, t.elapsed().as_secs_f64());
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6})  S = {:b}  hit by {}/{}", v, v / des.total_weight(), des.flat_value(), r[0].2, hits, chains);
            let q: Vec<String> = r.iter().take(10).map(|s| format!("{:.4}", s.0)).collect();
            println!("top chains: {:?}", q);
            let pj: Vec<String> = r[0]
                .1
                .iter()
                .map(|p| format!("{{\"arm\":{:?},\"t\":{:?},\"x\":{:?}}}", &p.arm[..m.arms.len()], &p.t[..m.arms.len()], &p.x[..m.k]))
                .collect();
            save(&format!("far_{}_{}_k{}_s{}", des.name, m.arms.iter().map(|x| x.to_string()).collect::<Vec<_>>().join("-"), k, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"far\",\"arms\":{:?},\"k\":{},\"value\":{},\"S\":{},\"hubs\":[{}]}}",
                         des.name, m.arms, k, v, r[0].2, pj.join(",")));
        }
        ("tree", Some(des)) => {
            // tree DESIGN NF NV K ITERS CHAINS [SEED] [START.json (far pod JSON)]
            let nf: usize = a[3].parse().unwrap();
            let nv: usize = a[4].parse().unwrap();
            let k: usize = a[5].parse().unwrap();
            let iters: usize = a[6].parse().unwrap();
            let chains: usize = a[7].parse().unwrap();
            let seed: u64 = a.get(8).map(|s| s.parse().unwrap()).unwrap_or(1);
            let start = a.get(9).map(|path| load_pod_start(path, nf, nv, k));
            let r = anneal_far_tree(&des, nf, nv, k, iters, chains, 0.3, 1e-6, seed, start);
            let v = r[0].0;
            let hits = r.iter().filter(|x| x.0 > v - 1e-6).count();
            println!("{} far-leg, {} general trees ({} vertices) x R^{} iters={} chains={}  time {:.1}s", des.name, nf, nv, k, iters, chains, t.elapsed().as_secs_f64());
            println!("BEST value = {:.6}  rho = {:.6}  (flat {:.6})  S = {:b}  hit by {}/{}", v, v / des.total_weight(), des.flat_value(), r[0].2, hits, chains);
            let q: Vec<String> = r.iter().take(10).map(|s| format!("{:.4}", s.0)).collect();
            println!("top chains: {:?}", q);
            let tm = &r[0].1;
            let fj: Vec<String> = tm.factors.iter().map(|f| format!("{{\"parent\":{:?},\"len\":{:?},\"hv\":{:?}}}", f.parent, f.len, f.hv)).collect();
            save(&format!("tree_{}_f{}_n{}_k{}_s{}", des.name, nf, nv, k, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"fartree\",\"k\":{},\"value\":{},\"S\":{},\"factors\":[{}],\"x\":{:?}}}",
                         des.name, k, v, r[0].2, fj.join(","), tm.x));
        }
        ("onetree", Some(des)) => {
            // onetree DESIGN NV ITERS CHAINS [SEED] [sym|gamma]
            let nv: usize = a[3].parse().unwrap();
            let iters: usize = a[4].parse().unwrap();
            let chains: usize = a[5].parse().unwrap();
            let seed: u64 = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(1);
            let sym = a.get(7).map(|s| s == "sym").unwrap_or(false);
            let orb = edge_orbits(&des);
            let no = orb.iter().max().unwrap() + 1;
            let sizes: Vec<usize> = (0..no).map(|o| orb.iter().filter(|&&x| x == o).count()).filter(|&c| c > 0).collect();
            let starts: Vec<TreeFactor> = if std::env::var("PF_NOSTART").is_ok() { vec![] } else { (0..des.nnodes).map(|v| node_pod(&des, v)).collect() };
            let pod0 = node_pod(&des, 0);
            let mut c = vec![];
            let (g0, s0, cs0) = one_tree_scores(&des, &pod0, &orb, &mut c);
            let r = anneal_one_tree(&des, nv, iters, chains, 0.05, 1e-6, seed, sym, &starts);
            let e = des.total_weight();
            println!("{} one tree, {} vertices, target {}, iters={} chains={}  time {:.1}s  edge orbits {:?}", des.name, nv, if sym { "sym" } else { "gamma" }, iters, chains, t.elapsed().as_secs_f64(), sizes);
            println!("node-pod start: Gamma {:.6}  sym value {:.6} (rho {:.6})  CS bound {:.6} (rho {:.6})", g0, s0, s0 / e, cs0, cs0 / e);
            println!("BEST: Gamma {:.6}  sym value {:.6} (rho {:.6})  CS bound {:.6} (rho {:.6})   flat {:.6} (rho {:.6})  cap E/sqrt2 {:.6}",
                     r[0].0, r[0].1, r[0].1 / e, r[0].2, r[0].2 / e, des.flat_value(), des.flat_value() / e, e / 2f64.sqrt());
            let q: Vec<String> = r.iter().take(16).map(|x| format!("{:.4}/{:.4}", x.0, x.1)).collect();
            println!("top chains (Gamma/sym): {:?}", q);
            let f = &r[0].3;
            println!("tree: parent {:?}\n      len {:?}\n      hub vertex {:?}", f.parent, f.len.iter().map(|x| (x * 1e4).round() / 1e4).collect::<Vec<_>>(), f.hv);
            save(&format!("onetree_{}_n{}_{}_s{}", des.name, nv, if sym { "sym" } else { "gamma" }, seed),
                 format!("{{\"design\":\"{}\",\"space\":\"onetree\",\"gamma\":{},\"sym\":{},\"cs\":{},\"parent\":{:?},\"len\":{:?},\"hv\":{:?}}}",
                         des.name, r[0].0, r[0].1, r[0].2, f.parent, f.len, f.hv));
        }
        _ => {
            println!("usage: see the header of examples/piecefloor.rs");
        }
    }
    eprintln!("elapsed {:.2}s", t.elapsed().as_secs_f64());
}
