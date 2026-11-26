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

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let cmd = a.get(1).map(|s| s.as_str()).unwrap_or("help");
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
        _ => {
            println!("usage: see the header of examples/piecefloor.rs");
        }
    }
    eprintln!("elapsed {:.2}s", t.elapsed().as_secs_f64());
}
