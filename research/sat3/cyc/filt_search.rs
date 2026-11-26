// filt_search.rs -- one-factor ratio Gamma of a design in Cone(spherical building of GL_N(F_2)).
//
// Build:  rustc -O -C target-cpu=native filt_search.rs -o filt_search
// Usage:  filt_search DESIGN N MAXSTEPS ITERS CHAINS SEED [T0] [T1]
//         filt_search check                (self tests)
//   DESIGN = delta3 | x4 ; N = 2..5 ; MAXSTEPS = number of steps of the leg flags (N-1 = exact).
//
// Model (research/sat3/q1-notes.md section 1, with the R-factor removed).
//   A point of Cone(Delta) is  h = sum_l g_l (1_{V_l} - (dim V_l/N) 1),  V_1 < V_2 < ... a chain, g_l >= 0.
//   <h,h'> = sum g_l g'_m (dim(V_l ^ V'_m) - dim V_l dim V'_m / N)   (common adapted basis).
//   A leg pair is a pair of opposite weighted flags: d = sum_{j in J} tau_j (1_{U+_j} - (j/N) 1), tau_j > 0,
//   U+_j of dimension j increasing, U-_j of dimension N-j a complement of U+_j, decreasing.
//   Far-leg saving of an edge (n,n') summed over the merges:
//       sum_j tau_j sigma_j / |d|,   sigma_j = sum_{h in n} B_h(U+_j) + sum_{h' in n'} B_h'(U-_j),
//       B_h(U) = sum_l g_l (dim(V_l ^ U) - dim V_l dim U / N),
//       |d|^2 = tau^T M tau,  M_jj' = min(j,j') - j j'/N.
//   c_e = max over flag pairs and tau.   Gamma = sum_e c_e^2 / Dbar,  Dbar = mean same-class |h-h'|^2.
//   Every value printed is a valid LOWER bound for Gamma of the space (restricted legs only lower it).
//   For Delta_3: value per merge = sqrt(Gamma)/9 * ... : Gamma = 36 <-> 2/3, Gamma = 40.5 <-> 1/sqrt2, 27 <-> flat.

use std::collections::HashMap;
use std::env;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12; self.0 ^= self.0 << 25; self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize { (self.next() % (n as u64)) as usize }
    fn unif(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 }
    fn gauss(&mut self) -> f64 {
        let u = self.unif().max(1e-300); let v = self.unif();
        (-2.0 * u.ln()).sqrt() * (2.0 * std::f64::consts::PI * v).cos()
    }
}

fn span_add(mask: u64, v: usize) -> u64 {
    let mut m = mask; let mut r = mask;
    while m != 0 { let u = m.trailing_zeros() as usize; m &= m - 1; r |= 1u64 << (u ^ v); }
    r
}

struct Space {
    n: usize,
    subs: Vec<u64>,
    dim: Vec<usize>,
    index: HashMap<u64, usize>,
    dimint: Vec<u8>, // S x S
    bydim: Vec<Vec<usize>>,
}

impl Space {
    fn new(n: usize) -> Space {
        let nv = 1usize << n;
        let mut subs = vec![1u64];
        let mut index = HashMap::new();
        index.insert(1u64, 0usize);
        let mut i = 0;
        while i < subs.len() {
            let m = subs[i];
            for v in 1..nv {
                if m >> v & 1 == 0 {
                    let s = span_add(m, v);
                    if !index.contains_key(&s) { index.insert(s, subs.len()); subs.push(s); }
                }
            }
            i += 1;
        }
        let dim: Vec<usize> = subs.iter().map(|m| m.count_ones().trailing_zeros() as usize).collect();
        let s = subs.len();
        let mut dimint = vec![0u8; s * s];
        for a in 0..s { for b in 0..s {
            dimint[a * s + b] = (subs[a] & subs[b]).count_ones().trailing_zeros() as u8;
        } }
        let mut bydim = vec![Vec::new(); n + 1];
        for a in 0..s { bydim[dim[a]].push(a); }
        Space { n, subs, dim, index, dimint, bydim }
    }
    fn di(&self, a: usize, b: usize) -> usize { self.dimint[a * self.subs.len() + b] as usize }
}

// Leg records grouped by type J (bitmask over j = 1..N-1)
struct LegType { js: Vec<usize>, minv: Vec<f64>, up: Vec<u16>, um: Vec<u16>, cnt: usize }

fn invert(a: &Vec<Vec<f64>>) -> Vec<Vec<f64>> {
    let n = a.len();
    let mut m: Vec<Vec<f64>> = (0..n).map(|i| { let mut r = a[i].clone(); for j in 0..n { r.push(if i == j {1.0} else {0.0}); } r }).collect();
    for c in 0..n {
        let mut p = c; for r in c..n { if m[r][c].abs() > m[p][c].abs() { p = r; } }
        m.swap(c, p);
        let d = m[c][c]; for j in 0..2 * n { m[c][j] /= d; }
        for r in 0..n { if r != c { let f = m[r][c]; if f != 0.0 { for j in 0..2 * n { m[r][j] -= f * m[c][j]; } } } }
    }
    m.iter().map(|r| r[n..].to_vec()).collect()
}

fn build_legs(sp: &Space, maxsteps: usize) -> Vec<LegType> {
    let n = sp.n; let nv = 1usize << n;
    let mut types: Vec<LegType> = Vec::new();
    let mut sets: Vec<HashMap<Vec<u16>, ()>> = Vec::new();
    let mut tmask: Vec<usize> = Vec::new();
    for jm in 1usize..(1 << (n - 1)) {
        if (jm.count_ones() as usize) > maxsteps { continue; }
        let js: Vec<usize> = (1..n).filter(|j| jm >> (j - 1) & 1 == 1).collect();
        let a: Vec<Vec<f64>> = js.iter().map(|&j| js.iter().map(|&k| (j.min(k) as f64) - (j * k) as f64 / n as f64).collect()).collect();
        let minv: Vec<f64> = invert(&a).into_iter().flatten().collect();
        types.push(LegType { js, minv, up: Vec::new(), um: Vec::new(), cnt: 0 });
        sets.push(HashMap::new()); tmask.push(jm);
    }
    // enumerate ordered bases
    let mut basis = vec![0usize; n];
    let mut spans = vec![1u64; n + 1];
    fn rec(k: usize, n: usize, nv: usize, basis: &mut Vec<usize>, spans: &mut Vec<u64>, sp: &Space,
           types: &mut Vec<LegType>, sets: &mut Vec<HashMap<Vec<u16>, ()>>) {
        if k == n {
            // U+_j = span(first j) = spans[j];  U-_j = span(last n-j)
            let mut um = vec![1u64; n + 1];
            let mut m = 1u64;
            for j in (1..n).rev() { m = span_add(m, basis[j]); um[j] = m; }
            for (t, ty) in types.iter_mut().enumerate() {
                let mut key: Vec<u16> = Vec::with_capacity(2 * ty.js.len());
                for &j in &ty.js { key.push(sp.index[&spans[j]] as u16); }
                for &j in &ty.js { key.push(sp.index[&um[j]] as u16); }
                if !sets[t].contains_key(&key) {
                    let l = ty.js.len();
                    ty.up.extend_from_slice(&key[..l]); ty.um.extend_from_slice(&key[l..]); ty.cnt += 1;
                    sets[t].insert(key, ());
                }
            }
            return;
        }
        for v in 1..nv {
            if spans[k] >> v & 1 == 1 { continue; }
            basis[k] = v; spans[k + 1] = span_add(spans[k], v);
            rec(k + 1, n, nv, basis, spans, sp, types, sets);
        }
    }
    rec(0, n, nv, &mut basis, &mut spans, sp, &mut types, &mut sets);
    types
}

struct Design { nh: usize, nodes: Vec<Vec<usize>>, edges: Vec<(usize, usize)>, pairs: Vec<(usize, usize)>, name: String }

fn delta3() -> Design {
    // hubs (u,v) -> 3u+v ; nodes (t,i) = {(u, i+t u)} ; edges ((t,i),(t,i+1))
    let mut nodes = Vec::new();
    for t in 0..3 { for i in 0..3 { nodes.push((0..3).map(|u| 3 * u + (i + t * u) % 3).collect()); } }
    let mut edges = Vec::new();
    for t in 0..3 { for i in 0..3 { edges.push((3 * t + i, 3 * t + (i + 1) % 3)); } }
    let mut pairs = Vec::new();
    for u in 0..3 { for v in 0..3 { for w in (v + 1)..3 { pairs.push((3 * u + v, 3 * u + w)); } } }
    Design { nh: 9, nodes, edges, pairs, name: "delta3".into() }
}

fn x4() -> Design {
    // nodes (r,c) in (F_2^2)^2 ; classes r, c, r+c ; hubs 4 per class ; edges: r-r', c-c' independent (generic)
    let mut nodes = Vec::new();
    for r in 0..4 { for c in 0..4 { nodes.push(vec![r, 4 + c, 8 + (r ^ c)]); } }
    let mut edges = Vec::new();
    for a in 0..16 { for b in (a + 1)..16 {
        let (r, c, r2, c2) = (a / 4, a % 4, b / 4, b % 4);
        let (dr, dc) = (r ^ r2, c ^ c2);
        if dr != 0 && dc != 0 && dr != dc { edges.push((a, b)); }
    } }
    let mut pairs = Vec::new();
    for k in 0..3 { for v in 0..4 { for w in (v + 1)..4 { pairs.push((4 * k + v, 4 * k + w)); } } }
    Design { nh: 12, nodes, edges, pairs, name: "x4".into() }
}

#[derive(Clone)]
struct Hub { flag: Vec<usize>, g: Vec<f64> } // flag[l] = subspace of dim l+1, l = 0..N-2

struct Eval<'a> { sp: &'a Space, legs: &'a Vec<LegType>, des: &'a Design }

impl<'a> Eval<'a> {
    fn btable(&self, h: &Hub) -> Vec<f64> {
        let s = self.sp.subs.len(); let n = self.sp.n as f64;
        let mut b = vec![0.0; s];
        for (l, &v) in h.flag.iter().enumerate() {
            let g = h.g[l]; if g == 0.0 { continue; }
            let k = self.sp.dim[v] as f64;
            for u in 0..s { b[u] += g * (self.sp.di(v, u) as f64 - k * self.sp.dim[u] as f64 / n); }
        }
        b
    }
    fn inner(&self, a: &Hub, b: &Hub) -> f64 {
        let n = self.sp.n as f64; let mut r = 0.0;
        for (l, &v) in a.flag.iter().enumerate() { if a.g[l] == 0.0 { continue; }
            for (m, &w) in b.flag.iter().enumerate() { if b.g[m] == 0.0 { continue; }
                r += a.g[l] * b.g[m] * (self.sp.di(v, w) as f64 - (self.sp.dim[v] * self.sp.dim[w]) as f64 / n);
            } }
        r
    }
    fn dbar(&self, hubs: &Vec<Hub>) -> f64 {
        let mut d = 0.0;
        for &(a, b) in &self.des.pairs {
            d += self.inner(&hubs[a], &hubs[a]) + self.inner(&hubs[b], &hubs[b]) - 2.0 * self.inner(&hubs[a], &hubs[b]);
        }
        d / self.des.pairs.len() as f64
    }
    // best saving of edge (n, n'), squared; also returns the argmax (type, record)
    fn edge(&self, bt: &Vec<Vec<f64>>, e: usize) -> (f64, usize, usize) {
        let (a, b) = self.des.edges[e];
        let s = self.sp.subs.len();
        let mut fp = vec![0.0f64; s]; let mut fm = vec![0.0f64; s];
        for &h in &self.des.nodes[a] { for u in 0..s { fp[u] += bt[h][u]; } }
        for &h in &self.des.nodes[b] { for u in 0..s { fm[u] += bt[h][u]; } }
        let mut best = 0.0f64; let mut arg = (usize::MAX, 0usize);
        let mut sig = [0.0f64; 8];
        for (t, ty) in self.legs.iter().enumerate() {
            let l = ty.js.len();
            for r in 0..ty.cnt {
                let mut pos = true;
                for i in 0..l {
                    sig[i] = fp[ty.up[r * l + i] as usize] + fm[ty.um[r * l + i] as usize];
                }
                // tau = Minv sigma ; need tau >= 0 ; value^2 = sigma^T Minv sigma
                let mut val = 0.0;
                for i in 0..l {
                    let mut tau = 0.0;
                    for j in 0..l { tau += ty.minv[i * l + j] * sig[j]; }
                    if tau < 0.0 { pos = false; break; }
                    val += tau * sig[i];
                }
                if pos && val > best { best = val; arg = (t, r); }
            }
        }
        (best, arg.0, arg.1)
    }
    fn gamma(&self, hubs: &Vec<Hub>) -> f64 {
        let bt: Vec<Vec<f64>> = hubs.iter().map(|h| self.btable(h)).collect();
        let mut s = 0.0;
        for e in 0..self.des.edges.len() { s += self.edge(&bt, e).0; }
        let d = self.dbar(hubs);
        if d <= 1e-12 { 0.0 } else { s / d }
    }
}

fn random_flag(sp: &Space, rng: &mut Rng) -> Vec<usize> {
    // random complete flag via a random ordered basis
    let n = sp.n; let nv = 1usize << n;
    let mut m = 1u64; let mut f = Vec::new();
    for _ in 0..(n - 1) {
        loop { let v = 1 + rng.below(nv - 1); if m >> v & 1 == 0 { m = span_add(m, v); break; } }
        f.push(sp.index[&m]);
    }
    f
}

fn mutate(sp: &Space, h: &mut Hub, rng: &mut Rng) {
    let n = sp.n; let l = rng.below(n - 1);
    match rng.below(10) {
        0 => { h.flag = random_flag(sp, rng); }
        1 | 2 | 3 => {
            // replace V_l by another subspace between V_{l-1} and V_{l+1}
            let cand = &sp.bydim[l + 1];
            for _ in 0..2000 {
                let c = cand[rng.below(cand.len())];
                if c == h.flag[l] { continue; }
                if l > 0 && sp.di(c, h.flag[l - 1]) != l { continue; }
                if l + 1 < n - 1 && sp.di(c, h.flag[l + 1]) != l + 1 { continue; }
                h.flag[l] = c; break;
            }
        }
        4 => { h.g[l] = 0.0; }
        5 => { h.g[l] = rng.unif(); }
        6 => { for x in h.g.iter_mut() { *x = 0.0; } h.g[l] = 1.0; }
        _ => { if h.g[l] > 0.0 { h.g[l] *= (0.25 * rng.gauss()).exp(); } else if rng.below(3) == 0 { h.g[l] = 0.3 * rng.unif(); } }
    }
}

fn describe(sp: &Space, hubs: &Vec<Hub>) -> String {
    let mut s = String::new();
    for (i, h) in hubs.iter().enumerate() {
        s += &format!("  hub {:2}:", i);
        for (l, &v) in h.flag.iter().enumerate() {
            if h.g[l] > 0.0 {
                // basis of the subspace: list of all nonzero vectors (compact for small N)
                let mut vs = Vec::new(); let mut m = sp.subs[v] & !1;
                while m != 0 { vs.push(m.trailing_zeros()); m &= m - 1; }
                s += &format!(" g={:.5} dim{} {:?}", h.g[l], l + 1, vs);
            }
        }
        s += "\n";
    }
    s
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() >= 2 && args[1] == "check" { selftest(); return; }
    let des = match args[1].as_str() { "delta3" => delta3(), "x4" => x4(), _ => panic!("design") };
    let n: usize = args[2].parse().unwrap();
    let maxsteps: usize = args[3].parse().unwrap();
    let iters: usize = args[4].parse().unwrap();
    let chains: usize = args[5].parse().unwrap();
    let seed: u64 = args[6].parse().unwrap();
    let t0: f64 = if args.len() > 7 { args[7].parse().unwrap() } else { 1.0 };
    let t1: f64 = if args.len() > 8 { args[8].parse().unwrap() } else { 0.01 };
    let sp = Space::new(n);
    let legs = build_legs(&sp, maxsteps);
    let nrec: usize = legs.iter().map(|t| t.cnt).sum();
    eprintln!("N={} subspaces={} leg records={} (maxsteps {})", n, sp.subs.len(), nrec, maxsteps);
    let exact = if maxsteps < n - 1 && n <= 4 { Some(build_legs(&sp, n - 1)) } else { None };
    let ev = Eval { sp: &sp, legs: &legs, des: &des };
    let ne = des.edges.len();
    let mut hub_edges: Vec<Vec<usize>> = vec![Vec::new(); des.nh];
    for (e, &(a, b)) in des.edges.iter().enumerate() {
        for &h in des.nodes[a].iter().chain(des.nodes[b].iter()) { if !hub_edges[h].contains(&e) { hub_edges[h].push(e); } }
    }
    let mut gbest = 0.0; let mut gbest_h: Vec<Hub> = Vec::new();
    for c in 0..chains {
        let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(c as u64 * 7919 + 1));
        for _ in 0..10 { rng.next(); }
        let mut hubs: Vec<Hub> = (0..des.nh).map(|_| {
            let mut g = vec![0.0; n - 1];
            if rng.below(2) == 0 { g[rng.below(n - 1)] = 1.0; }
            Hub { flag: random_flag(&sp, &mut rng), g }
        }).collect();
        let mut bt: Vec<Vec<f64>> = hubs.iter().map(|h| ev.btable(h)).collect();
        let mut es: Vec<f64> = (0..ne).map(|e| ev.edge(&bt, e).0).collect();
        let mut d = ev.dbar(&hubs);
        let mut cur = if d > 1e-12 { es.iter().sum::<f64>() / d } else { 0.0 };
        let mut best = cur; let mut best_h = hubs.clone();
        for it in 0..iters {
            let temp = t0 * (t1 / t0).powf(it as f64 / iters as f64);
            let h = rng.below(des.nh);
            let old = hubs[h].clone();
            mutate(&sp, &mut hubs[h], &mut rng);
            let oldbt = std::mem::replace(&mut bt[h], ev.btable(&hubs[h]));
            let nd = ev.dbar(&hubs);
            let mut nes = es.clone();
            for &e in &hub_edges[h] { nes[e] = ev.edge(&bt, e).0; }
            let new = if nd > 1e-12 { nes.iter().sum::<f64>() / nd } else { 0.0 };
            if new >= cur || rng.unif() < ((new - cur) / temp).exp() {
                cur = new; es = nes; d = nd;
                if cur > best { best = cur; best_h = hubs.clone(); }
            } else { hubs[h] = old; bt[h] = oldbt; }
        }
        let _ = d;
        let ex = match &exact { Some(l) => Eval { sp: &sp, legs: l, des: &des }.gamma(&best_h), None => best };
        println!("chain {} best Gamma = {:.6} (exact legs {:.6})", c, best, ex);
        if ex > gbest { gbest = ex; gbest_h = best_h.clone(); }
    }
    println!("{} N={} BEST Gamma = {:.6}", des.name, n, gbest);
    print!("{}", describe(&sp, &gbest_h));
}

fn selftest() {
    // 1. tripod atom in N = 2: Gamma = 36
    let sp = Space::new(2); let legs = build_legs(&sp, 1); let des = delta3();
    let ev = Eval { sp: &sp, legs: &legs, des: &des };
    let pts = &sp.bydim[1];
    let mut hubs: Vec<Hub> = (0..9).map(|_| Hub { flag: vec![pts[0]], g: vec![0.0] }).collect();
    for u in 0..3 { hubs[3 * u] = Hub { flag: vec![pts[u]], g: vec![1.0] }; }
    println!("tripod atom, N=2: Gamma = {:.6} (expect 36)", ev.gamma(&hubs));
    // 2. X4 in N = 4 with the placement of q1-notes 2.2: Gamma = 216
    let sp = Space::new(4); let des = x4();
    // V = F_2^2 + F_2^2 ; hub of class x (x in {(1,0),(0,1),(1,1)}) and value y in F_2^2: point <(x,y)>
    // vector index: bits 0,1 = z in F_2^2 ; bits 2,3 = F_2^m part
    let xs = [1usize, 2, 3];
    let mut hubs: Vec<Hub> = Vec::new();
    for k in 0..3 { for y in 0..4 {
        let v = xs[k] | (y << 2);
        let pt = sp.index[&span_add(1, v)];
        // complete the flag arbitrarily
        let mut f = vec![pt]; let mut m = sp.subs[pt];
        for _ in 0..2 { let mut w = 1; while m >> w & 1 == 1 { w += 1; } m = span_add(m, w); f.push(sp.index[&m]); }
        hubs.push(Hub { flag: f, g: vec![1.0, 0.0, 0.0] });
    } }
    // node a = (r,c): a(1,0) = r, a(0,1) = c, hubs: class (1,0) value r ; class (0,1) value c ; class (1,1) value r+c  -- as in x4()
    for ms in 1..4 {
        let legs = build_legs(&sp, ms);
        let ev = Eval { sp: &sp, legs: &legs, des: &des };
        println!("X4 placement, N=4, legs with <= {} steps ({} records): Gamma = {:.6} (expect 216)", ms,
                 legs.iter().map(|t| t.cnt).sum::<usize>(), ev.gamma(&hubs));
    }
}
