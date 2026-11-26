//! Exact search for XOR-AND circuits (multiplicative complexity) computing a set of
//! Boolean functions on n <= 8 inputs.  See README.md for the model and the proof of
//! correctness of every reduction used here.
//!
//! A function on n inputs is its truth table: a 256-bit vector (bit p = value at the input
//! whose k-th coordinate is bit k of p).  A circuit state is the F2-subspace
//!     S = span{1, x_1..x_n, g_1..g_j}
//! of truth tables.  A gate adds the product u*v of two elements of S.
//! The search is exhaustive; failed states are memoised by an exact canonical key
//! (the reduced row-echelon basis of S modulo the affine functions), no hashing shortcuts.

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

type V = [u64; 4];
const Z: V = [0; 4];

#[inline]
fn vx(a: &V, b: &V) -> V {
    [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]]
}
#[inline]
fn vxa(a: &mut V, b: &V) {
    a[0] ^= b[0];
    a[1] ^= b[1];
    a[2] ^= b[2];
    a[3] ^= b[3];
}
#[inline]
fn vand(a: &V, b: &V) -> V {
    [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]]
}
#[inline]
fn iz(a: &V) -> bool {
    (a[0] | a[1] | a[2] | a[3]) == 0
}
#[inline]
fn bit(a: &V, p: usize) -> bool {
    (a[p >> 6] >> (p & 63)) & 1 == 1
}
#[inline]
fn low(a: &V) -> usize {
    for i in 0..4 {
        if a[i] != 0 {
            return i * 64 + a[i].trailing_zeros() as usize;
        }
    }
    256
}

/// Fully reduced echelon basis (pivot = lowest set bit; every basis vector is zero at the
/// pivots of all other basis vectors).  Each vector carries a tag that is XORed along.
#[derive(Clone)]
struct Ech {
    v: Vec<V>,
    piv: Vec<usize>,
    tag: Vec<u64>,
}
impl Ech {
    fn new() -> Self {
        Ech { v: vec![], piv: vec![], tag: vec![] }
    }
    #[inline]
    fn reduce(&self, mut w: V, mut t: u64) -> (V, u64) {
        for i in 0..self.v.len() {
            if bit(&w, self.piv[i]) {
                vxa(&mut w, &self.v[i]);
                t ^= self.tag[i];
            }
        }
        (w, t)
    }
    /// insert; returns false if w is already in the span
    fn insert(&mut self, w: V, t: u64) -> bool {
        let (w, t) = self.reduce(w, t);
        if iz(&w) {
            return false;
        }
        let p = low(&w);
        for i in 0..self.v.len() {
            if bit(&self.v[i], p) {
                vxa(&mut self.v[i], &w);
                self.tag[i] ^= t;
            }
        }
        self.v.push(w);
        self.piv.push(p);
        self.tag.push(t);
        true
    }
    fn dim(&self) -> usize {
        self.v.len()
    }
}

// ---------------------------------------------------------------- problems
fn var(k: usize) -> V {
    let mut r = Z;
    for p in 0..256 {
        if (p >> k) & 1 == 1 {
            r[p >> 6] |= 1 << (p & 63);
        }
    }
    r
}
fn one(n: usize) -> V {
    let mut r = Z;
    for p in 0..(1usize << n) {
        r[p >> 6] |= 1 << (p & 63);
    }
    r
}
/// truth table (restricted to the 2^n points) of a sum of products x_i x_j
fn quad(n: usize, terms: &[(usize, usize)]) -> V {
    let mut r = Z;
    for &(i, j) in terms {
        vxa(&mut r, &vand(&var(i), &var(j)));
    }
    vand(&r, &one(n))
}

struct Problem {
    name: String,
    n: usize,
    targets: Vec<V>,
    tnames: Vec<String>,
    /// generators of a symmetry group, as linear maps on F2^n given by column images
    sym: Vec<Vec<u8>>,
}

fn mat2_mul(a: [[u8; 2]; 2], b: [[u8; 2]; 2]) -> [[u8; 2]; 2] {
    let mut c = [[0u8; 2]; 2];
    for i in 0..2 {
        for j in 0..2 {
            for k in 0..2 {
                c[i][j] ^= a[i][k] & b[k][j];
            }
        }
    }
    c
}
fn mat2_inv(a: [[u8; 2]; 2]) -> [[u8; 2]; 2] {
    // over F2 an invertible 2x2 matrix has det 1, inverse = adjugate
    let r = [[a[1][1], a[0][1]], [a[1][0], a[0][0]]];
    assert_eq!(mat2_mul(a, r), [[1, 0], [0, 1]]);
    r
}

fn problem(name: &str) -> Problem {
    match name {
        "mm222" => {
            // inputs: a11 a12 a21 a22 b11 b12 b21 b22 = x0..x7 ; a(i,k)=2i+k, b(k,j)=4+2k+j
            let a = |i: usize, k: usize| 2 * i + k;
            let b = |k: usize, j: usize| 4 + 2 * k + j;
            let mut targets = vec![];
            let mut tnames = vec![];
            for i in 0..2 {
                for j in 0..2 {
                    let terms: Vec<_> = (0..2).map(|k| (a(i, k), b(k, j))).collect();
                    targets.push(quad(8, &terms));
                    tnames.push(format!("c{}{}", i + 1, j + 1));
                }
            }
            // symmetry generators: (A,B) -> (P A Q^-1, Q B R^-1), and (A,B) -> (B^T, A^T)
            let s: [[u8; 2]; 2] = [[0, 1], [1, 0]];
            let t: [[u8; 2]; 2] = [[1, 1], [0, 1]];
            let id: [[u8; 2]; 2] = [[1, 0], [0, 1]];
            let to_mats = |x: u8| {
                let mut am = [[0u8; 2]; 2];
                let mut bm = [[0u8; 2]; 2];
                for i in 0..2 {
                    for k in 0..2 {
                        am[i][k] = (x >> a(i, k)) & 1;
                        bm[i][k] = (x >> b(i, k)) & 1;
                    }
                }
                (am, bm)
            };
            let from_mats = |am: [[u8; 2]; 2], bm: [[u8; 2]; 2]| {
                let mut x = 0u8;
                for i in 0..2 {
                    for k in 0..2 {
                        x |= am[i][k] << a(i, k);
                        x |= bm[i][k] << b(i, k);
                    }
                }
                x
            };
            let mut sym = vec![];
            let mut pqr = vec![];
            for g in [s, t] {
                pqr.push((g, id, id));
                pqr.push((id, g, id));
                pqr.push((id, id, g));
            }
            for (p, q, r) in pqr {
                let cols: Vec<u8> = (0..8)
                    .map(|k| {
                        let (am, bm) = to_mats(1u8 << k);
                        let a2 = mat2_mul(mat2_mul(p, am), mat2_inv(q));
                        let b2 = mat2_mul(mat2_mul(q, bm), mat2_inv(r));
                        from_mats(a2, b2)
                    })
                    .collect();
                sym.push(cols);
            }
            let cols: Vec<u8> = (0..8)
                .map(|k| {
                    let (am, bm) = to_mats(1u8 << k);
                    let tr = |m: [[u8; 2]; 2]| [[m[0][0], m[1][0]], [m[0][1], m[1][1]]];
                    from_mats(tr(bm), tr(am))
                })
                .collect();
            sym.push(cols);
            Problem { name: name.into(), n: 8, targets, tnames, sym }
        }
        "mm221" => {
            // A 2x2 (x0..x3, a(i,k)=2i+k), b 2x1 (x4,x5); c_i = sum_k a_ik b_k
            let mut targets = vec![];
            let mut tnames = vec![];
            for i in 0..2 {
                let terms: Vec<_> = (0..2).map(|k| (2 * i + k, 4 + k)).collect();
                targets.push(quad(6, &terms));
                tnames.push(format!("c{}", i + 1));
            }
            Problem { name: name.into(), n: 6, targets, tnames, sym: vec![] }
        }
        "polymul2" | "polymul3" => {
            let t = if name == "polymul2" { 2 } else { 3 };
            let n = 2 * t;
            let mut targets = vec![];
            let mut tnames = vec![];
            for s in 0..(2 * t - 1) {
                let mut terms = vec![];
                for i in 0..t {
                    if s >= i && s - i < t {
                        terms.push((i, t + s - i));
                    }
                }
                targets.push(quad(n, &terms));
                tnames.push(format!("c{}", s));
            }
            Problem { name: name.into(), n, targets, tnames, sym: vec![] }
        }
        "f4" => {
            // (a0 + a1 w)(b0 + b1 w), w^2 = w + 1; inputs a0 a1 b0 b1
            let targets = vec![quad(4, &[(0, 2), (1, 3)]), quad(4, &[(0, 3), (1, 2), (1, 3)])];
            Problem { name: name.into(), n: 4, targets, tnames: vec!["c0".into(), "c1".into()], sym: vec![] }
        }
        _ => panic!("unknown problem {name}"),
    }
}

/// f o M as a truth table, M given by column images
fn compose(f: &V, cols: &[u8], n: usize) -> V {
    let mut r = Z;
    for p in 0..(1usize << n) {
        let mut q = 0usize;
        for k in 0..n {
            if (p >> k) & 1 == 1 {
                q ^= cols[k] as usize;
            }
        }
        if bit(f, q) {
            r[p >> 6] |= 1 << (p & 63);
        }
    }
    r
}

fn affine_basis(n: usize) -> Vec<V> {
    let mut g = vec![one(n)];
    for k in 0..n {
        g.push(vand(&var(k), &one(n)));
    }
    g
}

/// Check that every generator M is invertible and maps span(A+T) onto itself under f -> f o M.
fn check_symmetry(pr: &Problem) {
    let mut e = Ech::new();
    for g in affine_basis(pr.n).iter().chain(pr.targets.iter()) {
        e.insert(*g, 0);
    }
    for cols in &pr.sym {
        // invertible
        let mut img: HashSet<usize> = HashSet::new();
        for x in 0..(1usize << pr.n) {
            let mut q = 0usize;
            for k in 0..pr.n {
                if (x >> k) & 1 == 1 {
                    q ^= cols[k] as usize;
                }
            }
            img.insert(q);
        }
        assert_eq!(img.len(), 1 << pr.n, "symmetry not invertible");
        for t in &pr.targets {
            let (r, _) = e.reduce(compose(t, cols, pr.n), 0);
            assert!(iz(&r), "symmetry does not preserve span(A+T)");
        }
    }
}

/// Planes (2-dim subspaces) of linear forms on F2^n, canonical rep (a,b) with a<b<a^b.
fn canon_plane(a: u8, b: u8) -> (u8, u8) {
    let mut t = [a, b, a ^ b];
    t.sort();
    (t[0], t[1])
}
/// Orbit representatives of planes under lambda -> M^T lambda for the generators.
fn plane_orbits(pr: &Problem) -> Vec<((u8, u8), usize)> {
    let n = pr.n;
    let lim = 1u16 << n;
    let mut all = vec![];
    for a in 1..lim {
        for b in (a + 1)..lim {
            if (a ^ b) > b {
                all.push((a as u8, b as u8));
            }
        }
    }
    let tr = |cols: &Vec<u8>, l: u8| -> u8 {
        let mut r = 0u8;
        for k in 0..n {
            if (l & cols[k]).count_ones() & 1 == 1 {
                r |= 1 << k;
            }
        }
        r
    };
    let mut seen: HashSet<(u8, u8)> = HashSet::new();
    let mut reps = vec![];
    for &p in &all {
        if seen.contains(&p) {
            continue;
        }
        let mut stack = vec![p];
        seen.insert(p);
        let mut size = 0;
        while let Some(q) = stack.pop() {
            size += 1;
            for cols in &pr.sym {
                let r = canon_plane(tr(cols, q.0), tr(cols, q.1));
                if seen.insert(r) {
                    stack.push(r);
                }
            }
        }
        reps.push((p, size));
    }
    assert_eq!(reps.iter().map(|r| r.1).sum::<usize>(), all.len());
    reps
}

// ---------------------------------------------------------------- search
struct Stats {
    states: u64,
    helpers: u64,
}

struct Ctx<'a> {
    pr: &'a Problem,
    k: usize,
    ea: Ech,
    memo: HashSet<Vec<V>>,
    st: Stats,
    stop: &'a AtomicBool,
}

impl<'a> Ctx<'a> {
    /// canonical key of S = span(gens): fully reduced echelon basis of S modulo A
    fn canon(&self, gens: &[V]) -> Vec<V> {
        let mut e = Ech::new();
        for g in &gens[self.pr.n + 1..] {
            let (r, _) = self.ea.reduce(*g, 0);
            e.insert(r, 0);
        }
        let mut idx: Vec<usize> = (0..e.dim()).collect();
        idx.sort_by_key(|&i| e.piv[i]);
        idx.iter().map(|&i| e.v[i]).collect()
    }

    /// All classes t in ((S+T)/S) \ {0} such that some product u*v (u,v in S) lies in S + t.
    /// Returns (class tag, u mask, v mask) with masks over gens indices.
    fn reducer_classes(&self, gens: &[V], est: &Ech, rem: usize) -> Vec<(u64, u64, u64)> {
        let m = gens.len() - 1;
        // P[j][i] = reduce_{S+T}(g_{j+1} * g_{i+1})  (residual, class tag)
        let mut p: Vec<Vec<(V, u64)>> = vec![vec![(Z, 0); m]; m];
        for j in 0..m {
            for i in 0..m {
                p[j][i] = est.reduce(vand(&gens[1 + j], &gens[1 + i]), 0);
            }
        }
        let full = (1u64 << rem) - 1;
        let mut reached: Vec<Option<(u64, u64)>> = vec![None; 1 << rem];
        let mut cnt = 0u64;
        let mut rows: Vec<(V, u64)> = vec![(Z, 0); m];
        let mut u = 0u64;
        let mut lv = [Z; 16];
        let mut lp = [0usize; 16];
        let mut lt = [0u64; 16];
        let mut lm = [0u64; 16];
        for s in 1u64..(1u64 << m) {
            let j = s.trailing_zeros() as usize;
            u ^= 1 << j;
            for i in 0..m {
                vxa(&mut rows[i].0, &p[j][i].0);
                rows[i].1 ^= p[j][i].1;
            }
            // kernel of v -> u*v mod (S+T), recording class tags
            let mut c = 0usize;
            let mut kt: Vec<(u64, u64)> = vec![]; // (tag, vmask), tags independent
            for i in 0..m {
                let (mut w, mut t) = rows[i];
                let mut mask = 1u64 << i;
                for l in 0..c {
                    if bit(&w, lp[l]) {
                        vxa(&mut w, &lv[l]);
                        t ^= lt[l];
                        mask ^= lm[l];
                    }
                }
                if iz(&w) {
                    // reduce tag against previously found kernel tags (pivot = lowest bit)
                    for &(kt0, km) in &kt {
                        let pv = kt0.trailing_zeros();
                        if (t >> pv) & 1 == 1 {
                            t ^= kt0;
                            mask ^= km;
                        }
                    }
                    if t != 0 {
                        kt.push((t, mask));
                    }
                } else {
                    lv[c] = w;
                    lp[c] = low(&w);
                    lt[c] = t;
                    lm[c] = mask;
                    c += 1;
                }
            }
            if !kt.is_empty() {
                for comb in 1u64..(1u64 << kt.len()) {
                    let mut t = 0;
                    let mut vm = 0;
                    for (b, &(kt0, km)) in kt.iter().enumerate() {
                        if (comb >> b) & 1 == 1 {
                            t ^= kt0;
                            vm ^= km;
                        }
                    }
                    if reached[t as usize].is_none() {
                        reached[t as usize] = Some((u << 1, vm << 1));
                        cnt += 1;
                    }
                }
                if cnt == full {
                    break;
                }
            }
        }
        (1..=full)
            .filter_map(|t| reached[t as usize].map(|(a, b)| (t, a, b)))
            .collect()
    }

    /// All products u*v (u,v in S) with u*v not in S+T, one witness per distinct space S+<u*v>.
    fn helper_successors(&self, gens: &[V], es: &Ech, est: &Ech) -> Vec<(u64, u64)> {
        let m = gens.len() - 1;
        let mut q: Vec<Vec<V>> = vec![vec![Z; m]; m];
        for j in 0..m {
            for i in 0..m {
                q[j][i] = es.reduce(vand(&gens[1 + j], &gens[1 + i]), 0).0;
            }
        }
        let mut found: HashMap<V, (u64, u64)> = HashMap::new();
        let mut ru: Vec<V> = vec![Z; m];
        let mut rv: Vec<V> = vec![Z; 1 << m];
        let mut u = 0u64;
        for s in 1u64..(1u64 << m) {
            let j = s.trailing_zeros() as usize;
            u ^= 1 << j;
            for i in 0..m {
                vxa(&mut ru[i], &q[j][i]);
            }
            for v in 1usize..(1usize << m) {
                let lb = v.trailing_zeros() as usize;
                rv[v] = vx(&rv[v & (v - 1)], &ru[lb]);
            }
            for v in (u as usize + 1)..(1usize << m) {
                if (u as usize ^ v) <= v {
                    continue;
                }
                let r = rv[v];
                if iz(&r) {
                    continue;
                }
                if found.contains_key(&r) {
                    continue;
                }
                let (r2, _) = est.reduce(r, 0);
                if iz(&r2) {
                    continue; // lands in S+T: a reducer, handled separately
                }
                found.insert(r, (u << 1, (v as u64) << 1));
            }
        }
        let mut out: Vec<(V, (u64, u64))> = found.into_iter().collect();
        out.sort();
        out.into_iter().map(|x| x.1).collect()
    }

    fn comb(gens: &[V], mask: u64) -> V {
        let mut r = Z;
        for (i, g) in gens.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                vxa(&mut r, g);
            }
        }
        r
    }

    /// Depth-first search.  gens = [1, x_1..x_n, g_1..g_j]; gates[i] = (u mask, v mask).
    fn dfs(&mut self, gens: &mut Vec<V>, gates: &mut Vec<(u64, u64)>) -> bool {
        if self.stop.load(Ordering::Relaxed) {
            return false;
        }
        let b = self.k - gates.len();
        let mut es = Ech::new();
        for (i, g) in gens.iter().enumerate() {
            assert!(es.insert(*g, 1 << i), "dependent generator");
        }
        let mut est = Ech::new();
        for g in gens.iter() {
            est.insert(*g, 0);
        }
        let mut rem = 0usize;
        for t in &self.pr.targets {
            if est.insert(*t, 1 << rem) {
                rem += 1;
            }
        }
        if rem == 0 {
            return true;
        }
        if rem > b {
            return false;
        }
        let key = self.canon(gens);
        if self.memo.contains(&key) {
            return false;
        }
        self.st.states += 1;
        // reducers
        for (_t, um, vm) in self.reducer_classes(gens, &est, rem) {
            let g = vand(&Self::comb(gens, um), &Self::comb(gens, vm));
            gens.push(g);
            gates.push((um, vm));
            if self.dfs(gens, gates) {
                return true;
            }
            gens.pop();
            gates.pop();
        }
        // helpers (gates that do not reduce rem) are useful only if rem < b
        if rem < b {
            let hs = self.helper_successors(gens, &es, &est);
            self.st.helpers += hs.len() as u64;
            for (um, vm) in hs {
                let g = vand(&Self::comb(gens, um), &Self::comb(gens, vm));
                gens.push(g);
                gates.push((um, vm));
                if self.dfs(gens, gates) {
                    return true;
                }
                gens.pop();
                gates.pop();
            }
        }
        if self.memo.len() > 4_000_000 {
            self.memo.clear(); // memo is only a cache of failed states; clearing is sound
        }
        self.memo.insert(key);
        false
    }
}

fn write_circuit(pr: &Problem, gens: &[V], gates: &[(u64, u64)], path: &str) {
    let mut es = Ech::new();
    for (i, g) in gens.iter().enumerate() {
        es.insert(*g, 1 << i);
    }
    let lst = |m: u64| -> String {
        (0..64).filter(|i| (m >> i) & 1 == 1).map(|i| i.to_string()).collect::<Vec<_>>().join(" ")
    };
    let mut s = String::new();
    s += &format!("# problem {} n={} ands={}\n", pr.name, pr.n, gates.len());
    s += "# generator indices: 0 = constant 1, 1..n = inputs x0..x(n-1), n+1+i = gate i\n";
    for (u, v) in gates {
        s += &format!("G {} | {}\n", lst(*u), lst(*v));
    }
    for (t, nm) in pr.targets.iter().zip(&pr.tnames) {
        let (r, m) = es.reduce(*t, 0);
        assert!(iz(&r));
        s += &format!("O {} {}\n", nm, lst(m));
    }
    std::fs::write(path, &s).unwrap();
    print!("{}", s);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: mc222 <problem> <k> [--no-orbits] [--threads N] [--roots a:b] [--out file]");
        std::process::exit(2);
    }
    let pr = problem(&args[1]);
    let k: usize = args[2].parse().unwrap();
    let mut orbits = !pr.sym.is_empty();
    let mut threads = 4usize;
    let mut range: Option<(usize, usize)> = None;
    let mut out = format!("circuit_{}_{}.txt", pr.name, k);
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--no-orbits" => orbits = false,
            "--threads" => {
                threads = args[i + 1].parse().unwrap();
                i += 1
            }
            "--roots" => {
                let v: Vec<usize> = args[i + 1].split(':').map(|x| x.parse().unwrap()).collect();
                range = Some((v[0], v[1]));
                i += 1
            }
            "--out" => {
                out = args[i + 1].clone();
                i += 1
            }
            a => panic!("bad arg {a}"),
        }
        i += 1;
    }
    let n = pr.n;
    // sanity: targets are independent modulo A
    {
        let mut e = Ech::new();
        for g in affine_basis(n) {
            e.insert(g, 0);
        }
        for t in &pr.targets {
            assert!(e.insert(*t, 0), "targets dependent mod affine");
        }
    }
    // roots: first gates (every circuit's first gate is a product of two linear forms)
    let roots: Vec<((u8, u8), usize)> = if orbits {
        check_symmetry(&pr);
        let r = plane_orbits(&pr);
        println!("# symmetry check passed; {} plane orbits, sizes {:?}", r.len(), {
            let mut s: Vec<usize> = r.iter().map(|x| x.1).collect();
            s.sort();
            s
        });
        r
    } else {
        let lim = 1u16 << n;
        let mut all = vec![];
        for a in 1..lim {
            for b in (a + 1)..lim {
                if (a ^ b) > b {
                    all.push(((a as u8, b as u8), 1));
                }
            }
        }
        all
    };
    let (lo, hi) = range.unwrap_or((0, roots.len()));
    let hi = hi.min(roots.len());
    println!("# problem {} n={} k={} orbits={} roots {}..{} of {}", pr.name, n, k, orbits, lo, hi, roots.len());
    let next = AtomicUsize::new(lo);
    let stop = AtomicBool::new(false);
    let results: Mutex<Vec<(usize, bool, u64, u64, f64)>> = Mutex::new(vec![]);
    let t0 = Instant::now();
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut ea = Ech::new();
                for g in affine_basis(n) {
                    ea.insert(g, 0);
                }
                let mut ctx = Ctx { pr: &pr, k, ea, memo: HashSet::new(), st: Stats { states: 0, helpers: 0 }, stop: &stop };
                loop {
                    let r = next.fetch_add(1, Ordering::SeqCst);
                    if r >= hi || stop.load(Ordering::Relaxed) {
                        break;
                    }
                    let ((a, b), _) = roots[r];
                    let mut gens = affine_basis(n);
                    let lf = |l: u8| {
                        let mut v = Z;
                        for kk in 0..n {
                            if (l >> kk) & 1 == 1 {
                                vxa(&mut v, &gens[1 + kk]);
                            }
                        }
                        v
                    };
                    let g = vand(&lf(a), &lf(b));
                    gens.push(g);
                    let mut gates = vec![((a as u64) << 1, (b as u64) << 1)];
                    let s0 = ctx.st.states;
                    let h0 = ctx.st.helpers;
                    let t1 = Instant::now();
                    let f = ctx.dfs(&mut gens, &mut gates);
                    let dt = t1.elapsed().as_secs_f64();
                    if f {
                        stop.store(true, Ordering::SeqCst);
                        println!("FOUND circuit with {} ANDs (root {})", gates.len(), r);
                        write_circuit(&pr, &gens, &gates, &out);
                    }
                    let line = format!(
                        "root {} plane ({},{}) {} states {} helpers {} time {:.2}s",
                        r,
                        a,
                        b,
                        if f { "FOUND" } else { "none" },
                        ctx.st.states - s0,
                        ctx.st.helpers - h0,
                        dt
                    );
                    println!("{}", line);
                    std::io::stdout().flush().unwrap();
                    results.lock().unwrap().push((r, f, ctx.st.states - s0, ctx.st.helpers - h0, dt));
                }
            });
        }
    });
    let res = results.into_inner().unwrap();
    let found = res.iter().any(|r| r.1);
    let done = res.len();
    println!(
        "# SUMMARY problem {} k={} roots done {}/{} found={} states={} wall={:.1}s",
        pr.name,
        k,
        done,
        hi - lo,
        found,
        res.iter().map(|r| r.2).sum::<u64>(),
        t0.elapsed().as_secs_f64()
    );
    if !found && done == hi - lo {
        println!("# RESULT: no circuit with <= {} AND gates for roots {}..{}", k, lo, hi);
    }
}
