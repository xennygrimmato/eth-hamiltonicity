//! Finite (pseudo)metrics stored as distance vectors, the inequality families used for
//! CAT(0)-type tests, cut-cone (l1) membership, and constructors.
//!
//! Distances are stored for pairs i<j in lexicographic order: (0,1),(0,2),...,(0,n-1),(1,2),...
//! so `pair_index(n,i,j)` is the position of d(i,j).

use nalgebra::{DMatrix, SymmetricEigen};

#[inline]
pub fn npairs(n: usize) -> usize {
    n * (n - 1) / 2
}

/// Index of the unordered pair {i,j} (i != j) in the distance vector of an n-point metric.
#[inline]
pub fn pair_index(n: usize, i: usize, j: usize) -> usize {
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    debug_assert!(a != b && b < n);
    a * (2 * n - a - 1) / 2 + (b - a - 1)
}

/// All pairs in storage order.
pub fn pairs(n: usize) -> Vec<(usize, usize)> {
    let mut v = Vec::with_capacity(npairs(n));
    for i in 0..n {
        for j in i + 1..n {
            v.push((i, j));
        }
    }
    v
}

#[derive(Clone, Debug)]
pub struct Metric {
    pub n: usize,
    pub d: Vec<f64>,
}

impl Metric {
    pub fn new(n: usize, d: Vec<f64>) -> Self {
        assert_eq!(d.len(), npairs(n), "distance vector has wrong length");
        Metric { n, d }
    }
    pub fn zeros(n: usize) -> Self {
        Metric { n, d: vec![0.0; npairs(n)] }
    }
    #[inline]
    pub fn get(&self, i: usize, j: usize) -> f64 {
        if i == j {
            0.0
        } else {
            self.d[pair_index(self.n, i, j)]
        }
    }
    #[inline]
    pub fn set(&mut self, i: usize, j: usize, v: f64) {
        let k = pair_index(self.n, i, j);
        self.d[k] = v;
    }
    pub fn from_fn(n: usize, f: impl Fn(usize, usize) -> f64) -> Self {
        let d = pairs(n).into_iter().map(|(i, j)| f(i, j)).collect();
        Metric { n, d }
    }
    /// Full symmetric distance matrix.
    pub fn matrix(&self) -> DMatrix<f64> {
        DMatrix::from_fn(self.n, self.n, |i, j| self.get(i, j))
    }
    /// Restrict to a subset of points (in the given order).
    pub fn sub(&self, pts: &[usize]) -> Metric {
        Metric::from_fn(pts.len(), |i, j| self.get(pts[i], pts[j]))
    }
    pub fn scale(&self, c: f64) -> Metric {
        Metric { n: self.n, d: self.d.iter().map(|x| x * c).collect() }
    }

    // ------------------------------------------------------------------ constructors
    /// Euclidean metric of points given as rows.
    pub fn euclidean(points: &[Vec<f64>]) -> Metric {
        let n = points.len();
        Metric::from_fn(n, |i, j| {
            points[i].iter().zip(&points[j]).map(|(a, b)| (a - b) * (a - b)).sum::<f64>().sqrt()
        })
    }
    /// Shortest-path metric of a weighted graph on `nv` vertices restricted to `pts`.
    pub fn graph_metric(nv: usize, edges: &[(usize, usize, f64)], pts: &[usize]) -> Metric {
        let dist = all_pairs_shortest(nv, edges);
        Metric::from_fn(pts.len(), |i, j| dist[pts[i]][pts[j]])
    }
    /// l2 product of metrics on the same index set: d = sqrt(sum_t d_t^2).
    pub fn l2_product(ms: &[Metric]) -> Metric {
        let n = ms[0].n;
        let mut d = vec![0.0; npairs(n)];
        for m in ms {
            assert_eq!(m.n, n);
            for (a, b) in d.iter_mut().zip(&m.d) {
                *a += b * b;
            }
        }
        Metric { n, d: d.into_iter().map(f64::sqrt).collect() }
    }
    /// l1 sum of metrics.
    pub fn l1_sum(ms: &[Metric]) -> Metric {
        let n = ms[0].n;
        let mut d = vec![0.0; npairs(n)];
        for m in ms {
            for (a, b) in d.iter_mut().zip(&m.d) {
                *a += b;
            }
        }
        Metric { n, d }
    }
    /// Cut (semi)metric of a subset given as a bitmask.
    pub fn cut(n: usize, mask: u64) -> Metric {
        Metric::from_fn(n, |i, j| if ((mask >> i) & 1) != ((mask >> j) & 1) { 1.0 } else { 0.0 })
    }
    /// sqrt(rank(a-b)) on Mat_mu(F_2), all 2^(mu^2) matrices (mu <= 3 recommended: 512 points).
    /// Point index = bit pattern of the matrix, row r occupies bits r*mu .. r*mu+mu-1.
    pub fn sqrt_rank_f2(mu: usize) -> Metric {
        assert!(mu * mu <= 16, "mu too large");
        let n = 1usize << (mu * mu);
        Metric::from_fn(n, |a, b| (rank_f2_matrix((a ^ b) as u64, mu) as f64).sqrt())
    }

    // ------------------------------------------------------------------ checks
    /// Largest violation of a triangle inequality d(i,k) <= d(i,j)+d(j,k) (<= 0 means all hold).
    pub fn max_triangle_violation(&self) -> f64 {
        let mut worst = f64::NEG_INFINITY;
        let n = self.n;
        for i in 0..n {
            for k in i + 1..n {
                for j in 0..n {
                    if j != i && j != k {
                        worst = worst.max(self.get(i, k) - self.get(i, j) - self.get(j, k));
                    }
                }
            }
        }
        if n < 3 { 0.0 } else { worst }
    }
    /// Largest value of a constraint from `family` (<= 0 means all hold) and the constraint.
    pub fn max_violation(&self, family: &[Constraint]) -> (f64, Option<Constraint>) {
        let mut worst = f64::NEG_INFINITY;
        let mut arg = None;
        for c in family {
            let v = c.value(&self.d);
            if v > worst {
                worst = v;
                arg = Some(c.clone());
            }
        }
        (worst, arg)
    }
    /// Largest eigenvalue of the centred matrix -1/2 J D^2 J ... i.e. returns the minimal eigenvalue
    /// of the Gram matrix at point 0. The metric is Euclidean iff this is >= 0 (up to tolerance).
    pub fn euclidean_gram_min_eig(&self) -> f64 {
        let n = self.n;
        if n <= 2 {
            return 0.0;
        }
        let g = DMatrix::from_fn(n - 1, n - 1, |a, b| {
            let (i, j) = (a + 1, b + 1);
            0.5 * (self.get(0, i).powi(2) + self.get(0, j).powi(2) - self.get(i, j).powi(2))
        });
        let e = SymmetricEigen::new(g);
        e.eigenvalues.iter().cloned().fold(f64::INFINITY, f64::min)
    }
    /// Largest value of sum_{i<j} b_i b_j d_ij over the pentagonal / hypermetric vectors b with
    /// entries in {-1,0,1,...} given; here: all b with sum b = 1 and entries in {-1,0,1} (triangle and
    /// pentagonal inequalities, plus the 7-gonal ones for n>=7). <= 0 means all hold.
    pub fn max_hypermetric_violation(&self, max_support: usize) -> (f64, Vec<i32>) {
        let n = self.n;
        let mut worst = f64::NEG_INFINITY;
        let mut arg = vec![];
        let mut b = vec![0i32; n];
        // enumerate 3^n vectors
        let total = 3usize.pow(n as u32);
        for code in 0..total {
            let mut c = code;
            let mut s = 0;
            let mut supp = 0;
            for x in b.iter_mut() {
                *x = (c % 3) as i32 - 1;
                c /= 3;
                s += *x;
                if *x != 0 {
                    supp += 1;
                }
            }
            if s != 1 || supp < 3 || supp > max_support {
                continue;
            }
            let mut v = 0.0;
            for i in 0..n {
                for j in i + 1..n {
                    v += (b[i] * b[j]) as f64 * self.get(i, j);
                }
            }
            if v > worst {
                worst = v;
                arg = b.clone();
            }
        }
        (worst, arg)
    }
    /// Cut-cone membership by nonnegative least squares over all 2^(n-1)-1 cut metrics.
    /// Returns (relative residual, coefficients by mask). Residual ~ 1e-12 means l1-embeddable.
    pub fn l1_nnls(&self) -> (f64, Vec<(u64, f64)>) {
        let n = self.n;
        assert!(n <= 12);
        let masks: Vec<u64> = (1..(1u64 << (n - 1))).collect();
        let a = DMatrix::from_fn(npairs(n), masks.len(), |r, c| Metric::cut(n, masks[c]).d[r]);
        let b = nalgebra::DVector::from_vec(self.d.clone());
        let x = nnls(&a, &b, 1e-13, 2000);
        let res = (&a * &x - &b).norm() / b.norm().max(1e-300);
        let coef = masks.iter().zip(x.iter()).filter(|(_, v)| **v > 1e-12).map(|(m, v)| (*m, *v)).collect();
        (res, coef)
    }
    /// Minimum over cuts of ratio <w_num,delta_S>/<w_den,delta_S> (cuts with zero denominator skipped).
    pub fn min_cut_ratio(n: usize, w_num: &[f64], w_den: &[f64]) -> (f64, u64) {
        let mut best = (f64::INFINITY, 0);
        for m in 1..(1u64 << (n - 1)) {
            let c = Metric::cut(n, m);
            let num: f64 = c.d.iter().zip(w_num).map(|(a, b)| a * b).sum();
            let den: f64 = c.d.iter().zip(w_den).map(|(a, b)| a * b).sum();
            if den > 0.0 && num / den < best.0 {
                best = (num / den, m);
            }
        }
        best
    }
    pub fn ratio(&self, w_num: &[f64], w_den: &[f64]) -> f64 {
        let num: f64 = self.d.iter().zip(w_num).map(|(a, b)| a * b).sum();
        let den: f64 = self.d.iter().zip(w_den).map(|(a, b)| a * b).sum();
        num / den
    }
}

/// Rank over F_2 of a mu x mu matrix packed row-major in the low mu*mu bits.
pub fn rank_f2_matrix(bits: u64, mu: usize) -> usize {
    let mask = (1u64 << mu) - 1;
    let mut rows: Vec<u64> = (0..mu).map(|r| (bits >> (r * mu)) & mask).collect();
    rank_f2_rows(&mut rows)
}

/// Rank over F_2 of a list of bit rows (destroys input).
pub fn rank_f2_rows(rows: &mut [u64]) -> usize {
    let mut rank = 0;
    for bit in 0..64 {
        let piv = (rank..rows.len()).find(|&r| (rows[r] >> bit) & 1 == 1);
        if let Some(p) = piv {
            rows.swap(rank, p);
            let pr = rows[rank];
            for r in 0..rows.len() {
                if r != rank && (rows[r] >> bit) & 1 == 1 {
                    rows[r] ^= pr;
                }
            }
            rank += 1;
            if rank == rows.len() {
                break;
            }
        }
    }
    rank
}

pub fn all_pairs_shortest(nv: usize, edges: &[(usize, usize, f64)]) -> Vec<Vec<f64>> {
    let mut d = vec![vec![f64::INFINITY; nv]; nv];
    for i in 0..nv {
        d[i][i] = 0.0;
    }
    for &(a, b, w) in edges {
        if w < d[a][b] {
            d[a][b] = w;
            d[b][a] = w;
        }
    }
    for k in 0..nv {
        for i in 0..nv {
            for j in 0..nv {
                let v = d[i][k] + d[k][j];
                if v < d[i][j] {
                    d[i][j] = v;
                }
            }
        }
    }
    d
}

/// Lawson-Hanson nonnegative least squares min ||Ax-b||, x>=0.
pub fn nnls(a: &DMatrix<f64>, b: &nalgebra::DVector<f64>, tol: f64, max_iter: usize) -> nalgebra::DVector<f64> {
    let (_m, n) = a.shape();
    let mut x = nalgebra::DVector::zeros(n);
    let mut passive = vec![false; n];
    for _ in 0..max_iter {
        let w = a.transpose() * (b - a * &x);
        let mut best = None;
        for j in 0..n {
            if !passive[j] && w[j] > tol {
                if best.map_or(true, |(_, v)| w[j] > v) {
                    best = Some((j, w[j]));
                }
            }
        }
        let Some((j, _)) = best else { break };
        passive[j] = true;
        loop {
            let idx: Vec<usize> = (0..n).filter(|&k| passive[k]).collect();
            let ap = DMatrix::from_fn(a.nrows(), idx.len(), |r, c| a[(r, idx[c])]);
            let z = ap.clone().svd(true, true).solve(b, 1e-14).unwrap();
            if z.iter().all(|&v| v > tol) {
                x.fill(0.0);
                for (c, &k) in idx.iter().enumerate() {
                    x[k] = z[c];
                }
                break;
            }
            let mut alpha = f64::INFINITY;
            for (c, &k) in idx.iter().enumerate() {
                if z[c] <= tol {
                    let den = x[k] - z[c];
                    if den > 0.0 {
                        alpha = alpha.min(x[k] / den);
                    }
                }
            }
            if !alpha.is_finite() {
                alpha = 0.0;
            }
            for (c, &k) in idx.iter().enumerate() {
                x[k] += alpha * (z[c] - x[k]);
            }
            for &k in &idx {
                if x[k] <= tol {
                    passive[k] = false;
                    x[k] = 0.0;
                }
            }
        }
    }
    x
}

// ---------------------------------------------------------------------- constraints

/// A constraint g(d) <= 0 on the distance vector.
#[derive(Clone, Debug, PartialEq)]
pub enum Constraint {
    /// d[a] - d[b] - d[c] <= 0  (a = long side)
    Triangle { a: usize, b: usize, c: usize },
    /// Euler / Enflo roundness-2 quadrilateral inequality:
    /// d[p0]^2 + d[p1]^2 - (d[s0]^2+d[s1]^2+d[s2]^2+d[s3]^2) <= 0 (diagonals p, sides s).
    Euler { diag: [usize; 2], sides: [usize; 4] },
    /// Reshetnyak quadruple comparison (AN Lemma C.4(b)) for points x,y,u,v:
    /// |xv|^2+|yu|^2 - |xu|^2 - |yv|^2 - 2|xy||uv| <= 0.
    Reshetnyak { plus: [usize; 2], minus: [usize; 2], prod: [usize; 2] },
    /// Linear: sum coef_k d[k] <= 0.
    Linear { coef: Vec<(usize, f64)> },
    /// Gromov-Sturm weighted quadruple ("box") inequalities for the cyclic order x,y,z,w, all
    /// t,s in [0,1] at once: g = -min_{t,s} Q(t,s) <= 0 with
    /// Q = (1-t)(1-s)|xy|^2 + t(1-s)|yz|^2 + ts|zw|^2 + (1-t)s|wx|^2 - t(1-t)|xz|^2 - s(1-s)|yw|^2.
    /// p = pair indices of [xy, yz, zw, wx, xz, yw]. (Toyoda 2020: for <= 5 points these, over
    /// all quadruples, characterise subsets of CAT(0) spaces.)
    BoxQ { p: [usize; 6] },
}

/// Exact minimum of the box quadratic over [0,1]^2 given squared distances
/// q = [xy, yz, zw, wx, xz, yw]^2. Returns (t, s, Q_min).
pub fn box_min(q: &[f64; 6]) -> (f64, f64, f64) {
    let [a, b, c, d, e, f] = *q;
    let qf = |t: f64, s: f64| {
        (1.0 - t) * (1.0 - s) * a + t * (1.0 - s) * b + t * s * c + (1.0 - t) * s * d - t * (1.0 - t) * e
            - s * (1.0 - s) * f
    };
    // Q = a + t(-a+b-e) + s(-a+d-f) + ts(a-b+c-d) + e t^2 + f s^2
    let (lt, ls, m) = (-a + b - e, -a + d - f, a - b + c - d);
    let mut best = (0.0, 0.0, qf(0.0, 0.0));
    let mut consider = |t: f64, s: f64| {
        if (0.0..=1.0).contains(&t) && (0.0..=1.0).contains(&s) {
            let v = qf(t, s);
            if v < best.2 {
                best = (t, s, v);
            }
        }
    };
    for &(t, s) in &[(1.0, 0.0), (0.0, 1.0), (1.0, 1.0)] {
        consider(t, s);
    }
    // edges: t fixed in {0,1}: quadratic in s: f s^2 + (ls + m t) s ; s fixed: e t^2 + (lt + m s) t
    for &t in &[0.0, 1.0] {
        if f > 0.0 {
            consider(t, -(ls + m * t) / (2.0 * f));
        }
    }
    for &s in &[0.0, 1.0] {
        if e > 0.0 {
            consider(-(lt + m * s) / (2.0 * e), s);
        }
    }
    // interior: [2e m; m 2f][t;s] = [-lt;-ls]
    let det = 4.0 * e * f - m * m;
    if det.abs() > 1e-300 {
        let t = (-lt * 2.0 * f + ls * m) / det;
        let s = (-ls * 2.0 * e + lt * m) / det;
        consider(t, s);
    }
    best
}

/// Coefficients of the squared distances [xy,yz,zw,wx,xz,yw] in Q(t,s).
pub fn box_coef(t: f64, s: f64) -> [f64; 6] {
    [(1.0 - t) * (1.0 - s), t * (1.0 - s), t * s, (1.0 - t) * s, -t * (1.0 - t), -s * (1.0 - s)]
}

impl Constraint {
    pub fn value(&self, d: &[f64]) -> f64 {
        match self {
            Constraint::Triangle { a, b, c } => d[*a] - d[*b] - d[*c],
            Constraint::Euler { diag, sides } => {
                diag.iter().map(|&k| d[k] * d[k]).sum::<f64>() - sides.iter().map(|&k| d[k] * d[k]).sum::<f64>()
            }
            Constraint::Reshetnyak { plus, minus, prod } => {
                d[plus[0]].powi(2) + d[plus[1]].powi(2) - d[minus[0]].powi(2) - d[minus[1]].powi(2)
                    - 2.0 * d[prod[0]] * d[prod[1]]
            }
            Constraint::Linear { coef } => coef.iter().map(|(k, c)| c * d[*k]).sum(),
            Constraint::BoxQ { p } => {
                let q = [d[p[0]].powi(2), d[p[1]].powi(2), d[p[2]].powi(2), d[p[3]].powi(2), d[p[4]].powi(2), d[p[5]].powi(2)];
                -box_min(&q).2
            }
        }
    }
    /// Gradient added into `g` scaled by `s`.
    pub fn add_grad(&self, d: &[f64], s: f64, g: &mut [f64]) {
        match self {
            Constraint::Triangle { a, b, c } => {
                g[*a] += s;
                g[*b] -= s;
                g[*c] -= s;
            }
            Constraint::Euler { diag, sides } => {
                for &k in diag {
                    g[k] += 2.0 * s * d[k];
                }
                for &k in sides {
                    g[k] -= 2.0 * s * d[k];
                }
            }
            Constraint::Reshetnyak { plus, minus, prod } => {
                for &k in plus {
                    g[k] += 2.0 * s * d[k];
                }
                for &k in minus {
                    g[k] -= 2.0 * s * d[k];
                }
                g[prod[0]] -= 2.0 * s * d[prod[1]];
                g[prod[1]] -= 2.0 * s * d[prod[0]];
            }
            Constraint::Linear { coef } => {
                for (k, c) in coef {
                    g[*k] += s * c;
                }
            }
            Constraint::BoxQ { p } => {
                // Danskin: gradient of -Q at the minimiser
                let q = [d[p[0]].powi(2), d[p[1]].powi(2), d[p[2]].powi(2), d[p[3]].powi(2), d[p[4]].powi(2), d[p[5]].powi(2)];
                let (t, u, _) = box_min(&q);
                let c = box_coef(t, u);
                for k in 0..6 {
                    g[p[k]] -= s * c[k] * 2.0 * d[p[k]];
                }
            }
        }
    }
    /// Degree of homogeneity (1 or 2).
    pub fn degree(&self) -> i32 {
        match self {
            Constraint::Triangle { .. } | Constraint::Linear { .. } => 1,
            _ => 2,
        }
    }
    pub fn describe(&self, n: usize, names: &[String]) -> String {
        let pr = pairs(n);
        let nm = |k: usize| {
            let (i, j) = pr[k];
            format!("{}{}", names[i], names[j])
        };
        match self {
            Constraint::Triangle { a, b, c } => format!("tri: {} <= {} + {}", nm(*a), nm(*b), nm(*c)),
            Constraint::Euler { diag, sides } => format!(
                "euler: {}^2+{}^2 <= {}^2+{}^2+{}^2+{}^2",
                nm(diag[0]), nm(diag[1]), nm(sides[0]), nm(sides[1]), nm(sides[2]), nm(sides[3])
            ),
            Constraint::Reshetnyak { plus, minus, prod } => format!(
                "resh: {}^2+{}^2 <= {}^2+{}^2+2*{}*{}",
                nm(plus[0]), nm(plus[1]), nm(minus[0]), nm(minus[1]), nm(prod[0]), nm(prod[1])
            ),
            Constraint::BoxQ { p } => format!(
                "box: cycle {}-{}-{}-{} (diagonals {},{})",
                nm(p[0]), nm(p[1]), nm(p[2]), nm(p[3]), nm(p[4]), nm(p[5])
            ),
            Constraint::Linear { coef } => {
                let terms: Vec<String> = coef.iter().map(|(k, c)| format!("{:+}*{}", c, nm(*k))).collect();
                format!("lin: {} <= 0", terms.join(" "))
            }
        }
    }
}

/// All triangle inequalities on n points (3 per triple).
pub fn triangle_family(n: usize) -> Vec<Constraint> {
    let mut v = vec![];
    for i in 0..n {
        for j in i + 1..n {
            for k in j + 1..n {
                let (ij, jk, ik) = (pair_index(n, i, j), pair_index(n, j, k), pair_index(n, i, k));
                v.push(Constraint::Triangle { a: ik, b: ij, c: jk });
                v.push(Constraint::Triangle { a: ij, b: ik, c: jk });
                v.push(Constraint::Triangle { a: jk, b: ij, c: ik });
            }
        }
    }
    v
}

/// Euler quadrilateral inequalities: 3 cyclic orders per 4-set.
pub fn euler_family(n: usize) -> Vec<Constraint> {
    let mut v = vec![];
    let p = |i, j| pair_index(n, i, j);
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                for e in c + 1..n {
                    for (x, y, z, w) in [(a, b, c, e), (a, b, e, c), (a, c, b, e)] {
                        // cycle x-y-z-w-x, diagonals xz, yw
                        v.push(Constraint::Euler { diag: [p(x, z), p(y, w)], sides: [p(x, y), p(y, z), p(z, w), p(w, x)] });
                    }
                }
            }
        }
    }
    v
}

/// Box (weighted quadruple) inequalities: 3 cyclic orders per 4-set (the family is invariant under
/// the dihedral symmetries of the cycle with (t,s) relabelled).
pub fn box_family(n: usize) -> Vec<Constraint> {
    let mut v = vec![];
    let p = |i, j| pair_index(n, i, j);
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                for e in c + 1..n {
                    for (x, y, z, w) in [(a, b, c, e), (a, b, e, c), (a, c, b, e)] {
                        v.push(Constraint::BoxQ { p: [p(x, y), p(y, z), p(z, w), p(w, x), p(x, z), p(y, w)] });
                    }
                }
            }
        }
    }
    v
}

/// Box inequalities for all 24 orderings of each 4-set (redundant; for checking).
pub fn box_family_all_orders(n: usize) -> Vec<Constraint> {
    let mut v = vec![];
    let p = |i, j| pair_index(n, i, j);
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                for e in c + 1..n {
                    let q = [a, b, c, e];
                    for pm in permutations4() {
                        let (x, y, z, w) = (q[pm[0]], q[pm[1]], q[pm[2]], q[pm[3]]);
                        v.push(Constraint::BoxQ { p: [p(x, y), p(y, z), p(z, w), p(w, x), p(x, z), p(y, w)] });
                    }
                }
            }
        }
    }
    v
}

/// Reshetnyak quadruple inequalities |xv|^2+|yu|^2 <= |xu|^2+|yv|^2+2|xy||uv| for all ordered
/// quadruples of distinct points, deduplicated (6 per 4-set).
pub fn reshetnyak_family(n: usize) -> Vec<Constraint> {
    let mut v: Vec<Constraint> = vec![];
    let p = |i, j| pair_index(n, i, j);
    let sort2 = |a: usize, b: usize| if a < b { [a, b] } else { [b, a] };
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                for e in c + 1..n {
                    let q = [a, b, c, e];
                    for perm in permutations4() {
                        let (x, y, u, w) = (q[perm[0]], q[perm[1]], q[perm[2]], q[perm[3]]);
                        let con = Constraint::Reshetnyak {
                            plus: sort2(p(x, w), p(y, u)),
                            minus: sort2(p(x, u), p(y, w)),
                            prod: sort2(p(x, y), p(u, w)),
                        };
                        if !v.contains(&con) {
                            v.push(con);
                        }
                    }
                }
            }
        }
    }
    v
}

fn permutations4() -> Vec<[usize; 4]> {
    let mut out = vec![];
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for d in 0..4 {
                    if a != b && a != c && a != d && b != c && b != d && c != d {
                        out.push([a, b, c, d]);
                    }
                }
            }
        }
    }
    out
}

/// Weight vector on pairs from a list of (i, j, w).
pub fn weights(n: usize, list: &[(usize, usize, f64)]) -> Vec<f64> {
    let mut w = vec![0.0; npairs(n)];
    for &(i, j, x) in list {
        w[pair_index(n, i, j)] += x;
    }
    w
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn index_roundtrip() {
        let n = 6;
        for (k, (i, j)) in pairs(n).into_iter().enumerate() {
            assert_eq!(pair_index(n, i, j), k);
            assert_eq!(pair_index(n, j, i), k);
        }
    }
    #[test]
    fn families_sizes() {
        assert_eq!(triangle_family(5).len(), 30);
        assert_eq!(euler_family(5).len(), 15);
        assert_eq!(reshetnyak_family(5).len(), 30);
    }
    #[test]
    fn euclidean_satisfies_all() {
        let pts = vec![vec![0.0, 0.0], vec![1.0, 0.3], vec![0.2, 2.0], vec![-1.0, 0.5], vec![0.7, -0.8]];
        let m = Metric::euclidean(&pts);
        assert!(m.max_triangle_violation() <= 1e-12);
        assert!(m.max_violation(&euler_family(5)).0 <= 1e-12);
        assert!(m.max_violation(&reshetnyak_family(5)).0 <= 1e-12);
        assert!(m.euclidean_gram_min_eig() > -1e-12);
    }
    #[test]
    fn box_examples() {
        // Toyoda Example 1.2: satisfies the quadrilateral inequality but not the box inequality.
        let r3 = 3f64.sqrt();
        let m = Metric::new(4, vec![1.0, r3, r3, 1.0, r3, 1.0]); // 01,02,03,12,13,23
        assert!(m.max_violation(&euler_family(4)).0 <= 1e-12);
        assert!(m.max_violation(&box_family(4)).0 > 1e-6);
        let pts = vec![vec![0.0, 0.0], vec![1.0, 0.3], vec![0.2, 2.0], vec![-1.0, 0.5], vec![0.7, -0.8]];
        let e = Metric::euclidean(&pts);
        assert!(e.max_violation(&box_family_all_orders(5)).0 <= 1e-12);
        // brute-force grid agrees with exact minimiser
        let q = [1.0, 2.0, 0.5, 3.0, 2.5, 1.7];
        let (_, _, v) = box_min(&q);
        let mut g = f64::INFINITY;
        for i in 0..=400 { for j in 0..=400 { let (t, s) = (i as f64 / 400.0, j as f64 / 400.0);
            let c = box_coef(t, s); g = g.min((0..6).map(|k| c[k] * q[k]).sum()); } }
        assert!(v <= g + 1e-12 && g - v < 1e-4);
    }
    #[test]
    fn rank_f2() {
        assert_eq!(rank_f2_matrix(0b1001, 2), 2);
        assert_eq!(rank_f2_matrix(0b1111, 2), 1);
        assert_eq!(rank_f2_matrix(0, 2), 0);
        let m = Metric::sqrt_rank_f2(2);
        assert_eq!(m.n, 16);
        assert!(m.max_triangle_violation() <= 1e-12);
    }
    #[test]
    fn cuts_are_l1() {
        let m = Metric::l1_sum(&[Metric::cut(5, 0b00011).scale(2.0), Metric::cut(5, 0b00101)]);
        let (res, _) = m.l1_nnls();
        assert!(res < 1e-10);
        assert!(m.max_hypermetric_violation(5).0 <= 1e-12);
    }
}
