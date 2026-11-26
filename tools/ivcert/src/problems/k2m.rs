//! Refined bracket Br' of the K_{2,m} notes (research/ports/k2m/notes.md §5.2, §5.4, "Certificate spec"),
//! m = 3, on the hard region F'_1, for the statements S(9/10) and (CL**_0).
//!
//! Variables sigma = (s12, s13, s21, s23, s31, s32) in [-1,1]^6, c = sqrt(1 - sigma^2); parameters lambda,
//! tau = sqrt(1 - lambda^2), eta (given as exact rationals; tau^2 = (q^2 - p^2)/q^2 for lambda = p/q).
//! Vertices: 1 -> (s12, s13) = (x0, x1), 2 -> (s21, s23) = (x2, x3), 3 -> (s31, s32) = (x4, x5).
//! Pairs: eps12 = x0 + x2, eps13 = x1 + x4, eps23 = x3 + x5.
//! Spec (notes §5.4), for a vertex (u, v):  Q = u + v,  W = (c_u + c_v)^2 + Q^2,
//!   C(u,v) = 1/2 sqrt(tau^2 (c_u + c_v)^2 + (u - v)^2) + (lambda/2)|Q|,
//!   N(u,v) = 1 if 2|Q| >= lambda W, = C(u,v) otherwise;   C <= N everywhere.
//!   E = |eps12| + |eps13| + |eps23|,  X = |Q1| + |Q2| + |Q3| - E,
//!   Br' = N1 + N2 + N3 - (lambda/2) X - eta.
//! Region F'_1 = { Q1 <= 0, Q2 >= 0, Q3 >= 0, 2|Q1| <= lambda W1, 2 Q2 <= lambda W2 } in [-1,1]^6.
//!
//! Cover of F'_1 by closed pieces P(case, s), case in {c, l}, s in {+,-}^3:
//!   P(c, s) = F'_1 ∩ { 2 Q3 <= lambda W3 } ∩ { s_k eps_k >= 0, k = 12, 13, 23 },
//!   P(l, s) = F'_1 ∩ { 2 Q3 >= lambda W3 } ∩ { s_k eps_k >= 0 }.
//! (Every point has some sign pattern s with s_k eps_k >= 0, and lies in case c or case l.)
//! On a piece, |Q1| = -Q1, |Q2| = Q2, |Q3| = Q3, |eps_k| = s_k eps_k, N1 = C1, N2 = C2 (vertices 1, 2 curved),
//! and N3 >= C3 (case c) resp. N3 = 1 (case l). With V(u,v) := 1/2 sqrt(tau^2 (c_u+c_v)^2 + (u-v)^2), so that
//! C_i - (lambda/2)|Q_i| = V_i exactly, this gives on the piece
//!   case c:  Br' >= f := V1 + V2 + V3 + (lambda/2) sum_k s_k eps_k - eta          (equality where v3 curved)
//!   case l:  Br' =  f := V1 + V2 + 1 - (lambda/2) Q3 + (lambda/2) sum_k s_k eps_k - eta.
//! f is smooth wherever all c > 0 (no |.|, no case distinction).
//! Scaling: the function evaluated is f_M := M f with M = lcm(den lambda, den eta), so that every constant
//! is an exact float: M V(u,v) = 1/2 sqrt(A (c_u+c_v)^2 + B (u-v)^2), A = M^2 tau^2, B = M^2 (integers),
//! M lambda/2 and M eta exact (M = 10, A = 19, B = 100, M lam/2 = 9/2, M eta = 12 for S(9/10);
//! M = 13, A = 25, B = 169, M lam/2 = 6, M eta = 15 for (CL**_0), where f_M(0) = 3*5 - 15 = 0 exactly).
//! The claim certified is f_M >= bound (default 0) on the piece; boxes that certainly miss the piece (one
//! of its defining inequalities is violated at every point of the box, by interval evaluation of the
//! inequality as written above with an enclosure of lambda) are closed as X.
//!
//! `k2far:lam=P/Q:eta=P/Q:case=c|l:s=+-+[:rho=R][:c=B]` : sigma coordinates, domain [-1,1]^6. With rho = R > 0
//!   (R <= 1/2) boxes inside the central cube [-R,R]^6 are also X: covered by the eight `k2near` certificates.
//! `k2near:lam=P/Q:eta=P/Q:case=c:s=+-+:t=T[:c=B]` : coordinates x = (a12, a13, a23, t12, t13, t23),
//!   e_k = s_k t_k^2, sigma_ij = a_k + e_k, sigma_ji = e_k - a_k, on a in [-R,R]^3, t in [0,T]^3, R = T^2
//!   (exact, R <= 1/2, so sigma in [-1,1]). t -> s t^2 maps [0,T] onto s[0,R], so the eight boxes cover
//!   the (a,e)-image of [-R,R]^6 (|a_k|, |e_k| <= R there), as for `clnear`. Here s_k eps_k = 2 t_k^2 >= 0
//!   on the whole domain. The substitution e = s t^2 makes the kink of |eps| at the equality point 0 a
//!   smooth minimum: f_M(0) = 3 M tau - M eta (= 0 for (CL**_0)), grad f_M(0) = 0 exactly
//!   (d/dt_k = 2 s_k t_k d/de_k), Hessian block diag(Hess_a, 2 M lambda I) at 0, so the convexity test C
//!   with anchor 0 closes a neighbourhood of 0.
//! `c=B` overrides the bound (used for mutation tests only).
//! No symmetry pruning is used (the symmetries S3 x {±1} map the other hard regions onto F'_1 or its
//! image under the exchange of pages 2 and 3; see the notes and ivcert-notes.md).

use super::parse_name;
use crate::ad::Scalar;
use crate::bnb::{BoxN, Problem};
use crate::interval::I;

fn parse_rat(m: &std::collections::BTreeMap<String, String>, k: &str) -> Result<(i64, i64), String> {
    let v = m.get(k).ok_or(format!("missing {k}=P/Q"))?;
    let (p, q) = v.split_once('/').ok_or(format!("{k} must be P/Q"))?;
    let p: i64 = p.parse().map_err(|_| format!("bad {k}"))?;
    let q: i64 = q.parse().map_err(|_| format!("bad {k}"))?;
    if q <= 0 || p <= 0 || p.abs() > (1 << 26) || q > (1 << 26) {
        return Err(format!("bad {k}"));
    }
    Ok((p, q))
}

fn rat(p: i64, q: i64) -> I {
    I::point(p as f64) / I::point(q as f64)
}

pub struct K2 {
    pub name: String,
    pub near: bool,
    pub lam: I,
    pub tau2: I,
    pub eta: I,
    pub linear3: bool,
    pub signs: [f64; 3],
    pub rho: f64,
    pub tmax: f64,
    pub bound: f64,
    /// scaled constants (exact floats): A = M^2 tau^2, B = M^2, M lambda/2, M eta, M
    pub ka: f64,
    pub kb: f64,
    pub khl: f64,
    pub keta: f64,
    pub km: f64,
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

/// Exact float from an integer numerator and a denominator 1 or 2, or an error.
fn exact(num: i64, den: i64) -> Result<f64, String> {
    if num.abs() > (1 << 50) || !(den == 1 || den == 2) {
        return Err("constant not exact".into());
    }
    Ok(num as f64 / den as f64)
}

impl K2 {
    pub fn from_name(name: &str) -> Result<K2, String> {
        let (base, m) = parse_name(name);
        let near = match base.as_str() {
            "k2far" => false,
            "k2near" => true,
            _ => return Err("not k2far/k2near".into()),
        };
        let (lp, lq) = parse_rat(&m, "lam")?;
        if lp >= lq {
            return Err("need lambda < 1".into());
        }
        let (ep, eq) = parse_rat(&m, "eta")?;
        let linear3 = match m.get("case").map(|s| s.as_str()) {
            Some("c") => false,
            Some("l") => true,
            _ => return Err("case=c|l".into()),
        };
        if near && linear3 {
            return Err("k2near only for case=c (case l misses [-1/2,1/2]^6: 2Q3 <= 1 < 2.77 <= lambda W3)".into());
        }
        let sg = m.get("s").ok_or("need s=+++ etc")?;
        if sg.len() != 3 || !sg.chars().all(|c| c == '+' || c == '-') {
            return Err("bad s".into());
        }
        let v: Vec<f64> = sg.chars().map(|c| if c == '-' { -1.0 } else { 1.0 }).collect();
        let (rho, tmax) = if near {
            let t: f64 = m.get("t").ok_or("k2near needs t=T")?.parse::<f64>().map_err(|e| e.to_string())?;
            let r = t * t;
            if !(t > 0.0) || t.mul_add(t, -r) != 0.0 || r > 0.5 {
                return Err("need T > 0 with T^2 exact and <= 1/2".into());
            }
            (r, t)
        } else {
            let r = match m.get("rho") {
                None => 0.0,
                Some(r) => r.parse::<f64>().map_err(|e| e.to_string())?,
            };
            if !(0.0..=0.5).contains(&r) {
                return Err("rho in [0, 1/2]".into());
            }
            (r, 0.0)
        };
        let mm = lq / gcd(lq, eq) * eq;
        let ka = exact(mm / lq * (mm / lq) * (lq * lq - lp * lp), 1)?;
        let kb = exact(mm * mm, 1)?;
        let khl = exact(mm / lq * lp, 2)?;
        let keta = exact(mm / eq * ep, 1)?;
        let km = exact(mm, 1)?;
        let bound = match m.get("c") {
            None => 0.0,
            Some(r) => r.parse::<f64>().map_err(|e| e.to_string())?,
        };
        Ok(K2 {
            name: name.to_string(),
            near,
            lam: rat(lp, lq),
            tau2: rat(lq * lq - lp * lp, lq * lq),
            eta: rat(ep, eq),
            linear3,
            signs: [v[0], v[1], v[2]],
            rho,
            tmax,
            bound,
            ka,
            kb,
            khl,
            keta,
            km,
        })
    }

    fn sigma<const N: usize, T: Scalar<N>>(&self, x: &[T; 6]) -> [T; 6] {
        if self.near {
            let (a12, a13, a23) = (x[0], x[1], x[2]);
            let (e12, e13, e23) = (
                T::cf(self.signs[0]) * x[3].sqr(),
                T::cf(self.signs[1]) * x[4].sqr(),
                T::cf(self.signs[2]) * x[5].sqr(),
            );
            [a12 + e12, a13 + e13, e12 - a12, a23 + e23, e13 - a13, e23 - a23]
        } else {
            *x
        }
    }

    /// True only if the point certainly satisfies every defining inequality of the piece.
    fn point_in_piece(&self, x: &[f64; 6]) -> bool {
        let b: [I; 6] = std::array::from_fn(|i| I::point(x[i]));
        self.piece_constraints(&b).iter().all(|g| g.is_valid() && g.lo >= 0.0)
    }

    /// Enclosures of the defining inequalities g >= 0 of the piece P(case, s) over the box.
    fn piece_constraints(&self, b: &BoxN<6>) -> Vec<I> {
        let s: [I; 6] = self.sigma::<6, I>(b);
        let c: [I; 6] = std::array::from_fn(|i| I::sqrt(&(I::point(1.0) - I::sqr(&s[i]))));
        let two = I::point(2.0);
        let q = [s[0] + s[1], s[2] + s[3], s[4] + s[5]];
        let w = |i: usize, a: usize, bb: usize| I::sqr(&(c[a] + c[bb])) + I::sqr(&q[i]);
        let g3 = self.lam * w(2, 4, 5) - two * q[2];
        let eps = [s[0] + s[2], s[1] + s[4], s[3] + s[5]];
        vec![
            -q[0],
            q[1],
            q[2],
            self.lam * w(0, 0, 1) - two * I::abs(&q[0]),
            self.lam * w(1, 2, 3) - two * q[1],
            if self.linear3 { -g3 } else { g3 },
            eps[0] * I::point(self.signs[0]),
            eps[1] * I::point(self.signs[1]),
            eps[2] * I::point(self.signs[2]),
        ]
    }

    /// True only if the closed box certainly misses the piece P(case, s).
    fn misses_piece(&self, b: &BoxN<6>) -> bool {
        self.piece_constraints(b).iter().any(|g| g.is_valid() && g.hi < 0.0)
    }
}

impl Problem<6> for K2 {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        format!(
            "K_(2,3) refined bracket: M Br' (k2m notes §5.4, M = {}) >= {} on the piece P(case={}, s={:?}) of F'_1 = {{Q1<=0, Q2>=0, Q3>=0, 2|Q1|<=lam W1, 2Q2<=lam W2}}, lam={:?}, eta={:?}; {}",
            self.km,
            self.bound,
            if self.linear3 { "l: 2Q3>=lam W3" } else { "c: 2Q3<=lam W3" },
            self.signs,
            self.lam,
            self.eta,
            if self.near {
                format!("coordinates (a12,a13,a23,t12,t13,t23), e_k=s_k t_k^2, sigma_ij=a+e, sigma_ji=e-a, a in [-{r},{r}]^3, t in [0,{}]^3", self.tmax, r = self.rho)
            } else {
                "coordinates sigma=(s12,s13,s21,s23,s31,s32) in [-1,1]^6".into()
            }
        )
    }
    fn domain(&self) -> BoxN<6> {
        if self.near {
            let r = self.rho;
            let mut b = [I::new(-r, r); 6];
            for k in 0..3 {
                b[3 + k] = I::new(0.0, self.tmax);
            }
            b
        } else {
            [I::new(-1.0, 1.0); 6]
        }
    }
    fn bound(&self) -> f64 {
        self.bound
    }
    fn eval<T: Scalar<6>>(&self, x: &[T; 6]) -> T {
        let s = self.sigma(x);
        let one = T::cf(1.0);
        let c: [T; 6] = std::array::from_fn(|i| (one - s[i].sqr()).sqrt());
        let (ka, kb, half) = (T::cf(self.ka), T::cf(self.kb), T::cf(0.5));
        // M V(u, v) = 1/2 sqrt(M^2 tau^2 (c_u + c_v)^2 + M^2 (u - v)^2)
        let v = |a: usize, b: usize| half * (ka * (c[a] + c[b]).sqr() + kb * (s[a] - s[b]).sqr()).sqrt();
        let hl = T::cf(self.khl);
        let e = T::cf(self.signs[0]) * (s[0] + s[2]) + T::cf(self.signs[1]) * (s[1] + s[4]) + T::cf(self.signs[2]) * (s[3] + s[5]);
        let v3 = if self.linear3 { T::cf(self.km) - hl * (s[4] + s[5]) } else { v(4, 5) };
        v(0, 1) + v(2, 3) + v3 + hl * e - T::cf(self.keta)
    }
    fn excluded(&self, b: &BoxN<6>) -> bool {
        if self.misses_piece(b) {
            return true;
        }
        let r = self.rho;
        !self.near && r > 0.0 && b.iter().all(|x| x.lo >= -r && x.hi <= r)
    }
    fn excluded_note(&self) -> String {
        let mut s = "box certainly misses the piece P(case,s) (a defining inequality is violated on the whole box)".to_string();
        if !self.near && self.rho > 0.0 {
            s += &format!("; or box inside the central cube [-{r},{r}]^6, covered by the 8 certificates k2near:...:s=..:t=sqrt({r})", r = self.rho);
        }
        s
    }
    fn point_in_domain(&self, x: &[f64; 6]) -> bool {
        self.point_in_piece(x)
    }
    fn special_points(&self) -> Vec<[f64; 6]> {
        if self.near {
            vec![[0.0; 6]]
        } else {
            vec![]
        }
    }
}
