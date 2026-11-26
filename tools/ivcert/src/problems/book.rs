//! Direct certificate for the book claim (hull notes §3.1, §3.4): for every book of three flat triangles
//! (u1, u2, v_j) glued along the common side [u1, u2],
//!     Sigma_S >= (3/sqrt 10) Sigma_T,  i.e.  G := sqrt(10) Sigma_S - 3 Sigma_T >= 0,
//! where Sigma_S = sum_{i,j} |u_i v_j| and Sigma_T = |u1 u2| + sum_{j<k} d^Z(v_j, v_k).
//! Coordinates: spine u1 = (0,-h), u2 = (0,h); page j point v_j = (rho_j >= 0, s_j) (distance from the
//! spine line, height). d^Z_jk = min_{t in [-h,h]} g(t), g(t) = |v_j - (0,t)| + |v_k - (0,t)| (convex).
//! With P = rho_j + rho_k, N = s_j rho_k + s_k rho_j the unconstrained minimiser (unfolded straight
//! line) is y* = N / P, and:
//!   P > 0, -h <= y* <= h  (N - hP <= 0 <= N + hP) : d^Z = sqrt(P^2 + (s_j - s_k)^2)
//!   P > 0, y* >= h                                : d^Z = g(h)
//!   P > 0, y* <= -h                               : d^Z = g(-h)
//!   P > 0, y* straddles +-h                      : g(h tau) with tau a constant enclosure of the
//!                                                   minimiser tau* = clamp(y*/h) (Danskin: C^1 only)
//!   P may be 0                                    : value enclosure g(T) ∩ [line.lo, inf) with
//!                                                   T = clamp(hull(s_j, s_k), -h, h) ⊇ argmin g,
//!                                                   upper end also <= g(h), g(-h), g(0)
//! The branch is decided from enclosures over the whole box (or point), so on the box the formula used
//! coincides with d^Z; smooth branches are differentiated, the straddling one only enclosed.
//! sqrt(10) Sigma_S is written as sum sqrt(10 (rho^2 + (s -+ h)^2)), so at W5 (rho = 3, s = 0, h = 1)
//! every term is exact (sqrt(100) = 10) and G(W5) = 0 exactly.
//!
//! G is positively homogeneous of degree 1 in (h, rho, s). Cover of all books with h > 0
//! (h = 0 gives R >= 1, notes §3.1):
//!   `book:m=M`        h = 1, rho in [0,M]^3, s in [-M,M]^3 (contains W5 = (3,3,3,0,0,0) in the interior).
//!   `bookface:f=rho:m=M` and `bookface:f=s:m=M`: the books with max(rho_j, |s_j|) > M at h = 1,
//!        rescaled by 1/max: coordinates with max = 1 and h in [0, 1/M]. By page permutations and
//!        s -> -s the maximum may be assumed to be rho_1 (f=rho: x = (h, rho2, rho3, s1, s2, s3), rho_1 = 1)
//!        or s_1 (f=s: x = (h, rho1, rho2, rho3, s2, s3), s_1 = 1).
//! Symmetries in `book`: page permutations and s -> -s; fundamental domain rho1 >= rho2 >= rho3,
//! s1 + s2 + s3 >= 0.

use super::{param_f64, parse_name};
use crate::ad::Scalar;
use crate::bnb::{BoxN, Problem};
use crate::interval::{add_ru, I};

fn dz<const N: usize, T: Scalar<N>>(h: T, rj: T, sj: T, rk: T, sk: T) -> T {
    let p = rj + rk;
    let n = sj * rk + sk * rj;
    let line = (p.sqr() + (sj - sk).sqr()).sqrt();
    let g = |t: T| (rj.sqr() + (sj - t).sqr()).sqrt() + (rk.sqr() + (sk - t).sqr()).sqrt();
    let (pv, up, dn) = (p.val(), (n - h * p).val(), (n + h * p).val());
    if pv.is_valid() && pv.lo > 0.0 && up.is_valid() && dn.is_valid() {
        if up.hi <= 0.0 && dn.lo >= 0.0 {
            return line;
        }
        if up.lo >= 0.0 {
            return g(h);
        }
        if dn.hi <= 0.0 {
            return g(-h);
        }
    }
    if pv.is_valid() && pv.lo > 0.0 && up.is_valid() && dn.is_valid() {
        // y* straddles an end of the spine. With t = h tau, tau in [-1, 1] (a fixed set),
        // g(x, h tau) is strictly convex in tau when h > 0 and P > 0, so the minimiser tau*(x) is
        // unique and by Danskin's theorem d^Z is C^1 with gradient grad_x g(x, h tau)|_{tau = tau*}.
        // Hence evaluating g with tau replaced by a constant enclosure of tau* gives valid value and
        // gradient enclosures (Hessian dropped). If h may be 0 we use tau in [-1, 1]; the mean-value
        // form only needs differentiability inside segments, where h > 0 whenever the box centre has
        // h > 0 (the centre of a box with h in [0, w], w > 0).
        let hv = h.val();
        let tau = if hv.lo > 0.0 {
            let yh = (n.val() / pv) / hv;
            if yh.is_valid() {
                let cl = |x: f64| x.max(-1.0).min(1.0);
                I::new(cl(yh.lo), cl(yh.hi))
            } else {
                I::new(-1.0, 1.0)
            }
        } else {
            I::new(-1.0, 1.0)
        };
        let t = h * T::cst(tau);
        // value: also d^Z >= line distance and d^Z <= g(t) for t = h, -h, 0
        let mut up = f64::INFINITY;
        for x in [g(h).val(), g(-h).val(), g(T::cf(0.0)).val()] {
            if x.is_valid() {
                up = up.min(x.hi);
            }
        }
        let lw = line.val();
        let lo = if lw.is_valid() { lw.lo } else { f64::NEG_INFINITY };
        return g(t).c1_only().meet_val(I::new(lo, up));
    }
    // P may vanish. Every minimiser of the convex g over [-h, h] lies in clamp(hull(s_j, s_k), -h, h)
    // (y* is a convex combination of s_j, s_k when P > 0; for P = 0 the unconstrained minimisers are
    // the points between s_j and s_k). So d^Z = g(t*) lies in g(T) for that interval T, and
    // d^Z >= line distance.
    let (sjv, skv, hv) = (sj.val(), sk.val(), h.val());
    let gl = line.val();
    if !(sjv.is_valid() && skv.is_valid() && hv.is_valid() && gl.is_valid()) {
        return T::from_enclosure(crate::interval::INVALID);
    }
    // t* = clamp(y, -h, h) with y in [S.lo, S.hi], h in [h.lo, h.hi]:
    //   t* >= min(max(S.lo, -h.hi), h.lo),  t* <= max(min(S.hi, h.hi), -h.lo)
    let (slo, shi) = (sjv.lo.min(skv.lo), sjv.hi.max(skv.hi));
    let tt = I::new(slo.max(-hv.hi).min(hv.lo), shi.min(hv.hi).max(-hv.lo));
    let gv = g(T::cst(tt)).val();
    if !gv.is_valid() {
        return T::from_enclosure(crate::interval::INVALID);
    }
    // also d^Z <= g(t) for each fixed t in [-h, h]: t = h, -h, 0
    let (gp, gm, g0) = (g(h).val(), g(-h).val(), g(T::cf(0.0)).val());
    let mut up = gv.hi;
    for x in [gp, gm, g0] {
        if x.is_valid() {
            up = up.min(x.hi);
        }
    }
    let v = I::new(gv.lo.max(gl.lo), up);
    if !(v.lo <= v.hi) {
        return T::from_enclosure(crate::interval::INVALID);
    }
    T::from_enclosure(v)
}

/// G(h, rho, s) = sum_j [sqrt(10(rho_j^2+(s_j+h)^2)) + sqrt(10(rho_j^2+(s_j-h)^2))] - 3 (2h + sum d^Z).
pub fn book_g<const N: usize, T: Scalar<N>>(h: T, r: [T; 3], s: [T; 3]) -> T {
    let ten = T::cf(10.0);
    let mut num = T::cf(0.0);
    for j in 0..3 {
        num = num + (ten * (r[j].sqr() + (s[j] + h).sqr())).sqrt() + (ten * (r[j].sqr() + (s[j] - h).sqr())).sqrt();
    }
    let mut den = T::cf(2.0) * h;
    for (j, k) in [(0, 1), (0, 2), (1, 2)] {
        den = den + dz(h, r[j], s[j], r[k], s[k]);
    }
    num - T::cf(3.0) * den
}

pub struct Book {
    pub name: String,
    pub m: f64,
}

impl Book {
    pub fn from_name(name: &str) -> Result<Book, String> {
        let (base, mm) = parse_name(name);
        if base != "book" {
            return Err("not book".into());
        }
        Ok(Book { name: name.to_string(), m: param_f64(&mm, "m", 128.0)? })
    }
}

impl Problem<6> for Book {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        format!("book claim, h=1: G(1,rho,s) >= 0 for rho in [0,{m}]^3, s in [-{m},{m}]^3; x=(rho1,rho2,rho3,s1,s2,s3)", m = self.m)
    }
    fn domain(&self) -> BoxN<6> {
        let m = self.m;
        [I::new(0.0, m), I::new(0.0, m), I::new(0.0, m), I::new(-m, m), I::new(-m, m), I::new(-m, m)]
    }
    fn bound(&self) -> f64 {
        0.0
    }
    fn eval<T: Scalar<6>>(&self, x: &[T; 6]) -> T {
        book_g(T::cf(1.0), [x[0], x[1], x[2]], [x[3], x[4], x[5]])
    }
    fn special_points(&self) -> Vec<[f64; 6]> {
        vec![[3.0, 3.0, 3.0, 0.0, 0.0, 0.0]]
    }
    /// grad G = 0 at W5 = (3,3,3,0,0,0): d/ds_j vanishes since G is even in s (s -> -s swaps u1, u2);
    /// d/drho_j = 2 * 10*3/sqrt(100) - 3 * 2 * (3+3)/sqrt(36) = 6 - 6 = 0.
    fn anchors_critical(&self) -> bool {
        true
    }
    /// G is C^1 wherever no distance vanishes (d^Z is C^1 by Danskin: unique minimiser when P > 0).
    fn c1(&self) -> bool {
        true
    }
    fn outside_fundamental(&self, b: &BoxN<6>) -> bool {
        b[0].hi < b[1].lo || b[1].hi < b[2].lo || add_ru(add_ru(b[3].hi, b[4].hi), b[5].hi) < 0.0
    }
}

pub struct BookFace {
    pub name: String,
    pub m: f64,
    pub rho_face: bool,
}

impl BookFace {
    pub fn from_name(name: &str) -> Result<BookFace, String> {
        let (base, mm) = parse_name(name);
        if base != "bookface" {
            return Err("not bookface".into());
        }
        let f = mm.get("f").map(|s| s.as_str()).unwrap_or("rho");
        if f != "rho" && f != "s" {
            return Err("f must be rho or s".into());
        }
        Ok(BookFace { name: name.to_string(), m: param_f64(&mm, "m", 128.0)?, rho_face: f == "rho" })
    }
}

impl Problem<6> for BookFace {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        if self.rho_face {
            format!("book claim, face rho1=1: G >= 0 for x=(h,rho2,rho3,s1,s2,s3), h in [0,1/{}], rho in [0,1], s in [-1,1]", self.m)
        } else {
            format!("book claim, face s1=1: G >= 0 for x=(h,rho1,rho2,rho3,s2,s3), h in [0,1/{}], rho in [0,1], s in [-1,1]", self.m)
        }
    }
    fn domain(&self) -> BoxN<6> {
        let hm = 1.0 / self.m; // exact for M a power of two
        assert!(hm * self.m == 1.0);
        if self.rho_face {
            [I::new(0.0, hm), I::new(0.0, 1.0), I::new(0.0, 1.0), I::new(-1.0, 1.0), I::new(-1.0, 1.0), I::new(-1.0, 1.0)]
        } else {
            [I::new(0.0, hm), I::new(0.0, 1.0), I::new(0.0, 1.0), I::new(0.0, 1.0), I::new(-1.0, 1.0), I::new(-1.0, 1.0)]
        }
    }
    fn bound(&self) -> f64 {
        0.0
    }
    fn eval<T: Scalar<6>>(&self, x: &[T; 6]) -> T {
        if self.rho_face {
            book_g(x[0], [T::cf(1.0), x[1], x[2]], [x[3], x[4], x[5]])
        } else {
            book_g(x[0], [x[1], x[2], x[3]], [T::cf(1.0), x[4], x[5]])
        }
    }
}
