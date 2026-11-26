//! Inequality (CL*) (hull notes §3.3(b)) in sine coordinates.
//!
//! Original: psi = (psi12, psi13, psi21, psi23, psi31, psi32) in [-pi/2, pi/2]^6,
//!   Phi = sum_i cos mu_i sqrt(1 + 9 sin^2 delta_i) - 3 + (3/2) sum_{i<j} |sin psi_ij + sin psi_ji|.
//! Substitution sigma = sin psi (a bijection [-pi/2,pi/2] -> [-1,1]; cos psi = sqrt(1 - sigma^2) >= 0)
//! and the identity  cos mu_i sqrt(1 + 9 sin^2 delta_i) = 1/2 sqrt((c_ij + c_ik)^2 + 10 (s_ij - s_ik)^2)
//! (c = cos psi, s = sin psi; uses cos mu_i >= 0) give the exactly equivalent statement
//!   Phi(sigma) = 1/2 sum_i sqrt((c_ij + c_ik)^2 + 10 (sigma_ij - sigma_ik)^2) - 3
//!                + 3/2 sum_{i<j} |sigma_ij + sigma_ji|  >= 0  on [-1,1]^6,  c = sqrt(1 - sigma^2).
//! No transcendental function and no pi enclosure is involved; the domain box is exact.
//!
//! Coordinates: x = (s12, s13, s21, s23, s31, s32). Pairs: {12} = (x0,x2), {13} = (x1,x4), {23} = (x3,x5).
//! Vertices: 1 -> (x0,x1), 2 -> (x2,x3), 3 -> (x4,x5).
//!
//! `clstar:rho=R`  : the domain [-1,1]^6 with two kinds of excluded boxes (leaves X):
//!    (i) boxes inside the central cube [-R,R]^6 (R = 1/2 default; R <= 1/2 needed below): covered by the eight
//!        certificates `clnear:rho=R:s=...` (each sigma-cube point maps into the (a,e)-box, see below);
//!   (ii) corner regions: for a pair {jk} and s = +-1, s*sigma_jk >= 15/16 and s*sigma_kj >= 15/16.
//!        Corner lemma (analytic): put d1 = 1 - s sigma_jk, d2 = 1 - s sigma_kj in [0, 1/16]. Then
//!        V_j >= c_jk / 2 = sqrt(d1 (2 - d1)) / 2 >= sqrt(d1)/2, V_k >= sqrt(d2)/2, all V >= 0, the other
//!        two |eps| >= 0 and |eps_jk| = 2 - d1 - d2, so Phi >= (sqrt d1 + sqrt d2)/2 - (3/2)(d1 + d2) >= 0
//!        because 3 d <= sqrt(d) for d <= 1/9.
//! Symmetry (both problems): S3 relabelling of the vertices (permuting the six ordered pairs) and the
//! global sign flip sigma -> -sigma. Fundamental domain: w1 >= w2 >= w3 and w1 + w2 + w3 >= 0, where
//! w_i = sigma_ij + sigma_ik (a permutation pi maps w_i to w_pi(i); the flip negates all w).
//!
//! `clnear:rho=R:s=+-+` : the central region in coordinates a_k = (sigma_ij - sigma_ji)/2,
//! e_k = (sigma_ij + sigma_ji)/2 (k = 12, 13, 23), on the orthant box a in [-R,R]^3, e_k in s_k [0,R].
//! There |sigma_ij + sigma_ji| = 2 s_k e_k is smooth. Each point of the sigma-cube [-R,R]^6 has (a,e) in
//! [-R,R]^6, hence in one of the 8 orthant boxes, and its sigma = (a+e, e-a) lies in [-2R,2R]^6 ⊂ [-1,1]^6.
//! Equality point 0 (a corner of every orthant box) is closed by the gain test with linear block e
//! (gradient 3 s_k in e_k, zero in a; Hessian in a positive definite = inequality (I) slice).

use super::{param_f64, parse_name};
use crate::ad::Scalar;
use crate::bnb::{BoxN, Problem};
use crate::interval::{add_ru, I};

/// `kp1` = 1 + k with k = 9 for (CL*) (other values only for tests).
fn vertex_terms<const N: usize, T: Scalar<N>>(s: &[T; 6], kp1: f64) -> T {
    let one = T::cf(1.0);
    let ten = T::cf(kp1);
    let c: [T; 6] = std::array::from_fn(|i| (one - s[i].sqr()).sqrt());
    let mut acc = T::cf(0.0);
    for (a, b) in [(0, 1), (2, 3), (4, 5)] {
        acc = acc + ((c[a] + c[b]).sqr() + ten * (s[a] - s[b]).sqr()).sqrt();
    }
    acc * T::cf(0.5)
}

/// Rigorous enclosure of w_i = sigma_ij + sigma_ik and of their sum, from sigma intervals.
fn outside_fd(sg: &[I; 6]) -> bool {
    let w: [I; 3] = [sg[0] + sg[1], sg[2] + sg[3], sg[4] + sg[5]];
    let tot_hi = add_ru(add_ru(w[0].hi, w[1].hi), w[2].hi);
    w[0].hi < w[1].lo || w[1].hi < w[2].lo || tot_hi < 0.0
}

pub struct ClStar {
    pub name: String,
    pub rho: f64,
    pub kp1: f64,
}

impl ClStar {
    pub fn from_name(name: &str) -> Result<ClStar, String> {
        let (base, m) = parse_name(name);
        if base != "clstar" {
            return Err("not clstar".into());
        }
        Ok(ClStar { name: name.to_string(), rho: param_f64(&m, "rho", 0.5)?, kp1: 1.0 + param_f64(&m, "k", 9.0)? })
    }
}

const CORNER: f64 = 0.9375; // 15/16

impl Problem<6> for ClStar {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        "(CL*) in sine coordinates: 1/2 sum_i sqrt((c_ij+c_ik)^2+10(s_ij-s_ik)^2) - 3 + 3/2 sum_{i<j} |s_ij+s_ji| >= 0 on [-1,1]^6, c=sqrt(1-s^2); x=(s12,s13,s21,s23,s31,s32)".into()
    }
    fn domain(&self) -> BoxN<6> {
        [I::new(-1.0, 1.0); 6]
    }
    fn bound(&self) -> f64 {
        0.0
    }
    fn eval<T: Scalar<6>>(&self, s: &[T; 6]) -> T {
        let e = (s[0] + s[2]).abs() + (s[1] + s[4]).abs() + (s[3] + s[5]).abs();
        vertex_terms(s, self.kp1) - T::cf(3.0) + T::cf(1.5) * e
    }
    fn outside_fundamental(&self, b: &BoxN<6>) -> bool {
        outside_fd(b)
    }
    fn excluded(&self, b: &BoxN<6>) -> bool {
        let r = self.rho;
        if r > 0.5 {
            return false;
        }
        if b.iter().all(|x| x.lo >= -r && x.hi <= r) {
            return true;
        }
        for (p, q) in [(0, 2), (1, 4), (3, 5)] {
            if b[p].lo >= CORNER && b[q].lo >= CORNER {
                return true;
            }
            if b[p].hi <= -CORNER && b[q].hi <= -CORNER {
                return true;
            }
        }
        false
    }
    fn excluded_note(&self) -> String {
        format!(
            "(i) central cube [-{r},{r}]^6: the 8 certificates clnear:rho={r}:s=..; (ii) corner regions s*sigma_jk, s*sigma_kj >= 15/16: corner lemma (analytic, see clstar.rs / notes)",
            r = self.rho
        )
    }
}

pub struct ClNear {
    pub name: String,
    pub rho: f64,
    pub kp1: f64,
    pub signs: [f64; 3],
}

impl ClNear {
    pub fn from_name(name: &str) -> Result<ClNear, String> {
        let (base, m) = parse_name(name);
        if base != "clnear" {
            return Err("not clnear".into());
        }
        let sg = m.get("s").ok_or("clnear needs s=+++ etc")?;
        let v: Vec<f64> = sg.chars().map(|c| if c == '-' { -1.0 } else { 1.0 }).collect();
        if v.len() != 3 || !sg.chars().all(|c| c == '+' || c == '-') {
            return Err("bad s".into());
        }
        Ok(ClNear {
            name: name.to_string(),
            rho: param_f64(&m, "rho", 0.5)?,
            kp1: 1.0 + param_f64(&m, "k", 9.0)?,
            signs: [v[0], v[1], v[2]],
        })
    }
}

impl Problem<6> for ClNear {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        format!(
            "(CL*) near 0 in coordinates x=(a12,a13,a23,e12,e13,e23), sigma_ij=a+e, sigma_ji=e-a, on a in [-{r},{r}]^3, e_k in s_k*[0,{r}] with s={:?}; |sigma_ij+sigma_ji| = 2 s_k e_k",
            self.signs,
            r = self.rho
        )
    }
    fn domain(&self) -> BoxN<6> {
        let r = self.rho;
        assert!(r <= 0.5, "rho <= 1/2 keeps sigma = a +- e inside [-1,1]");
        let mut b = [I::new(-r, r); 6];
        for k in 0..3 {
            b[3 + k] = if self.signs[k] > 0.0 { I::new(0.0, r) } else { I::new(-r, 0.0) };
        }
        b
    }
    fn bound(&self) -> f64 {
        0.0
    }
    fn eval<T: Scalar<6>>(&self, x: &[T; 6]) -> T {
        let (a12, a13, a23, e12, e13, e23) = (x[0], x[1], x[2], x[3], x[4], x[5]);
        let s: [T; 6] = [a12 + e12, a13 + e13, e12 - a12, a23 + e23, e13 - a13, e23 - a23];
        let gain = T::cf(self.signs[0]) * e12 + T::cf(self.signs[1]) * e13 + T::cf(self.signs[2]) * e23;
        vertex_terms(&s, self.kp1) - T::cf(3.0) + T::cf(3.0) * gain
    }
    fn special_points(&self) -> Vec<[f64; 6]> {
        vec![[0.0; 6]]
    }
    fn linear_block(&self) -> [bool; 6] {
        [false, false, false, true, true, true]
    }
}

