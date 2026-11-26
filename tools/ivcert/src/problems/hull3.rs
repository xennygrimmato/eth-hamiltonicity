//! Inequality (I), three-angle form:
//!   F(t) = sum_{i<j} cos((t_i - t_j)/2) * sqrt(1 + k sin^2((t_i + t_j)/2)) >= c   on [-pi/2, pi/2]^3,
//! with k = 9, c = 3 (equality at t = 0). Parameters k, c only for testing (k = 2 makes it false).
//! Symmetries: permutations of the t_i and t -> -t; fundamental domain
//!   R = { t_1 >= t_2 >= t_3, t_1 + t_2 + t_3 >= 0 }.

use super::{param_f64, parse_name};
use crate::ad::Scalar;
use crate::bnb::{BoxN, Problem};
use crate::elem::PI_HI;
use crate::interval::{add_ru, I};

pub struct Hull3 {
    pub name: String,
    pub k: f64,
    pub c: f64,
}

impl Hull3 {
    pub fn from_name(name: &str) -> Result<Hull3, String> {
        let (base, m) = parse_name(name);
        if base != "hull3" {
            return Err("not hull3".into());
        }
        Ok(Hull3 { name: name.to_string(), k: param_f64(&m, "k", 9.0)?, c: param_f64(&m, "c", 3.0)? })
    }
}

impl Problem<3> for Hull3 {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        format!(
            "sum_{{i<j}} cos((t_i-t_j)/2) sqrt(1+{} sin^2((t_i+t_j)/2)) >= {} for t in [-pi/2,pi/2]^3 (float box [-{:e},{:e}]^3)",
            self.k, self.c, PI_HI * 0.5, PI_HI * 0.5
        )
    }
    fn domain(&self) -> BoxN<3> {
        // PI_HI/2 > pi/2: the float box contains the true domain
        let h = PI_HI * 0.5;
        [I::new(-h, h); 3]
    }
    fn bound(&self) -> f64 {
        self.c
    }
    fn eval<T: Scalar<3>>(&self, t: &[T; 3]) -> T {
        let half = T::cf(0.5);
        let kk = T::cf(self.k);
        let one = T::cf(1.0);
        let mut acc = T::cf(0.0);
        for (i, j) in [(0, 1), (0, 2), (1, 2)] {
            let m = (t[i] - t[j]) * half;
            let s = (t[i] + t[j]) * half;
            acc = acc + m.cos() * (one + kk * s.sin().sqr()).sqrt();
        }
        acc
    }
    fn special_points(&self) -> Vec<[f64; 3]> {
        vec![[0.0; 3]]
    }
    fn outside_fundamental(&self, b: &BoxN<3>) -> bool {
        b[0].hi < b[1].lo || b[1].hi < b[2].lo || add_ru(add_ru(b[0].hi, b[1].hi), b[2].hi) < 0.0
    }
}
