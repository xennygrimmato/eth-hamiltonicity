//! Small test problems with known answers.
//!
//! `bowl2:c=..`   f(x,y) = 2 - cos x - cos y + x y / 2 on [-1,1]^2; min 0 at 0 only
//!                (1 - cos x >= 11 x^2 / 24 on [-1,1] and |xy|/2 <= (x^2+y^2)/4). True iff c <= 0.
//! `valley2:c=..` with u = x-1, v = y-1: f = u^2 + v^2 - 3uv/2 + u^3/10 on [-2,2]^2; min over v is
//!                u^2 (7/16 + u/10) >= 0 for u >= -4.375, so min 0 at (1,1) only (not the centre).
//! `ring2:c=..`   f(x,y) = x^2 + y^2 - sqrt(x^2+y^2) + 1/4 = (r - 1/2)^2 on [-1,1]^2; min 0 on a whole
//!                circle (non-isolated) and not smooth at 0: true for c <= 0, provable only for c < 0.

use super::{param_f64, parse_name};
use crate::ad::Scalar;
use crate::bnb::{BoxN, Problem};
use crate::interval::I;

pub struct TestFn {
    pub name: String,
    pub kind: u8,
    pub c: f64,
}

impl TestFn {
    pub fn from_name(name: &str) -> Result<TestFn, String> {
        let (base, m) = parse_name(name);
        let kind = match base.as_str() {
            "bowl2" => 0,
            "valley2" => 1,
            "ring2" => 2,
            _ => return Err("unknown test function".into()),
        };
        Ok(TestFn { name: name.to_string(), kind, c: param_f64(&m, "c", 0.0)? })
    }
}

impl Problem<2> for TestFn {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn statement(&self) -> String {
        format!("test function {} >= {}", self.kind, self.c)
    }
    fn domain(&self) -> BoxN<2> {
        match self.kind {
            1 => [I::new(-2.0, 2.0); 2],
            _ => [I::new(-1.0, 1.0); 2],
        }
    }
    fn bound(&self) -> f64 {
        self.c
    }
    fn eval<T: Scalar<2>>(&self, x: &[T; 2]) -> T {
        match self.kind {
            0 => T::cf(2.0) - x[0].cos() - x[1].cos() + x[0] * x[1] * T::cf(0.5),
            1 => {
                let u = x[0] - T::cf(1.0);
                let v = x[1] - T::cf(1.0);
                u * u + v * v - T::cf(1.5) * u * v + T::cf(0.1) * u * u * u
            }
            _ => {
                let r2 = x[0] * x[0] + x[1] * x[1];
                r2 - r2.sqrt() + T::cf(0.25)
            }
        }
    }
    fn special_points(&self) -> Vec<[f64; 2]> {
        match self.kind {
            0 => vec![[0.0, 0.0]],
            1 => vec![[1.0, 1.0]],
            _ => vec![],
        }
    }
}
