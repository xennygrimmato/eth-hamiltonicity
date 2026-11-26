//! Outward-rounded interval arithmetic on f64.
//!
//! Trust base (see README): IEEE-754 binary64 round-to-nearest for `+ - * / sqrt` and a correctly
//! rounded `mul_add` (fused multiply-add). No libm transcendental function is used anywhere.
//!
//! Every endpoint is computed by the round-to-nearest operation and then corrected in the right
//! direction using the *sign of the exact rounding error*:
//!   * sum:      error obtained exactly by TwoSum (Knuth),
//!   * product:  error sign = sign of fma(a, b, -r),
//!   * quotient: sign of the remainder fma(-r, b, a) times the sign of b,
//!   * sqrt:     sign of fma(r, r, -a).
//! (A correctly rounded fma returns 0 only if its exact value is 0 and otherwise has the sign of its
//! exact value, barring underflow; results of tiny magnitude are therefore widened unconditionally.)
//! If the error is zero the endpoint is exact, so exact computations (e.g. sin 0 = 0, F(0) = 3) stay
//! exact; otherwise it is moved by one ulp with `next_up` / `next_down`.
//!
//! An interval with a NaN endpoint is "invalid": it is the result of a domain error (sqrt of a
//! possibly negative number, division by an interval containing 0) and propagates; any bound derived
//! from it is rejected by the solver.

use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Below this magnitude we do not trust the error-sign tests (possible underflow): widen always.
const TINY: f64 = 1e-280;

#[inline]
fn nd(x: f64) -> f64 {
    x.next_down()
}
#[inline]
fn nu(x: f64) -> f64 {
    x.next_up()
}

/// Lower bound of a + b.
#[inline]
pub fn add_rd(a: f64, b: f64) -> f64 {
    let s = a + b;
    if !s.is_finite() {
        if s == f64::INFINITY && a.is_finite() && b.is_finite() {
            return f64::MAX;
        }
        return s;
    }
    let bb = s - a;
    let err = (a - (s - bb)) + (b - bb);
    if err < 0.0 {
        nd(s)
    } else {
        s
    }
}

/// Upper bound of a + b.
#[inline]
pub fn add_ru(a: f64, b: f64) -> f64 {
    let s = a + b;
    if !s.is_finite() {
        if s == f64::NEG_INFINITY && a.is_finite() && b.is_finite() {
            return f64::MIN;
        }
        return s;
    }
    let bb = s - a;
    let err = (a - (s - bb)) + (b - bb);
    if err > 0.0 {
        nu(s)
    } else {
        s
    }
}

#[inline]
pub fn sub_rd(a: f64, b: f64) -> f64 {
    add_rd(a, -b)
}
#[inline]
pub fn sub_ru(a: f64, b: f64) -> f64 {
    add_ru(a, -b)
}

/// Product of endpoints with the interval convention 0 * inf = 0.
#[inline]
fn mul_dir(a: f64, b: f64, up: bool) -> f64 {
    if a == 0.0 || b == 0.0 {
        return 0.0;
    }
    let r = a * b;
    if !r.is_finite() {
        if r.is_nan() {
            return r;
        }
        if a.is_finite() && b.is_finite() {
            // overflow
            return if r > 0.0 {
                if up { r } else { f64::MAX }
            } else if up {
                f64::MIN
            } else {
                r
            };
        }
        return r;
    }
    if r.abs() < TINY {
        return if up { nu(r) } else { nd(r) };
    }
    let e = a.mul_add(b, -r); // exact a*b - r has this sign
    if up {
        if e > 0.0 { nu(r) } else { r }
    } else if e < 0.0 {
        nd(r)
    } else {
        r
    }
}
#[inline]
pub fn mul_rd(a: f64, b: f64) -> f64 {
    mul_dir(a, b, false)
}
#[inline]
pub fn mul_ru(a: f64, b: f64) -> f64 {
    mul_dir(a, b, true)
}

/// Quotient a / b for b != 0 (b may be infinite).
#[inline]
fn div_dir(a: f64, b: f64, up: bool) -> f64 {
    if a == 0.0 {
        return 0.0;
    }
    let r = a / b;
    if !r.is_finite() {
        if r.is_nan() {
            return r;
        }
        if a.is_finite() {
            return if r > 0.0 {
                if up { r } else { f64::MAX }
            } else if up {
                f64::MIN
            } else {
                r
            };
        }
        return r;
    }
    if b.is_infinite() {
        // a finite, r = +-0: true quotient is exactly 0 in the limit sense used by intervals
        return 0.0;
    }
    if r.abs() < TINY || a.abs() < TINY || b.abs() < TINY {
        return if up { nu(r) } else { nd(r) };
    }
    let rem = (-r).mul_add(b, a); // a - r*b ; true q - r = rem / b
    let s = if b > 0.0 { rem } else { -rem };
    if up {
        if s > 0.0 { nu(r) } else { r }
    } else if s < 0.0 {
        nd(r)
    } else {
        r
    }
}

#[inline]
fn sqrt_dir(a: f64, up: bool) -> f64 {
    if a == 0.0 {
        return 0.0;
    }
    if a.is_infinite() {
        return a;
    }
    let r = a.sqrt();
    if a < TINY {
        return if up { nu(r) } else { nd(r).max(0.0) };
    }
    let e = r.mul_add(r, -a); // r^2 - a ; positive => r > sqrt(a)
    if up {
        if e < 0.0 { nu(r) } else { r }
    } else if e > 0.0 {
        nd(r)
    } else {
        r
    }
}

/// Closed interval [lo, hi]; lo may be -inf, hi may be +inf.
#[derive(Clone, Copy, PartialEq)]
pub struct I {
    pub lo: f64,
    pub hi: f64,
}

impl fmt::Debug for I {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:e}, {:e}]", self.lo, self.hi)
    }
}

pub const INVALID: I = I { lo: f64::NAN, hi: f64::NAN };

impl I {
    #[inline]
    pub fn new(lo: f64, hi: f64) -> I {
        debug_assert!(!(lo > hi), "bad interval {lo} {hi}");
        I { lo, hi }
    }
    /// Exact point (the float itself is the number meant).
    #[inline]
    pub fn point(x: f64) -> I {
        I { lo: x, hi: x }
    }
    pub fn entire() -> I {
        I { lo: f64::NEG_INFINITY, hi: f64::INFINITY }
    }
    #[inline]
    pub fn is_valid(&self) -> bool {
        !(self.lo.is_nan() || self.hi.is_nan())
    }
    #[inline]
    pub fn width(&self) -> f64 {
        sub_ru(self.hi, self.lo)
    }
    /// Midpoint as a float lying in [lo, hi] (not an enclosure, a chosen point).
    #[inline]
    pub fn mid(&self) -> f64 {
        let m = self.lo + 0.5 * (self.hi - self.lo);
        m.max(self.lo).min(self.hi)
    }
    #[inline]
    pub fn contains(&self, x: f64) -> bool {
        self.lo <= x && x <= self.hi
    }
    #[inline]
    pub fn contains_zero(&self) -> bool {
        self.lo <= 0.0 && 0.0 <= self.hi
    }
    #[inline]
    pub fn hull(&self, o: &I) -> I {
        if !self.is_valid() || !o.is_valid() {
            return INVALID;
        }
        I { lo: self.lo.min(o.lo), hi: self.hi.max(o.hi) }
    }
    /// Intersection (caller guarantees the true value lies in both).
    #[inline]
    pub fn meet(&self, o: &I) -> I {
        if !self.is_valid() || !o.is_valid() {
            return INVALID;
        }
        I { lo: self.lo.max(o.lo), hi: self.hi.min(o.hi) }
    }
    #[inline]
    pub fn mag(&self) -> f64 {
        self.lo.abs().max(self.hi.abs())
    }
    #[inline]
    pub fn abs(&self) -> I {
        if !self.is_valid() {
            return INVALID;
        }
        if self.lo >= 0.0 {
            *self
        } else if self.hi <= 0.0 {
            -*self
        } else {
            I { lo: 0.0, hi: self.mag() }
        }
    }
    #[inline]
    pub fn sqr(&self) -> I {
        if !self.is_valid() {
            return INVALID;
        }
        if self.lo >= 0.0 {
            I { lo: mul_rd(self.lo, self.lo), hi: mul_ru(self.hi, self.hi) }
        } else if self.hi <= 0.0 {
            I { lo: mul_rd(self.hi, self.hi), hi: mul_ru(self.lo, self.lo) }
        } else {
            let m = self.mag();
            I { lo: 0.0, hi: mul_ru(m, m) }
        }
    }
    /// sqrt; INVALID if the interval contains negative numbers.
    #[inline]
    pub fn sqrt(&self) -> I {
        if !self.is_valid() || self.lo < 0.0 {
            return INVALID;
        }
        I { lo: sqrt_dir(self.lo, false), hi: sqrt_dir(self.hi, true) }
    }
    #[inline]
    pub fn recip(&self) -> I {
        I::point(1.0) / *self
    }
    /// x * 2^k exactly (k small), used for halving.
    #[inline]
    pub fn scale_pow2(&self, f: f64) -> I {
        // multiplication by an exact power of two: exact unless under/overflow; use generic mul
        *self * I::point(f)
    }
    pub fn max_(&self, o: &I) -> I {
        I { lo: self.lo.max(o.lo), hi: self.hi.max(o.hi) }
    }
    pub fn min_(&self, o: &I) -> I {
        I { lo: self.lo.min(o.lo), hi: self.hi.min(o.hi) }
    }
}

impl Add for I {
    type Output = I;
    #[inline]
    fn add(self, o: I) -> I {
        if !self.is_valid() || !o.is_valid() {
            return INVALID;
        }
        I { lo: add_rd(self.lo, o.lo), hi: add_ru(self.hi, o.hi) }
    }
}
impl Sub for I {
    type Output = I;
    #[inline]
    fn sub(self, o: I) -> I {
        if !self.is_valid() || !o.is_valid() {
            return INVALID;
        }
        I { lo: sub_rd(self.lo, o.hi), hi: sub_ru(self.hi, o.lo) }
    }
}
impl Neg for I {
    type Output = I;
    #[inline]
    fn neg(self) -> I {
        I { lo: -self.hi, hi: -self.lo }
    }
}
impl Mul for I {
    type Output = I;
    #[inline]
    fn mul(self, o: I) -> I {
        if !self.is_valid() || !o.is_valid() {
            return INVALID;
        }
        let (a, b, c, d) = (self.lo, self.hi, o.lo, o.hi);
        // fast paths by sign
        if a >= 0.0 && c >= 0.0 {
            return I { lo: mul_rd(a, c), hi: mul_ru(b, d) };
        }
        if b <= 0.0 && d <= 0.0 {
            return I { lo: mul_rd(b, d), hi: mul_ru(a, c) };
        }
        if a >= 0.0 && d <= 0.0 {
            return I { lo: mul_rd(b, c), hi: mul_ru(a, d) };
        }
        if b <= 0.0 && c >= 0.0 {
            return I { lo: mul_rd(a, d), hi: mul_ru(b, c) };
        }
        let lo = mul_rd(a, c).min(mul_rd(a, d)).min(mul_rd(b, c)).min(mul_rd(b, d));
        let hi = mul_ru(a, c).max(mul_ru(a, d)).max(mul_ru(b, c)).max(mul_ru(b, d));
        I { lo, hi }
    }
}
impl Div for I {
    type Output = I;
    #[inline]
    fn div(self, o: I) -> I {
        if !self.is_valid() || !o.is_valid() || o.contains_zero() {
            return INVALID;
        }
        let (a, b, c, d) = (self.lo, self.hi, o.lo, o.hi);
        let lo = div_dir(a, c, false).min(div_dir(a, d, false)).min(div_dir(b, c, false)).min(div_dir(b, d, false));
        let hi = div_dir(a, c, true).max(div_dir(a, d, true)).max(div_dir(b, c, true)).max(div_dir(b, d, true));
        I { lo, hi }
    }
}
impl Add<f64> for I {
    type Output = I;
    #[inline]
    fn add(self, o: f64) -> I {
        self + I::point(o)
    }
}
impl Mul<f64> for I {
    type Output = I;
    #[inline]
    fn mul(self, o: f64) -> I {
        self * I::point(o)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_stays_exact() {
        let x = I::point(1.0) + I::point(2.0);
        assert_eq!(x, I::point(3.0));
        let y = I::point(3.0) * I::point(0.5);
        assert_eq!(y, I::point(1.5));
        assert_eq!(I::point(4.0).sqrt(), I::point(2.0));
        assert_eq!(I::point(0.0) * I::entire(), I::point(0.0));
    }

    #[test]
    fn inexact_is_widened() {
        let t = I::point(1.0) / I::point(3.0);
        assert!(t.lo < t.hi);
        assert_eq!(t.lo.next_up(), t.hi);
        // 3 * [1/3] must contain 1
        let o = t * I::point(3.0);
        assert!(o.contains(1.0));
        let s = I::point(2.0).sqrt();
        assert!(s.lo < s.hi);
        assert!(s.sqr().contains(2.0));
        let a = I::point(0.1) + I::point(0.2);
        assert!(a.lo < a.hi);
        // TwoSum exactness: 1e16 + 1 is not representable
        let b = I::point(1e16) + I::point(1.0);
        assert!(b.lo == 1e16 && b.hi == (1e16f64).next_up());
    }

    #[test]
    fn sqrt_domain() {
        assert!(!I::new(-1e-300, 1.0).sqrt().is_valid());
        assert!(!(I::point(1.0) / I::new(-1.0, 1.0)).is_valid());
    }

    #[test]
    fn random_containment() {
        // integers below 2^53: products and sums are exact in i128, endpoints >= 2^53 are integers
        let mut s: u64 = 12345;
        let mut rnd = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for _ in 0..200000 {
            let a = (rnd() % (1u64 << 53)) as i128 - (1i128 << 52);
            let b = (rnd() % (1u64 << 53)) as i128 - (1i128 << 52);
            let (fa, fb) = (a as f64, b as f64);
            let p = I::point(fa) * I::point(fb);
            let e = a * b;
            assert!((p.lo as i128) <= e && e <= (p.hi as i128), "{a} {b} {p:?}");
            assert!(p.hi == p.lo || p.lo.next_up() == p.hi);
            let q = I::point(fa * 4096.0) + I::point(fb / 4096.0);
            // exact sum at scale 2^-12: a*2^24 + b, compare scaled endpoints
            let es = a * (1i128 << 24) + b;
            assert!(((q.lo * 4096.0) as i128) <= es && es <= ((q.hi * 4096.0).ceil() as i128));
            if b != 0 {
                // division: check lo*b <= a <= hi*b (for b>0) using the interval product enclosure
                let d = I::point(fa) / I::point(fb);
                let back = d * I::point(fb);
                assert!(back.contains(fa));
            }
            let r = I::point(fa.abs()).sqrt();
            assert!(r.sqr().contains(fa.abs()));
        }
    }
}
