//! Rigorous enclosures of pi, sin, cos, built only from the basic interval operations.
//!
//! pi: PI_LO = the f64 nearest pi = 3.141592653589793115997963... < pi, PI_HI = next float up.
//! (The decimal expansion of PI_LO is checked in a unit test against 30 digits of pi.)
//!
//! sin/cos of a float x: x = q*(pi/2) + r with q = round(x / (pi/2)) an integer, r enclosed by
//! interval arithmetic with the pi enclosure, |r| <= pi/4 + tiny; then sin x is +-sin r or +-cos r and
//! sin r, cos r are Taylor polynomials (Horner, interval arithmetic) plus the Lagrange remainder
//! |R_m| <= |r|^m / m!, which is valid for sin and cos for every real r.
//!
//! sin/cos of an interval X: hull of the values at the two endpoints and of +-1 for every
//! critical point (j + 1/2) pi (sin) or j pi (cos) that possibly lies in X; [-1, 1] if X is wider
//! than 2 pi.

use crate::interval::I;

pub const PI_LO: f64 = std::f64::consts::PI;
pub const PI_HI: f64 = 3.1415926535897936; // == PI_LO.next_up(), checked in tests

#[inline]
pub fn pi() -> I {
    I::new(PI_LO, PI_HI)
}
#[inline]
pub fn half_pi() -> I {
    // halving is exact
    I::new(PI_LO * 0.5, PI_HI * 0.5)
}

/// Number of Taylor terms; |r| <= 0.786 < 0.8 and 0.8^27/27! < 1e-30.
const M_SIN: usize = 27; // remainder order for sin: terms r^1..r^25
const M_COS: usize = 26; // remainder order for cos: terms r^0..r^24

fn remainder(r: I, m: usize) -> I {
    // bound |r|^m / m!
    let a = I::point(r.mag());
    let mut p = I::point(1.0);
    for k in 1..=m {
        p = p * a / I::point(k as f64);
    }
    I::new(-p.hi, p.hi)
}

/// sin(r) for an interval r with |r| <= ~0.8 (Taylor + remainder).
fn sin_small(r: I) -> I {
    let r2 = r.sqr();
    // sin r = r (1 - r2/(2*3) (1 - r2/(4*5) (1 - ... )))
    let mut acc = I::point(1.0);
    let n = (M_SIN - 1) / 2; // highest power 2n-1 = 25 -> k from n-1 down to 1
    for k in (1..n).rev() {
        let den = I::point(((2 * k) * (2 * k + 1)) as f64);
        acc = I::point(1.0) - r2 * acc / den;
    }
    r * acc + remainder(r, M_SIN)
}

/// cos(r) for an interval r with |r| <= ~0.8.
fn cos_small(r: I) -> I {
    let r2 = r.sqr();
    // cos r = 1 - r2/(1*2) (1 - r2/(3*4) (1 - ...)), highest power 24
    let mut acc = I::point(1.0);
    let n = M_COS / 2; // 13
    for k in (1..n).rev() {
        let den = I::point(((2 * k - 1) * (2 * k)) as f64);
        acc = I::point(1.0) - r2 * acc / den;
    }
    acc + remainder(r, M_COS)
}

fn clamp1(x: I) -> I {
    I::new(x.lo.max(-1.0), x.hi.min(1.0))
}

/// (sin x, cos x) for a single float x, |x| < 1e15.
pub fn sincos_point(x: f64) -> (I, I) {
    if x == 0.0 {
        return (I::point(0.0), I::point(1.0));
    }
    assert!(x.abs() < 1e15, "argument too large for this range reduction");
    let q = (x / (PI_LO * 0.5)).round();
    let r = I::point(x) - I::point(q) * half_pi();
    let (s, c) = (sin_small(r), cos_small(r));
    let qm = (q.rem_euclid(4.0)) as i64;
    let (s, c) = match qm {
        0 => (s, c),
        1 => (c, -s),
        2 => (-s, -c),
        _ => (-c, s),
    };
    (clamp1(s), clamp1(c))
}

/// Interval sine.
pub fn sin(x: I) -> I {
    if !x.is_valid() {
        return x;
    }
    if x.lo == x.hi {
        return sincos_point(x.lo).0;
    }
    if !(x.lo.is_finite() && x.hi.is_finite()) || x.width() >= 6.28 {
        return I::new(-1.0, 1.0);
    }
    let mut res = sincos_point(x.lo).0.hull(&sincos_point(x.hi).0);
    // critical points (j + 1/2) pi with value (-1)^j
    let j0 = (x.lo / PI_LO - 0.5).floor() as i64 - 1;
    let j1 = (x.hi / PI_LO - 0.5).ceil() as i64 + 1;
    for j in j0..=j1 {
        let p = I::point(j as f64 + 0.5) * pi();
        if p.hi >= x.lo && p.lo <= x.hi {
            let v = if j.rem_euclid(2) == 0 { 1.0 } else { -1.0 };
            res = res.hull(&I::point(v));
        }
    }
    clamp1(res)
}

/// Interval cosine.
pub fn cos(x: I) -> I {
    if !x.is_valid() {
        return x;
    }
    if x.lo == x.hi {
        return sincos_point(x.lo).1;
    }
    if !(x.lo.is_finite() && x.hi.is_finite()) || x.width() >= 6.28 {
        return I::new(-1.0, 1.0);
    }
    let mut res = sincos_point(x.lo).1.hull(&sincos_point(x.hi).1);
    let j0 = (x.lo / PI_LO).floor() as i64 - 1;
    let j1 = (x.hi / PI_LO).ceil() as i64 + 1;
    for j in j0..=j1 {
        let p = I::point(j as f64) * pi();
        if p.hi >= x.lo && p.lo <= x.hi {
            let v = if j.rem_euclid(2) == 0 { 1.0 } else { -1.0 };
            res = res.hull(&I::point(v));
        }
    }
    clamp1(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pi_enclosure() {
        // exact decimal expansion of the f64 PI_LO, compared with pi = 3.14159265358979323846264338...
        let s = format!("{:.30}", PI_LO);
        assert_eq!(s, "3.141592653589793115997963468544");
        let pi30 = "3.141592653589793238462643383279";
        assert!(s.as_str() < pi30);
        let h = format!("{:.30}", PI_HI);
        assert!(h.as_str() > pi30);
        assert_eq!(PI_LO.next_up(), PI_HI);
    }

    #[test]
    fn exact_values() {
        assert_eq!(sin(I::point(0.0)), I::point(0.0));
        assert_eq!(cos(I::point(0.0)), I::point(1.0));
    }

    #[test]
    fn agrees_with_libm() {
        // libm is not trusted, but it is accurate to ~1 ulp: enclosures must be tight and contain it
        let mut x = -20.0f64;
        while x < 20.0 {
            let (s, c) = sincos_point(x);
            let (ls, lc) = (x.sin(), x.cos());
            assert!(s.lo <= ls.next_up() && ls.next_down() <= s.hi, "{x} {s:?} {ls}");
            assert!(c.lo <= lc.next_up() && lc.next_down() <= c.hi, "{x} {c:?} {lc}");
            assert!(s.width() < 1e-14 && c.width() < 1e-14);
            x += 0.0137;
        }
    }

    #[test]
    fn interval_extrema() {
        let s = sin(I::new(1.0, 2.0));
        assert_eq!(s.hi, 1.0);
        assert!((s.lo - 1.0f64.sin()).abs() < 1e-14);
        let c = cos(I::new(-0.1, 0.2));
        assert_eq!(c.hi, 1.0);
        let c2 = cos(I::new(3.0, 3.3));
        assert_eq!(c2.lo, -1.0);
        let s2 = sin(I::new(-2.0, -1.0));
        assert_eq!(s2.lo, -1.0);
        // monotone piece: no extremum
        let s3 = sin(I::new(0.1, 0.2));
        assert!(s3.hi < 0.2 && s3.lo > 0.09);
    }
}
