//! Scalar trait and forward-mode automatic differentiation over intervals.
//!
//! A problem writes its function once, generically over `T: Scalar<N>`; it is then evaluated as
//!   * `I`        : natural interval extension,
//!   * `Jet1<N>`  : value + interval gradient,
//!   * `Jet2<N>`  : value + interval gradient + interval Hessian.
//! Each jet component encloses the corresponding derivative at every point of the box (chain rule
//! applied with interval enclosures of g, g', g'' of each elementary function over the enclosure of
//! its argument). sqrt of an argument whose enclosure touches 0 gives INVALID derivatives (sqrt is
//! not differentiable there), so AD-based tests then fail and the box is subdivided instead.

use crate::elem;
use crate::interval::{I, INVALID};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Scalar<const N: usize>:
    Copy + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> + Neg<Output = Self>
{
    fn cst(c: I) -> Self;
    fn cf(c: f64) -> Self {
        Self::cst(I::point(c))
    }
    fn sin(self) -> Self;
    fn cos(self) -> Self;
    fn sqrt(self) -> Self;
    fn sqr(self) -> Self;
    /// |x|. Jet2 (only ever evaluated over a box): if the value enclosure over the box is
    /// sign-definite, |x| coincides on the box with the smooth function +-x and is differentiated as
    /// such (all leaf tests only use the function on the box); otherwise INVALID. Jet1 (also used at
    /// single points): +-dx if the value is strictly of one sign, otherwise INVALID.
    fn abs(self) -> Self;
    /// Enclosure of the value.
    fn val(&self) -> I;
    /// Value and (sin, cos) at once (saves work for jets).
    fn sincos(self) -> (Self, Self) {
        (self.sin(), self.cos())
    }
}

impl<const N: usize> Scalar<N> for I {
    #[inline]
    fn cst(c: I) -> I {
        c
    }
    #[inline]
    fn sin(self) -> I {
        elem::sin(self)
    }
    #[inline]
    fn cos(self) -> I {
        elem::cos(self)
    }
    #[inline]
    fn sqrt(self) -> I {
        I::sqrt(&self)
    }
    #[inline]
    fn sqr(self) -> I {
        I::sqr(&self)
    }
    #[inline]
    fn abs(self) -> I {
        I::abs(&self)
    }
    #[inline]
    fn val(&self) -> I {
        *self
    }
}

// ---------------------------------------------------------------- Jet1

#[derive(Clone, Copy, Debug)]
pub struct Jet1<const N: usize> {
    pub v: I,
    pub d: [I; N],
}

impl<const N: usize> Jet1<N> {
    pub fn var(x: I, k: usize) -> Self {
        let mut d = [I::point(0.0); N];
        d[k] = I::point(1.0);
        Jet1 { v: x, d }
    }
    #[inline]
    fn chain(self, g: I, g1: I) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = g1 * d[i];
        }
        Jet1 { v: g, d }
    }
}

impl<const N: usize> Add for Jet1<N> {
    type Output = Self;
    #[inline]
    fn add(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = d[i] + o.d[i];
        }
        Jet1 { v: self.v + o.v, d }
    }
}
impl<const N: usize> Sub for Jet1<N> {
    type Output = Self;
    #[inline]
    fn sub(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = d[i] - o.d[i];
        }
        Jet1 { v: self.v - o.v, d }
    }
}
impl<const N: usize> Neg for Jet1<N> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = -d[i];
        }
        Jet1 { v: -self.v, d }
    }
}
impl<const N: usize> Mul for Jet1<N> {
    type Output = Self;
    #[inline]
    fn mul(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.d[i] * o.v + self.v * o.d[i];
        }
        Jet1 { v: self.v * o.v, d }
    }
}
impl<const N: usize> Div for Jet1<N> {
    type Output = Self;
    #[inline]
    fn div(self, o: Self) -> Self {
        let r = o.v.recip();
        let rec = o.chain(r, -(I::sqr(&r)));
        self * rec
    }
}

impl<const N: usize> Scalar<N> for Jet1<N> {
    fn cst(c: I) -> Self {
        Jet1 { v: c, d: [I::point(0.0); N] }
    }
    fn sin(self) -> Self {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        self.chain(s, c)
    }
    fn cos(self) -> Self {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        self.chain(c, -s)
    }
    fn sincos(self) -> (Self, Self) {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        (self.chain(s, c), self.chain(c, -s))
    }
    fn sqrt(self) -> Self {
        let r = I::sqrt(&self.v);
        if !r.is_valid() || r.lo <= 0.0 {
            return Jet1 { v: r, d: [INVALID; N] };
        }
        let g1 = I::point(0.5) / r;
        self.chain(r, g1)
    }
    fn sqr(self) -> Self {
        let g1 = self.v * I::point(2.0);
        self.chain(I::sqr(&self.v), g1)
    }
    fn abs(self) -> Self {
        // strict tests: at a point where the value may be 0 the derivative is INVALID. (A Clarke
        // generalised-gradient enclosure [-1,1]*dx would be valid via Lebourg's mean-value theorem;
        // it is deliberately not used, to keep non-smooth analysis out of the trust base.)
        if self.v.is_valid() && self.v.lo > 0.0 {
            self
        } else if self.v.is_valid() && self.v.hi < 0.0 {
            -self
        } else {
            Jet1 { v: I::abs(&self.v), d: [INVALID; N] }
        }
    }
    fn val(&self) -> I {
        self.v
    }
}

// ---------------------------------------------------------------- Jet2

#[derive(Clone, Copy, Debug)]
pub struct Jet2<const N: usize> {
    pub v: I,
    pub d: [I; N],
    /// symmetric; only h[i][j] with i <= j is maintained, the lower triangle is mirrored on output
    pub h: [[I; N]; N],
}

impl<const N: usize> Jet2<N> {
    pub fn var(x: I, k: usize) -> Self {
        let mut d = [I::point(0.0); N];
        d[k] = I::point(1.0);
        Jet2 { v: x, d, h: [[I::point(0.0); N]; N] }
    }
    #[inline]
    fn chain(self, g: I, g1: I, g2: I) -> Self {
        let mut d = self.d;
        let mut h = self.h;
        for i in 0..N {
            for j in i..N {
                h[i][j] = g2 * (self.d[i] * self.d[j]) + g1 * self.h[i][j];
            }
        }
        for i in 0..N {
            d[i] = g1 * self.d[i];
        }
        Jet2 { v: g, d, h }
    }
    /// Full symmetric Hessian.
    pub fn hessian(&self) -> [[I; N]; N] {
        let mut h = self.h;
        for i in 0..N {
            for j in 0..i {
                h[i][j] = h[j][i];
            }
        }
        h
    }
}

impl<const N: usize> Add for Jet2<N> {
    type Output = Self;
    #[inline]
    fn add(self, o: Self) -> Self {
        let mut r = self;
        r.v = self.v + o.v;
        for i in 0..N {
            r.d[i] = self.d[i] + o.d[i];
            for j in i..N {
                r.h[i][j] = self.h[i][j] + o.h[i][j];
            }
        }
        r
    }
}
impl<const N: usize> Sub for Jet2<N> {
    type Output = Self;
    #[inline]
    fn sub(self, o: Self) -> Self {
        let mut r = self;
        r.v = self.v - o.v;
        for i in 0..N {
            r.d[i] = self.d[i] - o.d[i];
            for j in i..N {
                r.h[i][j] = self.h[i][j] - o.h[i][j];
            }
        }
        r
    }
}
impl<const N: usize> Neg for Jet2<N> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        let mut r = self;
        r.v = -self.v;
        for i in 0..N {
            r.d[i] = -self.d[i];
            for j in i..N {
                r.h[i][j] = -self.h[i][j];
            }
        }
        r
    }
}
impl<const N: usize> Mul for Jet2<N> {
    type Output = Self;
    #[inline]
    fn mul(self, o: Self) -> Self {
        let mut r = self;
        r.v = self.v * o.v;
        for i in 0..N {
            r.d[i] = self.d[i] * o.v + self.v * o.d[i];
            for j in i..N {
                r.h[i][j] = self.h[i][j] * o.v
                    + self.v * o.h[i][j]
                    + self.d[i] * o.d[j]
                    + self.d[j] * o.d[i];
            }
        }
        r
    }
}
impl<const N: usize> Div for Jet2<N> {
    type Output = Self;
    #[inline]
    fn div(self, o: Self) -> Self {
        let r = o.v.recip();
        let r2 = I::sqr(&r);
        let rec = o.chain(r, -r2, I::point(2.0) * r2 * r);
        self * rec
    }
}

impl<const N: usize> Scalar<N> for Jet2<N> {
    fn cst(c: I) -> Self {
        Jet2 { v: c, d: [I::point(0.0); N], h: [[I::point(0.0); N]; N] }
    }
    fn sin(self) -> Self {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        self.chain(s, c, -s)
    }
    fn cos(self) -> Self {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        self.chain(c, -s, -c)
    }
    fn sincos(self) -> (Self, Self) {
        let (s, c) = (elem::sin(self.v), elem::cos(self.v));
        (self.chain(s, c, -s), self.chain(c, -s, -c))
    }
    fn sqrt(self) -> Self {
        let r = I::sqrt(&self.v);
        if !r.is_valid() || r.lo <= 0.0 {
            return Jet2 { v: r, d: [INVALID; N], h: [[INVALID; N]; N] };
        }
        let g1 = I::point(0.5) / r;
        let g2 = -(I::point(0.25) / (r * self.v));
        self.chain(r, g1, g2)
    }
    fn sqr(self) -> Self {
        let g1 = self.v * I::point(2.0);
        self.chain(I::sqr(&self.v), g1, I::point(2.0))
    }
    fn abs(self) -> Self {
        if self.v.is_valid() && self.v.lo >= 0.0 {
            self
        } else if self.v.is_valid() && self.v.hi <= 0.0 {
            -self
        } else {
            Jet2 { v: I::abs(&self.v), d: [INVALID; N], h: [[INVALID; N]; N] }
        }
    }
    fn val(&self) -> I {
        self.v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f<T: Scalar<2>>(x: &[T; 2]) -> T {
        // f = sin(x) * sqrt(1 + y^2) / (2 + cos(x*y))
        (x[0].sin() * (T::cf(1.0) + x[1].sqr()).sqrt()) / (T::cf(2.0) + (x[0] * x[1]).cos())
    }

    #[test]
    fn derivatives_contain_finite_differences() {
        let (a, b) = (0.7f64, -0.4f64);
        let j = f(&[Jet2::<2>::var(I::point(a), 0), Jet2::var(I::point(b), 1)]);
        let g = |x: f64, y: f64| (x.sin() * (1.0 + y * y).sqrt()) / (2.0 + (x * y).cos());
        let h = 1e-5;
        let gx = (g(a + h, b) - g(a - h, b)) / (2.0 * h);
        let gy = (g(a, b + h) - g(a, b - h)) / (2.0 * h);
        assert!((j.d[0].mid() - gx).abs() < 1e-8 && (j.d[1].mid() - gy).abs() < 1e-8);
        let gxy = (g(a + h, b + h) - g(a + h, b - h) - g(a - h, b + h) + g(a - h, b - h)) / (4.0 * h * h);
        let hh = j.hessian();
        assert!((hh[0][1].mid() - gxy).abs() < 1e-4, "{:?} {}", hh[0][1], gxy);
        let gxx = (g(a + h, b) - 2.0 * g(a, b) + g(a - h, b)) / (h * h);
        assert!((hh[0][0].mid() - gxx).abs() < 1e-4);
        // box enclosure contains point values
        let bx = [I::new(0.6, 0.8), I::new(-0.5, -0.3)];
        let jb = f(&[Jet2::<2>::var(bx[0], 0), Jet2::var(bx[1], 1)]);
        assert!(jb.v.contains(g(a, b)) && jb.d[0].contains(gx) && jb.hessian()[0][0].contains(gxx));
    }
}
