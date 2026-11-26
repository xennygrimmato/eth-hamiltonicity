#!/usr/bin/env python3
"""hunch/law.py -- the trade-off law of the three-wire (matrix multiplication) triangle.

Inputs taken as given (unrefereed where marked):
  omega(x1,x2,x3) = (x1x2+x2x3+x3x1)^2/(4 x1x2x3) if no reciprocal thickness exceeds the sum of the other two,
                    else (sum of the two largest thicknesses)        [upper bound: published; equality: K-OA Lean claim]
  D*(a) = sum a - 1/sum(1/a)                                         [tripod principle, K-OA Prop. 8.1, first part]

Checks (all [N], random sampling plus closed forms):
  1. omega is homogeneous of degree 1, convex, hence subadditive: partial application
        omega(x) + omega(1-x) >= omega(1,1,1) = 9/4, equality only for x proportional to (1,1,1).
  2. label efficiency  eff(x) = 2(x1+x2+x3)/omega(x) = (cut bits removed, summed over the three one-party cuts)
     per label bit:  max = 8/3 at the square shape; a single wire gives 2; so at most 8/9 per cut per label bit.
  3. Legendre duality  omega(x) = max { sum_k c_k a_k : D*(a) <= 1 },  c_k = sum of the two thicknesses at site k.
  4. D* is convex and (8/9) hp <= D* <= hp (hp = a1+a2+a3 = half perimeter): the exchange rate
     kappa = (price of a hub bit)/(price of a pair bit across the diameter) of an equilateral triple is in [4/3, 3/2].
  5. the three numbers that get confused, for the triangle with thickness 1 on each wire (3 raw bits):
        one-cut terms (slice rank / flattening / Euclidean label floor): 2   -> 2/3
        all-cut terms (tensor rank, K-OA):                               9/4 -> 3/4
        trivial:                                                         3   -> 1
"""
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(1)


def omega(x):
    x = np.asarray(x, float)
    if np.min(x) <= 0:
        s = np.sort(x)
        return s[1] + s[2]
    u = 1.0 / x
    if np.max(u) >= np.sum(u) - np.max(u):       # reciprocal triangle inequality fails: collapsed regime
        s = np.sort(x)
        return s[1] + s[2]
    e2 = x[0] * x[1] + x[1] * x[2] + x[2] * x[0]
    return e2 * e2 / (4 * x[0] * x[1] * x[2])


def Dstar(a):
    a = np.asarray(a, float)
    if np.min(a) <= 0:
        return float(np.sum(a))
    return float(np.sum(a) - 1.0 / np.sum(1.0 / a))


def check1(n=200000):
    worst_conv = 0.0
    worst_pa = 1e9
    arg = None
    for _ in range(n):
        x = rng.random(3) * rng.choice([0.05, 1, 5])
        y = rng.random(3) * rng.choice([0.05, 1, 5])
        t = rng.random()
        gap = t * omega(x) + (1 - t) * omega(y) - omega(t * x + (1 - t) * y)
        worst_conv = min(worst_conv, gap)
        z = rng.random(3)
        tot = omega(z) + omega(1 - z)
        if tot < worst_pa:
            worst_pa, arg = tot, z
    print("1. convexity: min of [t w(x)+(1-t) w(y) - w(tx+(1-t)y)] over %d samples = %.3e (>= 0 expected)" % (n, worst_conv))
    print("   partial application: min of w(x)+w(1-x) = %.6f at x = %s   (9/4 = 2.25, attained on the diagonal)" % (worst_pa, np.round(arg, 3)))
    for s in (0.1, 0.5, 0.9):
        print("   diagonal s=%.1f: w(s,s,s)+w(1-s,1-s,1-s) = %.6f" % (s, omega([s] * 3) + omega([1 - s] * 3)))


def check2(n=200000):
    best, arg = 0, None
    for _ in range(n):
        x = rng.random(3) + 1e-9
        e = 2 * x.sum() / omega(x)
        if e > best:
            best, arg = e, x
    print("2. label efficiency 2*sum(x)/w(x): max over %d samples = %.6f at x ~ %s (8/3 = %.6f)" % (n, best, np.round(arg / arg.max(), 3), 8 / 3))
    print("   single wire (1,0,0): %.4f;  collapsed (1,1,1/2): %.4f;  square: %.4f" % (2 / omega([1, 0, 0]), 2 * 2.5 / omega([1, 1, .5]), 6 / omega([1, 1, 1])))


def check3(n=300):
    worst = 0
    for _ in range(n):
        x = rng.random(3) + 0.02
        c = np.array([x[1] + x[2], x[0] + x[2], x[0] + x[1]])  # site k sees the two wires other than wire k
        best = 0
        for _ in range(6):
            a0 = rng.random(3)
            f = lambda a: -(c @ np.abs(a)) / max(Dstar(np.abs(a)), 1e-12)
            r = minimize(f, a0, method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-12, maxiter=4000))
            best = max(best, -r.fun)
        worst = max(worst, abs(best - omega(x)) / omega(x))
    print("3. Legendre duality max{c.a : D*(a)<=1} = w(x): max relative error over %d shapes = %.2e" % (n, worst))


def check4(n=200000):
    lo, hi, conv = 9, 0, 0.0
    for _ in range(n):
        a = rng.random(3) + 1e-6
        b = rng.random(3) + 1e-6
        r = Dstar(a) / a.sum()
        lo, hi = min(lo, r), max(hi, r)
        t = rng.random()
        conv = min(conv, t * Dstar(a) + (1 - t) * Dstar(b) - Dstar(t * a + (1 - t) * b))
    print("4. D*/hp in [%.6f, %.6f] (8/9 = %.6f at equal arms; -> 1 when an arm -> 0);  convexity gap min = %.2e" % (lo, hi, 8 / 9, conv))
    print("   equilateral triple, pair distance delta = 2a: hub price per bit / pair price per bit = D/delta in [%.4f, %.4f]" % (Dstar([1, 1, 1]) / 2, 3 / 2))


def check5():
    print("5. triangle, 3 raw wire bits:  one-cut terms 2 (2/3);  all-cut terms 9/4 (3/4);  trivial 3 (1).")
    print("   ratio truth/Euclidean label floor = (9/4)/2 = %.4f" % (9 / 8))
    print("   for comparison (level values, 3-nets): pod floor/flat floor = %.4f (Delta_3: %.4f), cap/flat = %.4f"
          % (0.5 * np.sqrt(1.5) * np.sqrt(3), (2 / 3) * np.sqrt(3), np.sqrt(1.5)))


if __name__ == "__main__":
    check1(); check2(); check3(); check4(); check5()
