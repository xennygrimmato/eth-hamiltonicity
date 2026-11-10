"""Shared certified constants and analytic bounds (all arb, rigorous upper/lower bounds)."""
from flint import arb, acb
from kern import *
from certlib import certify_positive
import math

def sup_abs_r(d, a, b, n=2000):
    a = arb(a); b = arb(b); m = arb(0)
    for i in range(n):
        B = ballx(a + (b - a) * i / n, a + (b - a) * (i + 1) / n)
        v = abs(r(B, d)).upper()
        if v > m: m = arb(v)
    return m

R = [sup_abs_r(d, 0, 1) for d in range(4)]          # sup_[0,1] |r^{(d)}|  (upper bounds)
RP1 = abs(r(arb(1), 1)); RPP1 = abs(r(arb(1), 2))     # |r'(1)|, |r''(1)|
_m = moments_r(1, acb(0), 4)
M2 = 2 * _m[2].real; M4 = 2 * _m[4].real; NORM_R1 = 2 * _m[0].real   # int_{-1}^1 a^2 r, a^4 r, r  (r1 >= 0)
K1DD0 = 4 * PI ** 2 * M2                                   # |K1''(0)|

def up(v):   # upper end as arb
    return arb(arb(v).upper())
def lo(v):
    return arb(arb(v).lower())

def kappa(d):
    """lower bound for min_{|u|<=d} K(u), valid for 0<=d<=0.75 (K decreasing there: cert_kernel.py)."""
    assert float(d) <= 0.75
    return lo(Kd(arb(d)))

def h_charge(g, kap):
    """packing charge bound h <= 8g if 2g<=kap else (2g+kap)^2/kap  (Lemma 4). g, kap arb (upper / lower)."""
    g = up(g)
    if 2 * g <= kap:
        return 8 * g
    return up((2 * g + kap) ** 2 / kap)

# ---------- tail bounds for |beta_y(x)| = |Re K1(x+iy) - K1(x)| ----------
def tail_coef_small(y):
    """(a,b) with |beta_y(x)| <= a/x^2 + b/x^3 for x>0 (Lemma 5(b)); y>=0 (upper end used)."""
    y = up(y); t = 2 * PI * y
    ch = t.cosh() - 1; sh = t.sinh()
    shc = (sh / t - 1) if float(y) > 0 else arb(0)
    phi1 = RP1 * ch
    phi2 = RPP1 * ch + 2 * RP1 * t * sh
    phi3 = R[3] * shc + 3 * R[2] * ch + 3 * R[1] * t * sh + R[0] * t * t * ch
    a = 2 * phi1 / (4 * PI ** 2)
    b = 2 * (phi2 + phi3) / (8 * PI ** 3)
    return up(a), up(b)

def tail_coef_large(y):
    """(a,b) with |beta_y(x)| <= a/x^2 + b/x^3 for x>0 (Lemma 5(c))."""
    y = up(y); t = 2 * PI * y
    c = t.cosh() + 1
    a = c * 2 * RP1 / (4 * PI ** 2)
    b = c * 2 * (RPP1 + R[3]) / (8 * PI ** 3)
    return up(a), up(b)

def tail_charge(a, b, X, ell, kap):
    """upper bound for sum_{k>=0} [8 g_k + 4 g_k^2/kap], g_k = a/x_k^2 + b/x_k^3, x_k = X + k ell  (decreasing).
    sum_k phi(x_k) <= phi(X) + (1/ell) int_X^inf phi."""
    X = arb(X); ell = arb(ell)
    g0 = a / X ** 2 + b / X ** 3
    S1 = g0 + (a / X + b / (2 * X ** 2)) / ell
    S2 = g0 ** 2 + (a * a / (3 * X ** 3) + a * b / (2 * X ** 4) + b * b / (5 * X ** 5)) / ell
    return up(8 * S1 + 4 * S2 / kap)
