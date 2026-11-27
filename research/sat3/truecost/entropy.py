#!/usr/bin/env python3
"""Entropy of the classes.  s(c) = lim ln #{partitions of m with Durfee square c sqrt(m)} / sqrt(m)
( = lim ln |Sigma(n, 2m)| / sqrt(m), n = c sqrt(m) ),  from the generating function q^(n^2)/(q;q)_n^2:
   s(c) = min_b [ b (1 - c^2) + (2/b) G(b c) ],   G(u) = int_0^u -ln(1 - e^-x) dx.
Maximum kappa0 = pi sqrt(2/3) at c* = sqrt(6) ln 2 / pi.  Also exact finite checks.
"""
import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
def G(u): return quad(lambda x: -np.log1p(-np.exp(-x)), 0, u)[0]
def s(c):
    if c >= 1: return 0.0
    f = lambda b: b * (1 - c * c) + 2 / b * G(b * c)
    r = minimize_scalar(f, bounds=(1e-3, 60), method='bounded')
    return r.fun
k0 = np.pi * np.sqrt(2 / 3); cs = np.sqrt(6) * np.log(2) / np.pi
if __name__ == '__main__':
    print(f"kappa0 = {k0:.6f}, c* = {cs:.6f}, s(c*) = {s(cs):.6f}")
    for c in [0.1, 0.2, 0.3, cs / np.sqrt(2), 0.45, cs, 0.6, 0.7, np.sqrt(2) * cs, 0.85, 0.95]:
        print(f"  c = {c:.4f}   s(c) = {s(c):.5f}   s/kappa0 = {s(c)/k0:.5f}")
    r = s(np.sqrt(2) * cs) / k0
    print(f"top-size sector at the middle term (T of size n1+n2, p = q): exponent ratio s(sqrt2 c*)/kappa0 = {r:.5f}")
