#!/usr/bin/env python3
"""One-body test (*) against lattice-like backgrounds of doubles x_j = j*s (j=+-1..+-J), the pair sitting at a lattice site,
optionally with free relaxation of the first few sites. Uses tabulated kernels from t1b_onebody2.py."""
import numpy as np
exec(open('t1b_onebody2.py').read().split("rng = np.random")[0])
def LHS(X, m, y, Gt):
    selfy = 2*((rr[inb]*np.cosh(2*w[inb]*y)).sum()-K10)
    D = X[:, None]-X[None, :]; KD = np.interp(D, xs, Kt); np.fill_diagonal(KD, 0)
    return selfy, selfy+4*(m*np.interp(X, xs, Gt)).sum()+m@KD@m
print(" y      self      min over s of LHS (J=14 doubles each side)   s*     LHS/self")
for y in [0.01, 0.05, 0.1, 0.15, 0.2, 0.3, 0.5, 0.8]:
    best = (1e9, 0); Gt = tab(rr[inb]*np.cosh(w[inb]*y), w[inb])[0]-K1t+Kt
    for s in np.linspace(0.85, 1.25, 401):
        X = np.r_[-s*np.arange(1, 15), s*np.arange(1, 15)]; m = 2*np.ones(len(X))
        se, v = LHS(X, m, y, Gt)
        if v < best[0]: best = (v, s)
    print(f" {y:4.2f}  {se:9.5f}   {best[0]:+.6f}   {best[1]:.3f}   {best[0]/se:+.4f}")
