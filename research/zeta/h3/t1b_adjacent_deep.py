#!/usr/bin/env python3
"""Explicit adversarial family for CGdL (periodic N=32): k off-line pairs at common depth y, spacing d (d=1/2 cancels the
alpha=1 edge term), the rest simple points on a unit lattice; then local optimisation of all positions/depths from there."""
import numpy as np
from scipy.optimize import minimize
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
d = np.load(SP+"cgdl_32.npz"); c0 = float(d['c0']); a = d['a']; N = len(a)+1; L = np.arange(1, N); OM = 2*np.pi*L/N
def rc(t_s, t_p, y_p):
    S = np.exp(1j*np.outer(t_s, OM)).sum(0) + (2*np.cosh(np.outer(y_p, OM))*np.exp(1j*np.outer(t_p, OM))).sum(0)
    return len(t_s)/N - c0 + np.abs(S)**2 @ a
worst = (1e9, None)
for k in (1, 2, 3, 4, 6, 8):
    for dd in (0.5, 0.75, 1.0, 1.5):
        for y in (0.2, 0.3, 0.5, 0.8, 1.2, 2.0):
            t_p = dd*np.arange(k); ns = N-2*k
            t_s = (k*dd-dd+1.0)+np.arange(ns)*((N-k*dd)/ns)
            v0 = rc(t_s, t_p, np.full(k, y))
            f = lambda z: rc(z[:ns], z[ns:ns+k], np.abs(z[ns+k:]))
            res = minimize(f, np.r_[t_s, t_p, np.full(k, y)], method='L-BFGS-B', options={'maxiter': 400})
            ymin = np.abs(res.x[ns+k:]).min() if k else 0
            if res.fun < worst[0]: worst = (res.fun, (k, dd, y), np.round(np.abs(res.x[ns+k:]), 3))
            if ymin > 0.05 and res.fun < 0.01: print(f"k={k} d={dd} y={y}: start {v0:+.3e} -> local min {res.fun:+.3e} depths {np.round(np.abs(res.x[ns+k:]),3)}")
print("worst local min over family:", worst)
