#!/usr/bin/env python3
"""m2: is the pair-only depth excess Delta_P = int r1 (|sum 2c_p e_p|^2 - |sum 2 e_p|^2) >= 0 for all pair sets?
(it is for equal depths and for two pairs).  Multistart minimisation of Delta_P / sum_p self_p."""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import *
C = Kernel(r_K5, 200); a = C.a; W = C.W
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
def dP(x, P):
    t = x[:P]; y = np.abs(x[P:])
    E = np.exp(2j*np.pi*np.outer(a, t)); Ch = np.cosh(2*np.pi*np.outer(a, y))
    v = np.sum(W*(np.abs((2*Ch*E).sum(1))**2 - np.abs((2*E).sum(1))**2))
    selfs = np.sum(W[:, None]*4*(Ch**2-1))
    return v/selfs
best = 1e9
for tr in range(int(sys.argv[2]) if len(sys.argv) > 2 else 200):
    P = int(rng.integers(3, 9)); x0 = np.concatenate([rng.uniform(0, P, P), rng.uniform(0, 1.5, P)])
    r = minimize(dP, x0, args=(P,), method="L-BFGS-B", bounds=[(None,None)]*P+[(0,2)]*P, options=dict(maxiter=3000))
    if r.fun < best: best = r.fun; print(f"P={P} min Delta_P/sum self = {r.fun:+.4e} y={np.round(np.abs(r.x[P:]),3)} t={np.round(np.sort(r.x[:P]),3)}", flush=True)
