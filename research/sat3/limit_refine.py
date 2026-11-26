#!/usr/bin/env python3
"""Local refinement of the limit problem starting from the clustered-subgroup tripod (Phi = 27/8)."""
import sys, numpy as np
from scipy.optimize import minimize
from limitnet import phi, group
name = sys.argv[1]; idx = [int(t) for t in sys.argv[2].split(',')]  # elements of the subgroup A
m, sub = group(name)
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
arms = np.zeros((3, m), dtype=int); rho = np.zeros((3, m))
for k in range(3):
    for q in idx:
        arms[k, q] = k + 1; rho[k, q] = 1.0
cur = phi(arms, rho, m, sub); print("start", cur, flush=True)
best = cur
for trial in range(40):
    a2 = arms.copy(); r2 = rho + 0.3 * rng.random(rho.shape) * (rng.random(rho.shape) < 0.3)
    for k in range(3):
        for q in range(m):
            if rng.random() < 0.15: a2[k, q] = rng.integers(0, 7)
    f = lambda x: -phi(a2, np.abs(x.reshape(3, m)), m, sub)
    res = minimize(f, r2.ravel(), method='Powell', options=dict(maxiter=3000, xtol=1e-6, ftol=1e-9))
    v = -res.fun
    if v > best + 1e-7:
        best = v; print("improved", trial, v, "\n", a2, "\n", np.round(np.abs(res.x.reshape(3, m)), 3), flush=True)
print("best", best)
