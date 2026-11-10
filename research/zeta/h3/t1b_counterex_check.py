#!/usr/bin/env python3
"""Verify the N=8 counterexample to 'every a>=0 certificate valid on real configs transfers to off-line pairs':
s1=0 configurations = 4 points of mass 2. On-line: grid search (step h) + local polish over 4 real points (translation fixed).
Off-line: 4 pairs with depths optimised. Compares min F = sum a_l |S_l|^2 (s1=0 so RC = F - c0)."""
import numpy as np, itertools
from scipy.optimize import minimize
a = np.load("/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/randcert_a_8_6.npy"); N = 8
L = np.arange(1, N); OM = 2*np.pi*L/N
def F(t, y):
    S = (2*np.cosh(np.outer(y, OM))*np.exp(1j*np.outer(t, OM))).sum(0); return float(np.abs(S)**2 @ a)
h = 0.05; g = np.arange(0, N, h); best = (1e9, None)
E = np.exp(1j*np.outer(g, OM))           # (G, N-1)
for i2 in range(len(g)):
    S12 = 2*(1+E[i2])                      # t1=0
    S = S12[None, None, :]+2*E[None, :, :]+2*E[:, None, :]   # (G,G,N-1) over (t3,t4)
    val = (np.abs(S)**2) @ a
    j = np.unravel_index(val.argmin(), val.shape)
    if val[j] < best[0]: best = (val[j], (0.0, g[i2], g[j[0]], g[j[1]]))
r = minimize(lambda z: F(np.r_[0, z], np.zeros(4)), np.array(best[1][1:]), method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-14, 'maxiter': 20000})
print("a =", np.array2string(a, precision=6))
print(f"on-line (4 doubles) grid min {best[0]:.6f} at {np.round(best[1],3)} ; polished {r.fun:.8f} at t={np.round(np.r_[0,r.x],4)}")
bp = (1e9, None); rng = np.random.default_rng(0)
for _ in range(400):
    z0 = np.r_[rng.uniform(0, N, 3), rng.uniform(0, 0.3, 4)]
    q = minimize(lambda z: F(np.r_[0, z[:3]], z[3:]), z0, method='L-BFGS-B', bounds=[(None, None)]*3+[(0, 1)]*4)
    if q.fun < bp[0]: bp = (q.fun, q.x)
print(f"off-line (4 pairs) min {bp[0]:.8f} at t={np.round(np.r_[0, bp[1][:3]],4)} depths={np.round(bp[1][3:],4)}")
print("difference (pairs - on-line):", bp[0]-r.fun)
