#!/usr/bin/env python3
"""Deep pair + clustered on-line background: full periodic CGdL certificate (N given) reduced cost, optimised over
cluster positions; cluster of k1 simple/double points near the pair, remaining mass on a lattice far away."""
import numpy as np, sys
from scipy.optimize import minimize
SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
N = int(sys.argv[1]); d = np.load(SP+f"cgdl_{N}.npz"); c0 = float(d['c0']); a = d['a']; L = np.arange(1, N); OM = 2*np.pi*L/N
def rc(ts, ms, tp, yp):
    S = (ms[:, None]*np.exp(1j*np.outer(ts, OM))).sum(0) + 2*np.cosh(OM*yp)*np.exp(1j*OM*tp)
    s1 = (ms == 1).sum(); return s1/N - c0 + np.abs(S)**2 @ a
rng = np.random.default_rng(0)
for y in [0.8, 1.2, 1.6, 2.0, 2.5]:
    best = (1e18, None)
    for M in [2, 4, 8, 12, 16]:          # cluster mass (doubles) near the pair
        nd = M//2; rest = N-2-M
        for trial in range(6):
            xc = rng.choice([-1, 1], nd)*(0.6+0.15*rng.random(nd))
            far = N/2+np.arange(rest)-rest/2     # simple lattice far away
            ms = np.r_[2*np.ones(nd), np.ones(rest)]
            f = lambda z: rc(np.r_[z, far], ms, 0.0, y)
            r = minimize(f, xc, method='L-BFGS-B')
            if r.fun < best[0]: best = (r.fun, (M, np.round(np.sort(r.x), 3)))
    print(f"N={N} y={y}: min reduced cost {best[0]:+.4e}  cluster(mass, positions)={best[1]}", flush=True)
