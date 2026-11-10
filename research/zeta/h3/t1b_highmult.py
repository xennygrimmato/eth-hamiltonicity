#!/usr/bin/env python3
"""High-multiplicity background test: does a multiplicity-m on-line zero next to a shallow pair make the pair beat the double?
Periodic CGdL certificate (cgdl_N.npz). delta(y) = s1/N - c0 + sum a|S|^2; config = pair at 0 (depth y), point of mult m at x,
simple points filling the rest on a near-uniform grid.  Prints min over x of delta(y)-delta(0) and delta(y) itself."""
import numpy as np, sys
from scipy.optimize import minimize_scalar
N = int(sys.argv[1]); SP = "/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/"
d = np.load(SP+f"cgdl_{N}.npz"); c0 = float(d['c0']); a = d['a']; L = np.arange(1, N); OM = 2*np.pi*L/N
def delta(y, m, x, ts):
    S = 2*np.cosh(OM*y) + m*np.exp(1j*OM*x) + np.exp(1j*np.outer(ts, OM)).sum(0)
    return len(ts)/N - c0 + np.abs(S)**2 @ a
for m in [1, 2, 4, 7, 10, 14]:
    k = N-2-m; ts = np.linspace(2.5, N-2.5, k)     # simple points away from the pair/cluster
    out = []
    for y in [0.02, 0.05, 0.1, 0.2]:
        best = min((delta(y, m, x, ts)-delta(0, m, x, ts), x) for x in np.linspace(0.3, 2.0, 341))
        out.append(f"y={y}: min_x [d(y)-d(0)]={best[0]:+.2e} at x={best[1]:.3f} (d(0)={delta(0,m,best[1],ts):+.2e})")
    print(f"m={m}: " + " | ".join(out), flush=True)
