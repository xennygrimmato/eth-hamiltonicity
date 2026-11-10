#!/usr/bin/env python3
"""m2 attack 2: equal / forced depth. For each depth y and number of pairs p, minimise D over positions
(pairs at depth exactly y, or >= y if FREE), backgrounds of simples/doubles/triples. Report min D/p and ratio
to the pair self excess sx(y)=2K1(0)+2K1(2iy)-4.   usage: attack2.py KERNEL ntr [free]"""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import *
kname = sys.argv[1]; ntr = int(sys.argv[2]); FREE = len(sys.argv) > 3
ker = Kernel(r_K5, 240) if kname == "K5" else Kernel(r_MT, 240) if kname == "MT" else mixture(float(kname[3:]), 240)
rng = np.random.default_rng(7)
def sx(y): return 2*ker.K10 + 2*ker.K1(np.array([2j*y]))[0].real - 4
def opt(m_on, p, y, t_on0, t_p0):
    n1 = len(m_on); m_p = np.ones(p)
    if not FREE:
        def fg(x):
            v, g1, g2, g3 = defect_grad(ker, x[:n1], m_on, x[n1:], y*np.ones(p), m_p); return v, np.concatenate([g1, g2])
        res = minimize(fg, np.concatenate([t_on0, t_p0]), jac=True, method="L-BFGS-B", options=dict(maxiter=4000))
    else:
        def fg(x):
            v, g1, g2, g3 = defect_grad(ker, x[:n1], m_on, x[n1:n1+p], x[n1+p:], m_p); return v, np.concatenate([g1, g2, g3])
        res = minimize(fg, np.concatenate([t_on0, t_p0, y*np.ones(p)]), jac=True, method="L-BFGS-B",
                       bounds=[(None, None)]*(n1+p)+[(y, 5)]*p, options=dict(maxiter=4000))
    return res.fun, res.x
print(f"kernel {kname} value {ker.value:.6f} FREE={FREE}")
for y in [0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0]:
    s = sx(y); line = f"y={y:4.2f} sx={s:9.3e} |"
    for p in [1, 2, 3, 4, 6]:
        bestv = np.inf; bestc = None
        for tr in range(ntr):
            kind = tr % 5
            nb = int(rng.integers(0, 3*p+4))
            if kind == 0: m_on = np.ones(nb)
            elif kind == 1: m_on = 2*np.ones(nb)
            elif kind == 2: m_on = 3*np.ones(max(nb//2, 1))
            elif kind == 3: m_on = rng.choice([1., 2., 3.], size=nb)
            else: m_on = np.zeros(0)
            L = (len(m_on)+2*p)*rng.uniform(0.3, 1.0)
            if tr % 7 == 6:  # interleaved lattice
                d = rng.uniform(0.3, 1.0); t_p0 = 2*d*np.arange(p); m_on = rng.choice([1., 2., 3.])*np.ones(p+1); t_on0 = 2*d*np.arange(p+1)-d
            else:
                t_on0 = rng.uniform(0, L, len(m_on)); t_p0 = rng.uniform(0, L, p)
            v, x = opt(m_on, p, y, t_on0, t_p0)
            if v < bestv: bestv = v; bestc = (tuple(m_on.astype(int)), np.round(x, 3))
        line += f" p={p}: {bestv/p:+.4f} ({bestv/p/s:+.3f})"
        if bestv < 0: print("VIOLATION", y, p, bestv, bestc, flush=True)
    print(line, flush=True)
