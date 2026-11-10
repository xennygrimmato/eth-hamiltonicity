#!/usr/bin/env python3
"""m2 attack 1: random-structure multistart L-BFGS-B on the continuum defect D(X) (cilib).
usage: attack1.py KERNEL(K5|MT|mixE) seed ntrials"""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import *

kname = sys.argv[1]; seed = int(sys.argv[2]); ntr = int(sys.argv[3])
ker = Kernel(r_K5, 240) if kname == "K5" else Kernel(r_MT, 240) if kname == "MT" else mixture(float(kname[3:]), 240)
rng = np.random.default_rng(seed)

def run(m_on, m_p, t_on0, t_p0, y_p0, ymin=0.0):
    n1, n2 = len(m_on), len(m_p)
    def fg(x):
        t_on = x[:n1]; t_p = x[n1:n1+n2]; y_p = x[n1+n2:]
        v, g1, g2, g3 = defect_grad(ker, t_on, m_on, t_p, y_p, m_p)
        return v, np.concatenate([g1, g2, g3])
    x0 = np.concatenate([t_on0, t_p0, y_p0])
    bnds = [(None, None)]*(n1+n2) + [(ymin, 4.0)]*n2
    res = minimize(fg, x0, jac=True, method="L-BFGS-B", bounds=bnds, options=dict(maxiter=3000))
    return res.fun, res.x

best = []
for trial in range(ntr):
    kind = rng.integers(0, 6)
    npairs = int(rng.integers(1, 9))
    if kind == 0:   # pairs + simples, random
        m_on = np.ones(int(rng.integers(0, 12)))
    elif kind == 1:  # pairs + doubles
        m_on = 2*np.ones(int(rng.integers(0, 10)))
    elif kind == 2:  # pairs + triples
        m_on = 3*np.ones(int(rng.integers(1, 8)))
    elif kind == 3:  # mixture
        m_on = rng.choice([1, 2, 3, 4], size=int(rng.integers(1, 14)), p=[.4, .35, .2, .05]).astype(float)
    elif kind == 4:  # lattice: pairs at even sites, on-line at odd sites (Fabbian-type)
        mo = rng.choice([1, 2, 3]); d = rng.uniform(0.4, 1.2)
        m_on = mo*np.ones(npairs+1)
    else:            # cluster: pairs only
        m_on = np.zeros(0)
    m_p = np.ones(npairs)
    n1 = len(m_on); L = (n1+2*npairs)*rng.uniform(0.5, 1.1)
    if kind == 4:
        t_p0 = d*2*np.arange(npairs); t_on0 = d*(2*np.arange(n1)-1)
        y0 = rng.uniform(0.05, 1.0)*np.ones(npairs)
    else:
        t_on0 = rng.uniform(0, L, n1); t_p0 = rng.uniform(0, L, npairs)
        y0 = rng.uniform(0.0, 1.2, npairs)
    ymin = 0.0 if rng.random() < 0.5 else rng.uniform(0.05, 0.6)
    v, x = run(m_on, m_p, t_on0, t_p0, y0, ymin)
    yp = x[n1+npairs:]
    best.append((v, kind, ymin, tuple(m_on), np.round(np.sort(yp), 3)))
    if v < 0.05:
        print(f"trial {trial} kind {kind} D={v:+.5f} ymin={ymin:.2f} m_on={m_on} y={np.round(yp,3)}", flush=True)
best.sort(key=lambda b: b[0])
print("== best 10 ==")
for b in best[:10]: print(f"D={b[0]:+.6f} kind={b[1]} ymin={b[2]:.3f} m_on={b[3]} y={b[4]}")
# with forced depth: per-kind min
