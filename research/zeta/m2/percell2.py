#!/usr/bin/env python3
"""m2: periodic-cell search (exact infinite periodic limit, see percell.py) for Psi_C (K5) with pairs forced to depth >= ymin;
reports Psi_C, Psi_MT per cell and per pair.  usage: percell2.py seed ntr ymin"""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import r_K5, r_MT
seed, ntr, ymin = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
rng = np.random.default_rng(seed)
def Psi(rf, d, x_on, m_on, x_p, y_p):
    n = int(np.ceil(d)-1); ks = np.arange(-n, n+1); al = ks/d; al = al[np.abs(al) < 1]
    A = (m_on[None, :]*np.exp(2j*np.pi*np.outer(al, x_on))).sum(1) + \
        (2*np.cosh(2*np.pi*np.outer(al, y_p))*np.exp(2j*np.pi*np.outer(al, x_p))).sum(1)
    T = 2*m_on.sum()-np.sum(m_on == 1)+4*len(x_p)
    return np.sum(rf(np.abs(al))*np.abs(A)**2)/d - T
out = []
for tr in range(ntr):
    P = int(rng.integers(1, 6)); no = int(rng.integers(0, 6)); m_on = rng.choice([1., 2., 3.], size=no, p=[.4, .4, .2])
    Mc = 2*P + m_on.sum(); d0 = rng.uniform(0.6, 1.6)*Mc/1.0
    def unpack(x):
        d = min(np.exp(x[0]), 30.0); xo = x[1:1+no]; xp = x[1+no:1+no+P]; yp = ymin + np.minimum(x[1+no+P:]**2, 3.0)
        return d, xo, xp, yp
    F = lambda x: Psi(r_K5, *unpack(x)[:1], unpack(x)[1], m_on, unpack(x)[2], unpack(x)[3])
    x0 = np.concatenate([[np.log(d0)], rng.uniform(0, d0, no), rng.uniform(0, d0, P), rng.uniform(0, 0.8, P)])
    try:
        r = minimize(F, x0, method="BFGS", options=dict(maxiter=3000, gtol=1e-9))
        r = minimize(F, r.x, method="Nelder-Mead", options=dict(maxiter=8000, xatol=1e-10, fatol=1e-13))
    except Exception: continue
    d, xo, xp, yp = unpack(r.x); pm = Psi(r_MT, d, xo, m_on, xp, yp)
    out.append((r.fun, pm, d, P, tuple(m_on.astype(int)), np.round(yp, 3)))
    if r.fun < 0: print("NEG", out[-1], flush=True)
out.sort(key=lambda o: o[0]/o[3])
print(f"ymin={ymin} ntr={ntr}: best per pair")
for o in out[:10]: print(f"PsiC={o[0]:+.5f} PsiMT={o[1]:+.5f} perpair={o[0]/o[3]:+.5f} d={o[2]:.4f} P={o[3]} on={o[4]} y={o[5]}")
