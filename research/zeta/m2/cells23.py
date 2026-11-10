#!/usr/bin/env python3
"""m2: periodic cells with period d in (2,3] (in-band frequencies 0, 1/d, 2/d). Cells of mass M>=6 and cells with
one pair + on-line mass <=2, or two pairs only, are settled [R] (multi_pair.md sec 6). Remaining types:
{P,3}, {P,2,1}, {P,P,1}. Global grid + polish of Psi over (d, depths, phases).  usage: cells23.py KERNEL"""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import r_K5, r_MT
kn = sys.argv[1] if len(sys.argv) > 1 else "K5"
rf = r_K5 if kn == "K5" else r_MT if kn == "MT" else (lambda a, e=float(kn[3:]): (1-e)*r_MT(a)+e*r_K5(a))
r0 = rf(np.array([0.0]))[0]
def Psi(d, objs):
    """objs: list of (kind, x, m_or_y)"""
    tot = r0*sum((2 if k == 'P' else v) for k, x, v in objs)**2; T = 0
    for k, x, v in objs: T += 4 if k == 'P' else (2*v - (v == 1))
    for kk in (1, 2):
        al = kk/d
        if al >= 1: continue
        A = sum((2*np.cosh(2*np.pi*al*v) if k == 'P' else v)*np.exp(2j*np.pi*al*x) for k, x, v in objs)
        tot += 2*rf(np.array([al]))[0]*abs(A)**2
    return tot/d - T
types = {
 "P,3":   lambda p: [('P', 0, p[1]), ('R', p[2], 3)],
 "P,2,1": lambda p: [('P', 0, p[1]), ('R', p[2], 2), ('R', p[3], 1)],
 "P,P,1": lambda p: [('P', 0, p[1]), ('P', p[2], p[3]), ('R', p[4], 1)],
 "P,1,1,1": lambda p: [('P', 0, p[1]), ('R', p[2], 1), ('R', p[3], 1), ('R', p[4], 1)],
}
nps = {"P,3": 3, "P,2,1": 4, "P,P,1": 5, "P,1,1,1": 5}
rng = np.random.default_rng(0)
for name, mk in types.items():
    best = (np.inf, None)
    for tr in range(400):
        p0 = np.concatenate([[rng.uniform(2.0, 3.0), rng.uniform(0, 1.0)], rng.uniform(0, 3, nps[name]-1)])
        if name == "P,P,1": p0[3] = rng.uniform(0, 1.0)
        def F(p):
            d = 2+1/(1+np.exp(-p[0])) if False else np.clip(p[0], 2.0, 3.0)
            q = p.copy(); q[1] = abs(q[1]);
            if name == "P,P,1": q[3] = abs(q[3])
            return Psi(d, mk(q))
        r = minimize(F, p0, method="Nelder-Mead", options=dict(maxiter=6000, xatol=1e-10, fatol=1e-12))
        if r.fun < best[0]: best = (r.fun, r.x)
    print(f"{kn} type {{{name}}}: min Psi = {best[0]:+.6f} at d={np.clip(best[1][0],2,3):.4f} params={np.round(best[1][1:],4)}", flush=True)
