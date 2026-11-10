#!/usr/bin/env python3
"""m2: numerical tau = sup_Z (-Phi_C(Z))/Phi_MT(Z), C = h3's K5 kernel.
Minimise Phi_C + lam*Phi_MT over finite configurations from structured + random starts (L-BFGS-B, analytic grad);
report min Phi_C, Phi_MT at the minimiser and the ratio.  usage: tau_search.py seed ntr lam [ymin]"""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import *
seed, ntr, lam = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
YMIN = float(sys.argv[4]) if len(sys.argv) > 4 else 0.0
C = Kernel(r_K5, 260); M = Kernel(r_MT, 260)
J = Kernel(lambda a: r_K5(a)+lam*r_MT(a), 260)   # Phi_J = Phi_C + lam Phi_MT + lam*T (target counted once) -> fix below
rng = np.random.default_rng(seed)
def phiJ(x, m_on, m_p, n1, n2):
    v, g1, g2, g3 = defect_grad(J, x[:n1], m_on, x[n1:n1+n2], x[n1+n2:], m_p)
    T = target(m_on, m_p)
    return v - lam*T, np.concatenate([g1, g2, g3])   # = Phi_C + lam*Phi_MT
def starts():
    k = rng.integers(0, 8); P = int(rng.integers(1, 10)); y = rng.uniform(0.05, 1.5)
    if k == 0:   # comb of pairs, spacing ~1, with interleaved/defect on-line points
        tp = np.arange(P)*rng.uniform(0.9, 1.1); m = rng.choice([1., 2., 3.], size=int(rng.integers(0, 4)))
        to = rng.uniform(-1, P, len(m)); yp = y*np.ones(P)
    elif k == 1:  # Fabbian integer-triple chain: triples at odd, pairs at even, y*=0.3063
        tp = 2.0*np.arange(P); to = 2.0*np.arange(P)+1; m = 3*np.ones(P); yp = (0.3063+rng.normal(0, .05))*np.ones(P)
    elif k == 2:  # one pair + doubles at +-r (Thm 4.13)
        P = 1; tp = np.zeros(1); r = rng.uniform(0.8, 2.2, int(rng.integers(1, 3))); to = np.concatenate([r, -r]); m = 2*np.ones(len(to)); yp = np.array([rng.uniform(.02, .4)])
    elif k == 3:  # doubles at spacing 2 (tight real config), some turned into pairs
        n = int(rng.integers(3, 12)); sites = 2.0*np.arange(n); sel = rng.random(n) < 0.4; sel[n//2] = True
        tp = sites[sel]; to = sites[~sel]; m = 2*np.ones(len(to)); yp = rng.uniform(0.02, 0.6, len(tp)); P = len(tp)
    elif k == 4:  # cluster of deep pairs + shallow mass
        tp = rng.normal(0, 0.8, P); yp = rng.uniform(0.3, 1.5, P); m = rng.choice([1., 2., 3.], size=int(rng.integers(0, 2*P+3))); to = rng.uniform(-2, 2, len(m))
    elif k == 5:  # mixed depths, random
        L = 3*P; tp = rng.uniform(0, L, P); yp = rng.uniform(0, 1.2, P); m = rng.choice([1., 2., 3.], size=int(rng.integers(0, 3*P))); to = rng.uniform(0, L, len(m))
    elif k == 6:  # chain pairs at odd sites, simples at even (fractional-chain shape, integer mass)
        n = P; to = 2.0*np.arange(n+1); m = rng.choice([1., 2.])*np.ones(n+1); tp = 2.0*np.arange(n)+1; yp = y*np.ones(n)
    else:         # pairs only, two depths
        tp = rng.uniform(0, 1.5*P, P); yp = np.where(rng.random(P) < .5, y, rng.uniform(0, 0.3)); m = np.zeros(0); to = np.zeros(0)
    return k, np.asarray(to, float), np.asarray(m, float), np.asarray(tp, float), np.maximum(np.asarray(yp, float), YMIN)
rows = []
for tr in range(ntr):
    k, to, m, tp, yp = starts(); n1, n2 = len(to), len(tp); mp = np.ones(n2)
    x0 = np.concatenate([to, tp, yp])
    res = minimize(phiJ, x0, args=(m, mp, n1, n2), jac=True, method="L-BFGS-B",
                   bounds=[(None, None)]*(n1+n2)+[(YMIN, 4)]*n2, options=dict(maxiter=5000))
    x = res.x; pc = defect(C, x[:n1], m, x[n1:n1+n2], x[n1+n2:], mp); pm = defect(M, x[:n1], m, x[n1:n1+n2], x[n1+n2:], mp)
    rows.append((pc, pm, k, m, x, n1, n2))
    if pc < 0: print(f"NEG Phi_C={pc:+.3e} Phi_MT={pm:.3e} ratio={-pc/pm:.3f} kind={k} m={m} y={np.round(x[n1+n2:],3)}", flush=True)
print(f"lam={lam} ymin={YMIN} ntr={ntr}; min Phi_C/pair, then min ratio Phi_C/Phi_MT")
rows.sort(key=lambda r: r[0]/max(r[6], 1))
for pc, pm, k, m, x, n1, n2 in rows[:5]:
    print(f"Phi_C={pc:+.5f} Phi_MT={pm:+.5f} kind={k} n_on={n1} pairs={n2} m={m.astype(int)} y={np.round(x[n1+n2:],3)}")
rows.sort(key=lambda r: r[0]/r[1] if r[1] > 1e-9 else 1e9)
for pc, pm, k, m, x, n1, n2 in rows[:5]:
    print(f"Phi_C={pc:+.5f} Phi_MT={pm:+.5f} kind={k} n_on={n1} pairs={n2} m={m.astype(int)} y={np.round(x[n1+n2:],3)}")
