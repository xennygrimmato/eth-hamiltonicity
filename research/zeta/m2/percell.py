#!/usr/bin/env python3
"""m2: periodic-cell defect. For a cell of length d with objects (on-line mult m at x, or pair at x+-iy),
the N-fold repetition Z_N satisfies Phi(Z_N)/N -> Psi = (1/d) sum_{|k|<d} r(k/d) |A_k|^2 - T_cell,
A_k = sum_o w_o(k/d) e(k x_o/d), w = m (on-line) or 2cosh(2 pi alpha y) (pair)  [Fejer; needs r(1)=0].
Global multistart minimisation of Psi over d, positions, depths, for given object lists."""
import numpy as np, sys
from scipy.optimize import minimize
from cilib import r_K5, r_MT
kn = sys.argv[1] if len(sys.argv) > 1 else "K5"
eps = None if kn in ("K5", "MT") else float(kn[3:])
def rf(a):
    a = np.atleast_1d(a)
    if kn == "K5": return r_K5(a)
    if kn == "MT": return r_MT(a)
    return (1-eps)*r_MT(a)+eps*r_K5(a)
def Psi(d, x_on, m_on, x_p, y_p):
    n = int(np.ceil(d)-1)
    ks = np.arange(-n, n+1); al = ks/d
    al = al[np.abs(al) < 1]; ks = np.round(al*d).astype(int)
    rr = rf(np.abs(al))
    A = (m_on[None, :]*np.exp(2j*np.pi*np.outer(al, x_on))).sum(1) + \
        (2*np.cosh(2*np.pi*np.outer(al, y_p))*np.exp(2j*np.pi*np.outer(al, x_p))).sum(1)
    T = 2*m_on.sum()-np.sum(m_on == 1)+4*len(x_p)
    return np.sum(rr*np.abs(A)**2)/d - T
if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    types = []
    for P in range(1, 5):
        for ons in [(), (1,), (2,), (3,), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (1, 1, 1), (1, 1, 2), (4,), (1, 4)]:
            types.append((P, ons))
    res = []
    for P, ons in types:
        m_on = np.array(ons, float); best = (np.inf, None)
        Mcell = 2*P+m_on.sum()
        for tr in range(60):
            d0 = rng.uniform(0.5, 2*Mcell)
            x0 = np.concatenate([[np.log(d0)], rng.uniform(0, 1, len(ons)), rng.uniform(0, 1, P), rng.uniform(0, 1.5, P)])
            def F(x):
                d = np.exp(x[0]); xo = x[1:1+len(ons)]*d; xp = x[1+len(ons):1+len(ons)+P]*d; yp = np.abs(x[1+len(ons)+P:])
                return Psi(d, xo, m_on, xp, yp)
            r = minimize(F, x0, method="Nelder-Mead", options=dict(maxiter=20000, xatol=1e-10, fatol=1e-12))
            r = minimize(F, r.x, method="Nelder-Mead", options=dict(maxiter=20000, xatol=1e-12, fatol=1e-14))
            if r.fun < best[0]: best = (r.fun, r.x)
        x = best[1]; d = np.exp(x[0])
        res.append((best[0], P, ons, d, np.abs(x[1+len(ons)+P:])))
        print(f"P={P} on={ons} minPsi={best[0]:+.6f} d={d:.4f} y={np.round(np.abs(x[1+len(ons)+P:]),4)} xo={np.round(x[1:1+len(ons)]*d,4)} xp={np.round(x[1+len(ons):1+len(ons)+P]*d,4)}", flush=True)
