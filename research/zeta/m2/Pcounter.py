#!/usr/bin/env python3
"""m2: Conjecture P (Delta_P >= 0) is FALSE: deep pair at 0 + n near-real pairs stacked near the deepest lobe of beta_y.
Also evaluates P' = Delta_P + 4 sum_{p!=q} K(x_p-x_q) (= Phi(pairs) - OB) on the same configurations."""
import numpy as np
from cilib import *
C = Kernel(r_K5, 300); a, W = C.a, C.W
# K(x) = int_R r cos: use r on [0,1.5]
xg, wg = np.polynomial.legendre.leggauss(400); aa = 0.75*xg+0.75; ww = 0.75*wg; ra = r_K5(aa)
K = lambda x: 2*np.sum(ww*ra*np.cos(2*np.pi*np.outer(np.atleast_1d(x), aa)), 1)
def DeltaP(t, y):
    E = np.exp(2j*np.pi*np.outer(a, t)); Ch = np.cosh(2*np.pi*np.outer(a, y))
    return 4*np.sum(W*(np.abs((Ch*E).sum(1))**2-np.abs(E.sum(1))**2))
for y0 in (0.3, 0.5, 1.0):
    xs = np.linspace(0.3, 3, 2701)
    beta = (W[None, :]*(np.cosh(2*np.pi*a*y0)-1)[None, :]*np.cos(2*np.pi*np.outer(xs, a))).sum(1)
    xs_ = xs[beta.argmin()]
    for n in (1, 2, 4, 8):
        t = np.concatenate([[0.0], xs_+1e-3*np.arange(n)]); y = np.concatenate([[y0], 1e-3*np.ones(n)])
        dp = DeltaP(t, y); D = t[:, None]-t[None, :]; kk = K(D.ravel()).reshape(D.shape); np.fill_diagonal(kk, 0)
        print(f"y0={y0} x*={xs_:.3f} beta*={beta.min():+.3e} n={n}: Delta_P={dp:+.4e}  P'={dp+4*kk.sum():+.4e}")
