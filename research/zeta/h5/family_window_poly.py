#!/usr/bin/env python3
"""Explicit real-analytic (even polynomial) window for the family theorem, positive on [-lam/2, lam/2],
fitted to the QP optimum; R evaluated by Gauss-Legendre product quadrature split at the kinks |a-b| = 1."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from family_opt import optimise, Ft_LS
S = 0.47914534724162244; K = 1.5 / S; lam = 1.4
_, _, u, psi = optimise(lam, Ft_LS(K), n=400)
deg = 10
V = np.vander(u ** 2, deg // 2 + 1, increasing=True)
coef = np.linalg.lstsq(V, np.sqrt(psi / psi.max()), rcond=None)[0]   # fit p = sqrt(psi); window = p^2
p = lambda x: np.vander(np.atleast_1d(x) ** 2, deg // 2 + 1, increasing=True) @ coef
P = lambda x: p(x) ** 2
xs = np.linspace(-lam / 2, lam / 2, 20001); print("min of p=sqrt(window) on support:", p(xs).min())
def R_poly(K, cut=1.0, n=400):
    # integrate over u in [-lam/2,lam/2], v likewise, splitting v-range at u-1, u+1
    g, w = leggauss(n)
    A = lam / 2
    # outer nodes: split at u = +-(cut - A) where the inner breakpoints enter/leave the support
    obp = sorted(set([-A, A] + [b for b in (cut - A, A - cut) if -A < b < A]))
    U = np.concatenate([(h - l) / 2 * g + (h + l) / 2 for l, h in zip(obp[:-1], obp[1:])])
    WU = np.concatenate([(h - l) / 2 * w for l, h in zip(obp[:-1], obp[1:])])
    num1 = np.sum(WU * P(U) ** 2); den = np.sum(WU * P(U)) ** 2
    tot = 0.0
    for ui, wi in zip(U, WU):
        bps = sorted(set([-A, A] + [b for b in (ui - cut, ui + cut) if -A < b < A]))
        for lo, hi in zip(bps[:-1], bps[1:]):
            V_ = (hi - lo) / 2 * g + (hi + lo) / 2; WV = (hi - lo) / 2 * w
            d = np.abs(ui - V_)
            F = np.where(d <= cut, d, K * d)
            tot += wi * P(ui)[0] * np.sum(WV * F * P(V_))
    return (num1 + tot) / den
for n in [50, 100, 200]:
    R = R_poly(K, n=n); print('n=%d  K=%.4f lam=%.2f  R=%.7f  simple>=%.6f distinct>=%.6f' % (n, K, lam, R, 2 - R, (3 - R) / 2))
print('poly coefficients in u^2 (normalised):', np.array2string(coef, precision=6))
np.save('family_poly_coef.npy', coef)
