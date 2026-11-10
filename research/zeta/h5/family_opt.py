#!/usr/bin/env python3
"""T3 (h5): window optimisation for the family-average rank-trace certificate.
Certificate: proportion (simple & on line) >= 2 - R(psi), distinct >= (3 - R)/2, with
  R(psi) = [ int psi^2 + iint Ft(|u-v|) psi(u) psi(v) ] / (int psi)^2,
psi >= 0 even on [-lam/2, lam/2] (units of log Q), and Ft an upper bound for the
(off-delta) family form factor:  Ft(a) = a on [0,1],  K*a on (1, lam]   (K = large-sieve ratio),
or Ft(a) = min(a,1) (GRH, CLLR Thm 2).  Checks: lam=1 gives MT 1/c1* = 1.32750.
"""
import numpy as np
from scipy.optimize import minimize

def R_of(psi, u, h, Ft):
    D = np.abs(u[:, None] - u[None, :])
    F = Ft(D)
    np.fill_diagonal(F, Ft(np.array([h / 3.0]))[0])  # cell self-average of |u-v| ~ h/3
    num = h * np.sum(psi ** 2) + h * h * psi @ F @ psi
    return num / (h * np.sum(psi)) ** 2

def optimise(lam, Ft, n=600):
    h = lam / n
    u = -lam / 2 + h * (np.arange(n) + 0.5)
    D = np.abs(u[:, None] - u[None, :]); F = Ft(D)
    np.fill_diagonal(F, Ft(np.array([h / 3.0]))[0])
    M = h * np.eye(n) + h * h * F
    act = np.ones(n, bool)          # active-set: min p^T M p, sum p = const, p >= 0
    for _ in range(n):
        p = np.zeros(n); p[act] = np.linalg.solve(M[np.ix_(act, act)], np.ones(act.sum()))
        if (p[act] >= -1e-14).all(): break
        act &= p > 0
    psi = np.maximum(p, 0)
    flat = R_of(np.ones(n), u, h, Ft)
    return R_of(psi, u, h, Ft), flat, u, psi

def Ft_LS(K):
    return lambda a: np.where(a <= 1, a, K * a)

def Ft_GRH(a):
    return np.minimum(a, 1.0)

if __name__ == '__main__':
    S = 0.47914534724162244          # prod_p (1 - p^-2 - p^-3)
    Kc = 2 / S                       # classical large sieve (Q^2 + N) / (#harmonics), q <= Q, weights q/phi(q)
    cMTinv = 0.5 + np.cos(2 ** -0.5) / np.sin(2 ** -0.5) / 2 ** 0.5
    print('check MT: 1/c1* =', cMTinv, ' 2-1/c1* =', 2 - cMTinv)
    Kmv = 1.5 / S                    # Montgomery-Vaughan weighted large sieve (N + 1.5/delta_r), weights 1/phi(q)
    for name, Ft, lams in [('K=3/(2S)=%.4f (MV weighted LS, q in (Q^(1-eps),Q], w=1/phi(q))' % Kmv, Ft_LS(Kmv), [1, 1.05, 1.1, 1.15, 1.2, 1.25, 1.3, 1.4, 1.5, 1.75, 1.99]),('K=1 (diag only)', Ft_LS(1.0), [1, 1.25, 1.5, 1.75, 1.99]),
                           ('K=1.263 (paper weighted LS, unproved)', Ft_LS(1.263), [1, 1.25, 1.5, 1.75, 1.99]),
                           ('K=2/S=%.4f (classical LS)' % Kc, Ft_LS(Kc), [1, 1.1, 1.2, 1.3, 1.4, 1.5, 1.75, 1.99]),
                           ('GRH F=min(a,1)', Ft_GRH, [1, 1.5, 1.99])]:
        print('==', name)
        for lam in lams:
            R, Rf, u, psi = optimise(lam, Ft)
            print('  lam=%.3f  opt R=%.5f  simple>=%.5f  distinct>=%.5f   | flat R=%.5f -> %.5f'
                  % (lam, R, 2 - R, (3 - R) / 2, Rf, 2 - Rf))
