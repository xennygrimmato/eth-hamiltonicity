#!/usr/bin/env python3
"""Lemma T illustrated on h3's N=8 counterexample certificate (randcert_8_6): defect of the certificate C and of the
periodic MT Gram certificate G at the violating configuration; tau = -delta_C/delta_G there (a lower bound for tau(C))."""
import numpy as np
from scipy.optimize import minimize
N = 8; l = np.arange(1, N); w = 2 * np.pi * l / N
d = np.load('randcert_8_6.npz'); c0, a = float(d['c0']), d['a']
# periodic MT-type Gram certificate in data form: c0G = 2 - N r0, aG_l = 2 r_l / N
j = np.arange(N)
def r_of(psi): return np.array([np.sum(psi[:N - k] * psi[k:]) for k in range(N)])
def val(psi): r = r_of(psi); return 2 - N * r[0] - (2 / N) * np.sum(r[1:] * l)
res = minimize(lambda p: -val(np.abs(p) / np.abs(p).sum()), np.ones(N) / N, method='Nelder-Mead', options={'maxiter': 40000, 'xatol': 1e-12, 'fatol': 1e-14})
psi = np.abs(res.x) / np.abs(res.x).sum(); r = r_of(psi); c0G, aG = 2 - N * r[0], 2 * r[1:] / N
def S(t, y, m, isp):
    W = np.where(isp[:, None], 2 * np.cosh(np.outer(y, w)), m[:, None] * np.ones(N - 1)); return (W * np.exp(1j * np.outer(t, w))).sum(0)
m = np.array([2, 2, 2, 2.]); isp = np.array([False, False, True, True])
def dC(z):
    t, y = z[:4], np.r_[0, 0, z[4], z[5]]; return 0 / N - c0 + a @ np.abs(S(t, y, m, isp)) ** 2
r_ = minimize(dC, np.r_[0, 6.999, 0.9754, 1.9764, 0.0991, 0.0991], method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-15, 'maxiter': 20000})
z = r_.x; t, y = z[:4], np.r_[0, 0, z[4], z[5]]
dc = r_.fun; dg = 0 / N - c0G + aG @ np.abs(S(t, y, m, isp)) ** 2
dg0 = -c0G + aG @ np.abs(S(t, np.zeros(4), m, np.zeros(4, bool))) ** 2
print('violating config: positions', np.round(t, 4), 'depths', np.round(z[4:], 4))
print(f'delta_C = {dc:+.4e}   delta_MT = {dg:+.4e} (collapsed: {dg0:+.4e})   tau >= {-dc/dg:.4e}')
print(f'=> mixture (1-eps) MT + eps C passes this config for eps <= {1/(1-dc/dg):.4f}')
