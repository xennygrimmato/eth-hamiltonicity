"""Find books where the direct m-page calibration bracket Br is negative (m >= 4)."""
import numpy as np, sys
from scipy.optimize import minimize
from calib_check import book_data, bracket, Rm
def br_of(x, m, w):
    rho = np.abs(x[:m]) + 1e-9; a = x[m:]
    A, B, dZ, E, ht = book_data(1.0, rho, a)
    return bracket(E, m, w, Rm(m, w))
m = int(sys.argv[1]); w = float(sys.argv[2])
rng = np.random.default_rng(1)
best = (1e9, None)
for s in range(60):
    x0 = np.concatenate([10**rng.uniform(-2, 1, m), rng.normal(0.5, 1.5, m)])
    r = minimize(br_of, x0, args=(m, w), method='Nelder-Mead', options=dict(maxiter=20000, xatol=1e-10, fatol=1e-13))
    if r.fun < best[0]: best = (r.fun, r.x)
x = best[1]; rho = np.abs(x[:m]) + 1e-9; a = x[m:]
A, B, dZ, E, ht = book_data(1.0, rho, a)
lam = Rm(m, w)
print("min Br =", best[0], " rho =", np.round(rho, 5), " a =", np.round(a, 5))
print("true slack/D =", A.sum()+B.sum() - lam*(w + np.triu(dZ,1).sum()))
print("hub types (1: through u1, 2: through u2):\n", ht)
print("exit angles psi_ij (deg):\n", np.round(np.degrees(np.arctan2(E[...,1], E[...,0])), 2))
