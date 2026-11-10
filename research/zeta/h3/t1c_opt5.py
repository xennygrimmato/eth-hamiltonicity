#!/usr/bin/env python3
"""Re-optimise the 5-parameter kernel with exact (Gauss) autocorrelation and dense constraints r<=0 on [1,c] (201 pts), r>=0 on [0,1]."""
import numpy as np, sys
from scipy.optimize import minimize
c = float(sys.argv[1]) if len(sys.argv) > 1 else 1.5
gx, gw = np.polynomial.legendre.leggauss(60)
def mk(co):
    def f(u): return (co[0]+co[1]*np.cos(2*np.pi*u/c)+co[2]*np.cos(4*np.pi*u/c)+co[3]*np.sin(2*np.pi*u/c)+co[4]*np.sin(4*np.pi*u/c))
    return f
A1 = np.linspace(1, c, 201); A0 = np.linspace(0, 1, 101)
def r(co, a):
    f = mk(co); a = np.abs(np.atleast_1d(a)); lo = -c/2; hi = c/2-a
    U = (hi-lo)[:, None]/2*gx[None, :]+(hi+lo)[:, None]/2
    return (hi-lo)/2*(gw[None, :]*f(U)*f(U+a[:, None])).sum(1)
ga = 0.5*gx+0.5
def val(co):
    intf = co[0]*c
    return 2-(r(co, 0)[0]+2*0.5*np.sum(gw*ga*r(co, ga)))/intf**2
best = None
for s in range(6):
    x0 = np.array([1/c, 0.53, -0.14, 0.34, -0.18])+np.random.default_rng(s).normal(0, 0.03, 5); x0[0] = 1/c
    cons = [{'type': 'ineq', 'fun': lambda x: -r(x, A1)}, {'type': 'ineq', 'fun': lambda x: r(x, A0)}, {'type': 'eq', 'fun': lambda x: x[0]-1/c}]
    res = minimize(lambda x: -val(x), x0, method='SLSQP', constraints=cons, options={'maxiter': 500, 'ftol': 1e-14})
    if res.success and (best is None or -res.fun > best[0]): best = (-res.fun, res.x)
v, x = best
print(f"c={c}: value {v:.6f} coef {np.round(x, 6)}  max r[1,c] {r(x, A1).max():+.2e}  min r[0,1] {r(x, A0).min():+.2e}")
np.save(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/k5opt_{c}.npy", x)
