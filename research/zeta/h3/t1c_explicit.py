#!/usr/bin/env python3
"""T1c (h3): explicit CGdL-admissible kernels r = f*f (autocorrelation of a REAL f on [-c/2,c/2]), so r^ = |f^|^2 >= 0 automatically.
Constraint: r(alpha) <= 0 on [1,c].  Value v = 2 - [r(0) + 2 int_0^1 alpha r]/(int f)^2   (RH: CGdL; target: unconditional via D_CGdL).
Write f = e + o (even/odd parts): r = R_ee + R_oo, int r = (int e)^2, and K = r^ = e^^2 + |o^|^2 (sum of two squares: no real zeros
generically).  (a) MT + one odd sine mode, closed form; (b) SLSQP over f on a grid."""
import numpy as np
from scipy.optimize import minimize
def value(f, h, c):
    n = len(f); r = np.correlate(f, f, 'full')*h          # r at lags k*h, k=-(n-1)..n-1
    lags = (np.arange(-(n-1), n))*h
    num = r[n-1] + 2*np.sum((lags[n-1:] <= 1)*lags[n-1:]*r[n-1:])*h
    den = (f.sum()*h)**2
    return 2-num/den, r[n-1:], lags[n-1:]
def run_family(c, n=140):
    h = c/n; u = -c/2+h*(np.arange(n)+0.5)
    e = np.where(np.abs(u) <= 0.5, np.cos(np.sqrt(2)*u), 0.0)
    best = (value(e, h, c)[0], 0, 0)
    for k in [1, 2, 3]:
        for eps in np.linspace(0, 0.6, 61):
            f = e + eps*np.sin(np.pi*k*u/(c/2))*(np.abs(u) <= c/2)
            v, r, lg = value(f, h, c)
            if (r[(lg >= 1-1e-9)] <= 1e-12).all() and v > best[0]: best = (v, k, eps)
    return best
print("(a) MT window + eps*sin(pi k u/(c/2)) on [-c/2,c/2]:")
for c in [1.0, 1.2, 1.3, 1.4, 1.5, 1.6]:
    print(f"   c={c}: best (value, k, eps) = {run_family(c)}")
def slsqp(c, n=70, seed=0):
    h = c/n; u = -c/2+h*(np.arange(n)+0.5)
    f0 = np.where(np.abs(u) <= 0.5, np.cos(np.sqrt(2)*u), 0.0)+0.05*np.random.default_rng(seed).normal(size=n)
    obj = lambda f: -value(f, h, c)[0]
    def cons(f):
        _, r, lg = value(f, h, c); return -r[lg >= 1-1e-9]
    res = minimize(obj, f0, method='SLSQP', constraints=[{'type': 'ineq', 'fun': cons}], options={'maxiter': 400, 'ftol': 1e-12})
    return -res.fun, res.x, u
print("(b) SLSQP over real f on [-c/2,c/2]:")
for c in [1.2, 1.4, 1.6]:
    v, f, u = max((slsqp(c, seed=s) for s in range(3)), key=lambda z: z[0])
    print(f"   c={c}: value {v:.5f}; f/f(0) at u=0,.1,..: {np.round(np.interp(np.arange(0, c/2, 0.1), u, f)/np.interp(0, u, f),3)}  odd part norm/even {np.linalg.norm(f-f[::-1])/np.linalg.norm(f+f[::-1]):.3f}")
