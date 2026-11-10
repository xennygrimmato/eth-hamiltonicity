#!/usr/bin/env python3
"""T1c: smooth parametrised real windows f on [-c/2,c/2] (even modes cos(2 pi j u/c), odd modes sin(2 pi j u/c), j<J, plus the
MT shape), r = f*f computed on a fine grid (n points, trapezoid), constraint r <= 0 on [1,c] at all grid lags, value
v = 2 - [r(0) + 2 int_0^1 a r(a) da]/(int f)^2.  Checks c=1 MT accuracy first."""
import numpy as np, sys
from scipy.optimize import minimize
n = 3000
def setup(c, J):
    u = np.linspace(-c/2, c/2, n); h = u[1]-u[0]
    B = [np.cos(2*np.pi*j*u/c) for j in range(J)] + [np.sin(2*np.pi*j*u/c) for j in range(1, J)]
    return u, h, np.array(B)
def value(coef, u, h, B):
    f = coef @ B; w = np.ones(n); w[0] = w[-1] = 0.5
    fw = f*w
    r = np.correlate(f, fw, 'full')[n-1:]*h; lag = np.arange(n)*h
    m = lag <= 1+1e-12
    g = lag*r*m; num = r[0] + 2*h*(g.sum()-0.5*g[0]-0.5*g[m][-1])
    return 2-num/(fw.sum()*h)**2, r, lag
u = np.linspace(-.5, .5, n); h = u[1]-u[0]; print("check MT at c=1:", value(np.r_[1.0], u, h, np.cos(np.sqrt(2)*u)[None, :])[0], "(exact 0.6725007)")
for c in [float(v) for v in sys.argv[1:]] or [1.2, 1.3, 1.4, 1.5]:
    for J in [int(j) for j in __import__("os").environ.get("JS","4 6").split()]:
        u, h, B = setup(c, J); k = B.shape[0]
        def cons(x):
            _, r, lag = value(x, u, h, B); return -r[lag >= 1][::10]
        best = None
        for s in range(4):
            x0 = np.r_[1.0, np.random.default_rng(s).normal(0, 0.3, k-1)]
            res = minimize(lambda x: -value(x, u, h, B)[0], x0, method='SLSQP', constraints=[{'type': 'ineq', 'fun': cons}, {'type': 'eq', 'fun': lambda x: (x @ B).sum()*h - 1.0}], options={'maxiter': 300, 'ftol': 1e-12})
            v = -res.fun; ok = cons(res.x).min() >= -1e-10
            if ok and (best is None or v > best[0]): best = (v, res.x)
        print(f"c={c} J={J}: value {best[0]:.5f}  coef {np.round(best[1],4)}", flush=True)
        np.save(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/t1c_c{c}_J{J}.npy", np.r_[c, J, best[1]])
