"""Floating-point sanity check (NOT part of the proof): local minimisation of LHS(B,y)/(2 Delta(y)) of (*) over backgrounds
of up to 12 points with integer multiplicities 1..4, started at the minima of G_y.  Reports the smallest ratio found."""
import numpy as np
from scipy.optimize import minimize
from fastnum import K, Gf, Delta
rng = np.random.default_rng(1)
def c(m): return max(m*m-2*m, 0)
def LHS(xs, ms, y):
    v = 2*Delta(y) + 4*np.sum(ms*Gf(xs, y)) + sum(c(m) for m in ms)
    d = xs[:, None]-xs[None, :]; Kd = K(d.ravel()).reshape(d.shape); np.fill_diagonal(Kd, 0)
    return v + ms@Kd@ms
for y in [0.01, 0.05, 0.2, 0.5, 0.75, 1.0, 2.0]:
    x = np.linspace(-15, 15, 30001); g = Gf(x, y)
    mins = x[1:-1][(g[1:-1] < g[:-2]) & (g[1:-1] < g[2:]) & (g[1:-1] < 0)]
    best = np.inf
    for trial in range(30):
        n = min(len(mins), rng.integers(1, 13))
        if n == 0: break
        xs0 = rng.choice(mins, n, replace=False) + rng.normal(0, 0.02, n)
        ms = rng.integers(1, 5, n).astype(float)
        f = lambda z: LHS(z, ms, y)
        res = minimize(f, xs0, method='Nelder-Mead', options=dict(maxiter=400))
        best = min(best, res.fun/(2*Delta(y)))
    print(f'y={y}: min LHS/(2Delta) found = {best:.4f}  (>0 means (*) holds there)')
