#!/usr/bin/env python3
"""Fast version of the one-body test (*) (see t1b_onebody.py docstring): tabulated kernels + Adam with analytic gradients.
Backgrounds: k points with masses in {1,2} placed freely in [-R,R].  Prints min LHS(B,y) per y; LHS>=0 everywhere => single-pair D_CGdL."""
import numpy as np, sys
d = np.load("/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/cgdl_r_64.npz"); r = d['r']; N = int(d['N'])
M = len(r)-1; ll = np.arange(-M, M+1); rr = r[np.abs(ll)]; inb = np.abs(ll) < N; w = 2*np.pi*ll/N
xs = np.linspace(-16, 16, 32001); hx = xs[1]-xs[0]
def tab(coef, freqs): return (coef[None, :]*np.cos(np.outer(xs, freqs))).sum(1), -(coef[None, :]*freqs*np.sin(np.outer(xs, freqs))).sum(1)
Kt, Kdt = tab(rr, w); K1t, _ = tab(rr[inb], w[inb])
K10 = rr[inb].sum()
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
def interp(tbl, X): return np.interp(X, xs, tbl)
def run(y, k, B=512, steps=500, lr=0.03, R=6.0):
    Gt, Gdt = tab(rr[inb]*np.cosh(w[inb]*y), w[inb]); Gt = Gt-K1t+Kt
    Gdt = Gdt - tab(rr[inb], w[inb])[1] + Kdt
    selfy = 2*((rr[inb]*np.cosh(2*w[inb]*y)).sum()-K10)
    X = rng.uniform(-R, R, (B, k)); m = rng.choice([1.0, 2.0], (B, k))
    # structured starts: doubles near the zeros of K
    zs = np.array([1.048, -1.048, 2.082, -2.082, 1.935, -1.935, 3.02, -3.02])
    X[:B//4] = zs[rng.integers(0, len(zs), (B//4, k))]+rng.normal(0, 0.05, (B//4, k)); m[:B//4] = 2.0
    mt = np.zeros_like(X); vt = np.zeros_like(X); eye = np.eye(k, dtype=bool)
    for s in range(1, steps+1):
        D = X[:, :, None]-X[:, None, :]
        Kd = np.where(eye, 0, interp(Kdt, D))
        g = 4*m*interp(Gdt, X) + 2*m*(Kd*m[:, None, :]).sum(2)
        mt = 0.9*mt+0.1*g; vt = 0.999*vt+0.001*g*g
        X -= lr*(mt/(1-0.9**s))/(np.sqrt(vt/(1-0.999**s))+1e-12); np.clip(X, -15, 15, out=X)
    D = X[:, :, None]-X[:, None, :]
    f = selfy + 4*(m*interp(Gt, X)).sum(1) + np.einsum('bi,bij,bj->b', m, np.where(eye, 0, interp(Kt, D)), m)
    b = f.argmin(); o = np.argsort(X[b])
    return f[b], selfy, np.round(X[b][o], 3), m[b][o]
print(" y     self(y)-self(0)   min LHS   (k)  argmin background")
for y in [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5, 0.8, 1.2]:
    best = min((run(y, k)+(k,) for k in (1, 2, 3, 4, 6, 8)), key=lambda z: z[0])
    print(f" {y:5.3f}  {best[1]:.6f}   {best[0]:+.6f}  ({best[4]})  x={best[2]} m={best[3]}", flush=True)
