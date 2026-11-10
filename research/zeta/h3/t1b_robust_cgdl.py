#!/usr/bin/env python3
"""Robust CGdL LP (periodic model, N, M=4N): CGdL constraints (K>=0, r_l<=0 for |l|>=N, sum r=1)
PLUS  r_l >= 0 for |l|<N  and  G_eta(x) := sum_{|l|<N} r_l cosh(w_l eta) cos(w_l x) + sum_{|l|>=N} r_l cos(w_l x) >= 0
for x in [0,N/2], eta in [0, 2Y].  Lemma (h3, T1b_depth_lemma.md sec 6): then sum_X K1 >= N*_X for EVERY conjugation-symmetric
configuration whose off-line points have depth <= Y, hence the CGdL certificate holds for such configurations.
Usage: t1b_robust_cgdl.py N Y1 Y2 ...  (prints value for each Y)"""
import sys, numpy as np
from scipy.optimize import linprog
N = int(sys.argv[1]); M = 4*N; l = np.arange(M+1); wl = 2*np.pi*l/N
G = 30*M; th = np.linspace(0, np.pi, G)
Cm = np.cos(np.outer(th, l)); Cm[:, 1:] *= 2
c = np.zeros(M+1); c[0] = N; c[1:N] = 2*np.arange(1, N)/N
Aeq = np.ones((1, M+1)); Aeq[0, 1:] = 2
xg = np.r_[np.linspace(0, 6, 1201), np.linspace(6, N/2, 300)]
def solve(Y):
    bounds = [(0, None)]*N + [(None, 0)]*(M+1-N)
    A = [-Cm]; b = [np.zeros(G)]
    if Y > 0:
        for eta in np.linspace(0, 2*Y, 13)[1:]:
            coef = np.where(l < N, np.cosh(wl*eta), 1.0)
            Gm = np.cos(np.outer(xg, wl))*coef; Gm[:, 1:] *= 2
            A.append(-Gm); b.append(np.zeros(len(xg)))
    res = linprog(c, A_ub=np.vstack(A), b_ub=np.concatenate(b), A_eq=Aeq, b_eq=[1.0], bounds=bounds, method='highs')
    return (2-res.fun if res.status == 0 else None), res
for Y in [float(v) for v in sys.argv[2:]]:
    v, res = solve(Y)
    print(f"N={N} Y={Y}: robust CGdL value {v}", flush=True)
    if v is not None:
        np.savez(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/robust_{N}_{Y}.npz", r=res.x, N=N, Y=Y, val=v)
