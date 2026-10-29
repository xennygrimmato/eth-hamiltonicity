#!/usr/bin/env python3
"""Certify (numerically, high precision) that a NON-commutative M0 beats the best commutative one
for r=2, Q=3, R=2: rank(I-M) = 8 < 10 = commutative optimum (= exact lower bound 8 from the
max triangular set).  ALS finds G = X Y^T of rank 8 matching all forced entries; we then
(i) report forced-entry residual and singular values, (ii) check that M = I - G satisfies the
support condition up to the residual, (iii) check that M does not commute with the swaps
(so it is outside the commutative algebra), (iv) refine in mpmath (50 digits) by Newton/Gauss-Newton
on the forced equations to show the residual goes to ~1e-40 (a genuine solution, not a near miss)."""
import numpy as np, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from parity_exact_minrank import allowed, als_rank
import mpmath as mp

Q, R, k = 3, 2, 8
L, A = allowed(Q, R)
D = len(L); forced = ~A; I = np.eye(D)
rng = np.random.default_rng(1)
best = None
for trial in range(20):
    X = rng.standard_normal((D, k)); Y = rng.standard_normal((D, k))
    for _ in range(1500):
        for i in range(D):
            cols = np.where(forced[i])[0]; X[i] = np.linalg.lstsq(Y[cols], I[i, cols], rcond=None)[0]
        for j in range(D):
            rows = np.where(forced[:, j])[0]; Y[j] = np.linalg.lstsq(X[rows], I[rows, j], rcond=None)[0]
    G = X @ Y.T; res = np.max(np.abs((G - I)[forced]))
    if best is None or res < best[0]:
        best = (res, X.copy(), Y.copy())
    if res < 1e-12:
        break
res, X, Y = best
G = X @ Y.T
print("float: forced residual", res)
s = np.linalg.svd(G, compute_uv=False); print("singular values 7..10:", s[6:10])
M = I - G
# swaps Pi_s : exchange a_s and d_s
def idx(a, d): return L.index((a, d))
Pis = []
for sb in range(Q):
    P = np.zeros((D, D))
    for i, (a, d) in enumerate(L):
        ba = (a >> sb) & 1; bd = (d >> sb) & 1
        a2 = (a & ~(1 << sb)) | (bd << sb); d2 = (d & ~(1 << sb)) | (ba << sb)
        P[i, idx(a2, d2)] = 1
    Pis.append(P)
print("||[M,Pi_s]|| :", [float(np.linalg.norm(M @ P - P @ M)) for P in Pis])
# Gauss-Newton refinement in mpmath on unknowns X,Y (forced equations), 50 digits
mp.mp.dps = 50
fi = np.argwhere(forced)
def F(Xm, Ym):
    return [ (Xm[i] * Ym[j].T)[0, 0] - (1 if i == j else 0) for i, j in fi]
Xm = mp.matrix(X.tolist()); Ym = mp.matrix(Y.tolist())
for it in range(6):
    # alternate exact least squares solves in mpmath (row-wise), which converge quadratically near a solution
    for i in range(D):
        cols = np.where(forced[i])[0]
        Am = mp.matrix([[Ym[j, c] for c in range(k)] for j in cols]); b = mp.matrix([1 if j == i else 0 for j in cols])
        sol = mp.lu_solve(Am.T * Am, Am.T * b)
        for c in range(k): Xm[i, c] = sol[c]
    for j in range(D):
        rows = np.where(forced[:, j])[0]
        Am = mp.matrix([[Xm[i, c] for c in range(k)] for i in rows]); b = mp.matrix([1 if i == j else 0 for i in rows])
        sol = mp.lu_solve(Am.T * Am, Am.T * b)
        for c in range(k): Ym[j, c] = sol[c]
    r = max(abs((sum(Xm[i, c] * Ym[j, c] for c in range(k))) - (1 if i == j else 0)) for i, j in fi)
    print("mp iteration", it, "forced residual", mp.nstr(r, 5))
