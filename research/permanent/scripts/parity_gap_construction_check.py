#!/usr/bin/env python3
"""Direct check of Proposition 5.1 (parity-barrier.md): build the rows
   P_u(T) = delta_u Pi_Lambda + sum_k P^(k)_u(T) Pi_k
explicitly (P^(k) = OpenAI's swaps-row for M_k = V0 f_{J_k}(W0)) and verify, for every row u and
every point t, that P_u(t) restricted to {w : a_w(t) != d_u(t)} equals the restriction of some
lambda in Lambda (least squares residual), that P_u(0) = delta_u, and deg <= R-1.  r = 2."""
import numpy as np, sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from parity_general_interface import build
from numpy.polynomial import polynomial as Pl

def run(Q, J, R):
    D, Psi, lev, a, d = build(Q)
    Pn = Psi / np.linalg.norm(Psi, axis=0)          # orthonormal eigenbasis
    proj = lambda S: Pn[:, np.isin(lev, S)] @ Pn[:, np.isin(lev, S)].T
    runs = []
    for j in sorted(J):
        if runs and runs[-1][-1] == j - 1: runs[-1].append(j)
        else: runs.append([j])
    assert max(map(len, runs)) <= R
    PiL = proj([j for j in range(Q + 1) if j not in J])
    Lam = Pn[:, ~np.isin(lev, J)]
    # V0 and W0
    V0 = np.zeros((D, D)); Pis = []
    for s in range(Q):
        P = np.zeros((D, D))
        for w in range(D):
            aw, dw = a[w].copy(), d[w].copy(); aw[s], dw[s] = dw[s], aw[s]
            w2 = sum((2 * aw[t] + dw[t]) * 4**t for t in range(Q)); P[w, w2] = 1
        Pis.append(P)
    V0 = np.linalg.multi_dot(Pis) if Q > 1 else Pis[0]
    W0 = 0.5 * sum(np.eye(D) - P for P in Pis)
    rows_k = []
    for Jk in runs:
        A0 = Jk[0]; Rk = len(Jk)
        # f(z) = (-1)^A0 sum_{j<Rk} (-2)^j binom(z-A0, j)
        f = np.zeros((D, D)); B = np.eye(D)
        for j in range(Rk):
            f += (-2.0)**j * B
            B = B @ (W0 - (A0 + j) * np.eye(D)) / (j + 1)
        Mk = (-1)**A0 * V0 @ f
        rows_k.append((Mk, proj(Jk)))
    worst = 0.0
    for u in range(D):
        # coefficient polynomials of row u: list over w of np poly arrays (degree <= R-1)
        coef = np.zeros((D, R))
        coef[:, 0] += PiL[u]
        for Mk, Pk in rows_k:
            rk = np.zeros((D, R)); rk[:, 0] += (np.eye(D) - Mk)[u]
            for w in np.nonzero(np.abs(Mk[u]) > 1e-12)[0]:
                E = [t + 1 for t in range(Q) if a[w, t] != d[u, t]]
                assert len(E) <= R - 1
                poly = np.array([1.0])
                for s in E: poly = Pl.polymul(poly, [1, -1.0 / s])
                rk[w, :len(poly)] += Mk[u, w] * poly
            coef += Pk @ rk                 # (row * Pi_k) coefficientwise; Pi_k symmetric
        assert np.allclose(coef[:, 0], np.eye(D)[u])
        for t in range(1, Q + 1):
            Pt = coef @ (t ** np.arange(R))
            out = np.array([a[w, t - 1] != d[u, t - 1] for w in range(D)])
            x, *_ = np.linalg.lstsq(Lam[out], Pt[out], rcond=None)
            worst = max(worst, np.max(np.abs(Lam[out] @ x - Pt[out])))
    print(f"Q={Q} J={J} R={R}: runs={runs}, max residual over all rows/points = {worst:.2e}")

for Q, J, R in ((4, [0, 1, 2, 4], 3), (4, [0, 1, 3, 4], 2), (5, [0, 1, 2, 4, 5], 3)):
    run(Q, J, R)
