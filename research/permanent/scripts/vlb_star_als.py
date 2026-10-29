#!/usr/bin/env python3
"""vlb_star_als.py -- can a STAR skeleton with 1-bit legs compute per in Model V(1)?

Clusters {i, i'} (row i and column i), node i's table depends on A only through row i and
column i; one routing node (the centre) shares c = 1 bit with every leaf.  By Lemma 3.1 of
barrier.md such a network has value  Sum_T G(T) Prod_i h_i^{T_i}(A_i),  T in {0,1}^n, where
A_i = (row i, column i) and h_i^0, h_i^1 are arbitrary functions of A_i.  Every single cut of
this skeleton passes the rank test (Prop. 3.5), so only a global method can refute it.

We fit the model by alternating least squares (ALS) on all 2^{n^2} matrices and report the
residual.  Residual 0 (up to fp) => the star computes per with bond dimension D.

CAVEAT (see vertex-local-bound.md §7): ALS gets stuck in local minima -- it does not recover the
known D = 3 solution for n = 3 (theta_i = sigma(i), G = [permutation]) -- so a non-zero residual is
NOT evidence of impossibility.  The impossibility of D = 2 is proved exactly in Theorem 2.1 and
checked by vlb_star_hyperdet.py.  Usage: vlb_star_als.py n seed D restarts
"""
import itertools, sys
import numpy as np
from math import factorial

rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
D = int(sys.argv[3]) if len(sys.argv) > 3 else 2   # bond dimension of every leg
N = 2 ** (n * n)

# all matrices, their permanents, and the index of each node's view A_i
bits = ((np.arange(N)[:, None] >> np.arange(n * n)) & 1).astype(np.int64)  # N x n^2
A = bits.reshape(N, n, n)
per = np.zeros(N)
for s in itertools.permutations(range(n)):
    per += np.prod(A[:, np.arange(n), s], axis=1)
view_idx = []
for i in range(n):
    cells = [i * n + j for j in range(n)] + [k * n + i for k in range(n) if k != i]
    v = np.zeros(N, dtype=np.int64)
    for t, c in enumerate(cells):
        v |= bits[:, c] << t
    view_idx.append(v)                      # value in [0, 2^{2n-1})
V = 2 ** (2 * n - 1)
Ts = np.array(list(itertools.product(range(D), repeat=n)))  # D^n x n


def value(h, G):
    """h: n x D x V, G: D^n -> vector of length N."""
    out = np.zeros(N)
    for t, T in enumerate(Ts):
        p = np.full(N, G[t])
        for i in range(n):
            p *= h[i, T[i]][view_idx[i]]
        out += p
    return out


def fit(restarts=int(sys.argv[4]) if len(sys.argv) > 4 else 20, sweeps=300, lam=1e-9):
    best = np.inf
    for r in range(restarts):
        h = rng.standard_normal((n, D, V))
        G = rng.standard_normal(D ** n)
        for sweep in range(sweeps):
            # update G (linear least squares)
            cols = []
            for T in Ts:
                p = np.ones(N)
                for i in range(n):
                    p *= h[i, T[i]][view_idx[i]]
                cols.append(p)
            M = np.stack(cols, 1)
            G = np.linalg.lstsq(M, per, rcond=None)[0]
            # update each h_i: per = Sum_b h_i^b(A_i) * R_b(A), linear in the 2V unknowns
            for i in range(n):
                R = np.zeros((N, D))
                for t, T in enumerate(Ts):
                    p = np.full(N, G[t])
                    for j in range(n):
                        if j != i:
                            p *= h[j, T[j]][view_idx[j]]
                    R[:, T[i]] += p
                # design matrix: column (b, v) = R[:, b] * [view_idx[i] == v]
                Dm = np.zeros((N, D * V))
                for b in range(D):
                    Dm[np.arange(N), b * V + view_idx[i]] = R[:, b]
                sol = np.linalg.lstsq(Dm.T @ Dm + lam * np.eye(D * V), Dm.T @ per, rcond=None)[0]
                h[i] = sol.reshape(D, V)
            res = np.linalg.norm(value(h, G) - per) / np.linalg.norm(per)
            if res < 1e-10:
                break
        best = min(best, res)
        print(f"restart {r:2d}: relative residual {res:.3e}", flush=True)
    return best


if __name__ == "__main__":
    print(f"n = {n}, bond dimension D = {D}: star skeleton, Model V(1); fitting per on all {N} matrices")
    b = fit()
    print(f"best relative residual over restarts: {b:.3e}")
