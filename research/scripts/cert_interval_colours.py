"""Colour-model (non-uniform weights) experiment for the 'ladder interval' system.

Model (generalises hamiltonicity.md section 8 to vertex-dependent weights):
each vertex v gets a colour c in [q]; X-edges force equal colours; vertex weight w(v,c).
A cycle C not through the root then contributes h(C) = sum_c prod_{v in C} w(v,c).
For an exact filter on the 4 x m grid (rows P,Q = ladder, rows R,S = highway, root in S)
one needs h(C_[i,j]) = 0 for every ladder cycle C_[i,j] (columns i..j of rows P,Q),
while every Hamiltonian cycle forces w(v,0) != 0 for all v.
With y_t = w(P_t,.) * w(Q_t,.) (componentwise), normalised y_{t,0} = 1, the constraints are

    1 + sum_{c=1}^{q-1} prod_{t=i}^{j} y_{t,c} = 0     for all 1 <= i < j <= M.

Question: smallest q for which this is solvable over C, as a function of M.
Zero-free solutions need q >= ~M/2 by a triangular-rank argument; zeros are allowed here.
We search numerically (Levenberg-Marquardt, many random complex starts).
"""
import sys
import numpy as np
from scipy.optimize import least_squares

def residual(z, M, q):
    y = (z[: M * (q - 1)] + 1j * z[M * (q - 1):]).reshape(M, q - 1)
    res = []
    for i in range(M):
        p = np.ones(q - 1, dtype=complex)
        p = p * y[i]
        for j in range(i + 1, M):
            p = p * y[j]
            r = 1 + p.sum()
            res.append(r.real)
            res.append(r.imag)
    return np.array(res)

def solvable(M, q, tries=200, seed=0):
    rng = np.random.default_rng(seed)
    best = np.inf
    for _ in range(tries):
        z0 = rng.normal(size=2 * M * (q - 1)) * rng.choice([0.5, 1, 2])
        sol = least_squares(residual, z0, args=(M, q), method=("lm" if M*(M-1) >= 2*M*(q-1) else "trf"), max_nfev=4000,
                            xtol=1e-15, ftol=1e-15, gtol=1e-15)
        c = np.sqrt((sol.fun ** 2).sum())
        best = min(best, c)
        if c < 1e-9:
            return True, c
    return False, best

if __name__ == "__main__":
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    for q in range(2, 7):
        row = []
        for M in range(2, Mmax + 1):
            ok, c = solvable(M, q)
            row.append((M, ok, c))
            print(f"q={q} M={M} solvable={ok} best_residual={c:.2e}", flush=True)
            if not ok:
                break
