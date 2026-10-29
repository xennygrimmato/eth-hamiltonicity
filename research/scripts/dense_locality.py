#!/usr/bin/env python3
"""dense_locality.py -- the network quantity of Theorem 1 is a sum of LOCAL weights on the sparse graph supp(D).

For a fixed (R, T) and a numeric evaluation point (w, x, t) the algorithm needs
    Q = sum_{F acyclic} D^F prod_units l(u, w).
Check (exact, rational): Q = [eps^{n}] Qloc(eps), where
    Qloc(eps) = sum_{F subset arcs(D): indeg,outdeg <= 1} sum_{labellings lam: F -> {0} u T}
                   D^F eps^{|F|} det( Lap(F_und) + eps diag(tau) ) prod_v phi_v,
    tau_v = [indeg_F(v) = 0]   (one per unit: the tail, or the isolated vertex),
    phi_v depends only on the arcs of F at v and their labels:
        isolated: l(v,v);  tail with out-label 0: alpha(v);  tail with out-label (a->b): V_va w_a x_a t_ab;
        internal: [in-label = out-label];  head with in-label 0: beta(v);  head with (a->b): U_vb / x_b,
and all coefficients of eps^j, j < n, vanish (cyclic F only reach degree > n).
The determinant is the fermionic (Berezin) factor of exact-count-lowrank.md / E2: one Grassmann edge factor
(1 + (psibar_i - psibar_j)(psi_i - psi_j)) per arc of F and (1 + eps tau_v psibar_v psi_v) per vertex.
Also prints the per-arc local alphabet size 1 + 5|labels| and per-edge 1 + 10|labels|.
"""
import itertools, random, sys
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense_lib import *


def lagrange_coeffs(xs, ys):
    """coefficients of the interpolating polynomial (exact)."""
    n = len(xs)
    coeffs = [Fr(0)] * n
    for i in range(n):
        num = [Fr(1)]
        den = Fr(1)
        for j in range(n):
            if j == i: continue
            num = [Fr(0)] + num
            for k in range(len(num) - 1):
                num[k] -= xs[j] * num[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n):
            coeffs[k] += ys[i] * num[k] / den
    return coeffs


def run(seed, n, r, m):
    rng = random.Random(seed)
    U = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    V = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    offd = [(i, j) for i in range(n) for j in range(n) if i != j]
    D = [[0] * n for _ in range(n)]
    for (i, j) in rng.sample(offd, m):
        D[i][j] = rng.choice((-1, 1, 2))
    R = list(range(r))
    T = sorted(rng.choice(in_arborescences(R)).items())
    w = [Fr(rng.randint(1, 5)) for _ in range(r)]
    x = [Fr(rng.randint(1, 5)) for _ in range(r)]
    t = [Fr(rng.randint(1, 5)) for _ in T]
    alpha = lambda u: sum(V[u][a] * w[a] * x[a] for a in R)
    beta = lambda v: sum(U[v][b] / x[b] for b in R)
    def ell(u, v):
        s = alpha(u) * beta(v)
        for k, (a, b) in enumerate(T):
            s += t[k] * V[u][a] * w[a] * x[a] * U[v][b] / x[b]
        return s
    arcs = arcs_of(D)
    Q = Fr(0)
    for F in dir_subsets(arcs, n):
        us = units(F, n)
        if us is None: continue
        p = Fr(wprod(D, F))
        for (u, v) in us: p *= ell(u, v)
        Q += p
    labels = [None] + list(range(len(T)))      # None = label 0
    poly = [Fr(0)] * (2 * n + 2)
    for F in dir_subsets(arcs, n):
        ind = {j: (i, j) for i, j in F}; outd = {i: (i, j) for i, j in F}
        tau = [0 if v in ind else 1 for v in range(n)]
        # determinant polynomial in eps of Lap(F_und) + eps diag(tau)
        def lapdet(eps):
            M = [[Fr(0)] * n for _ in range(n)]
            for (i, j) in F:
                M[i][i] += 1; M[j][j] += 1; M[i][j] -= 1; M[j][i] -= 1
            for v in range(n): M[v][v] += eps * tau[v]
            return det(M)
        xs = [Fr(k) for k in range(n + 1)]
        dc = lagrange_coeffs(xs, [lapdet(e) for e in xs])
        lsum = Fr(0)
        for lam in itertools.product(labels, repeat=len(F)):
            lab = dict(zip(F, lam))
            p = Fr(1)
            for v in range(n):
                ia, oa = ind.get(v), outd.get(v)
                if ia is None and oa is None:
                    p *= ell(v, v)
                elif ia is None:
                    l = lab[oa]
                    p *= alpha(v) if l is None else V[v][T[l][0]] * w[T[l][0]] * x[T[l][0]] * t[l]
                elif oa is None:
                    l = lab[ia]
                    p *= beta(v) if l is None else U[v][T[l][1]] / x[T[l][1]]
                else:
                    p *= 1 if lab[ia] == lab[oa] else 0
                if p == 0: break
            lsum += p
        c = Fr(wprod(D, F)) * lsum
        for k, dk in enumerate(dc):
            poly[k + len(F)] += c * dk
    low_ok = all(poly[j] == 0 for j in range(n))
    ok = low_ok and poly[n] == Q
    print(f"seed={seed} n={n} r={r} m={m} |T|={len(T)}: Q={Q} [eps^n]Qloc={poly[n]} lower coeffs zero={low_ok}  "
          f"labels/arc={len(labels)} states/arc={1+5*len(labels)} states/edge={1+10*len(labels)}  {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    ok = True
    for seed, n, r, m in [(1, 5, 2, 6), (2, 6, 2, 6), (3, 5, 3, 6), (4, 6, 3, 7), (5, 6, 1, 8), (6, 6, 3, 5)]:
        ok &= run(seed, n, r, m)
    print("ALL PASS" if ok else "SOME FAIL")
