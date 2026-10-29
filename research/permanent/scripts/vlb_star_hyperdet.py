#!/usr/bin/env python3
"""vlb_star_hyperdet.py -- exact check of Theorem 2.1 of vertex-local-bound.md.

Setting: Model V(1) with clusters {i, i'} (row i and column i), skeleton = star with one routing
centre and c = 1 shared bit per leaf (U = 2n).  Writing A = diag(x) + s (x = diagonal, private to
the leaves; s = off-diagonal part), per(A) = Sum_S x^S D_S(s) and the network identity becomes

    Pi(s) := (coefficient tensor of x -> per(diag x + s)) in (Q^2)^{(x) n}  =  (M_1(s_1) (x) ... (x) M_n(s_n)) G

with G in (Q^2)^{(x) n} fixed and M_i(s_i) a 2x2 matrix depending only on node i's view s_i
(row i and column i of s).  So whenever every M_i is invertible, Pi(s) lies in the GL_2^n-orbit
of G.  We exhibit two configurations s (a 3-cycle and a path on nodes 1,2,3, zeros elsewhere)
for which all M_i must be invertible (all one-leg flattenings of Pi(s) have rank 2), but whose
2x2x2 tensors lie in different GL_2^3 orbits (Cayley hyperdeterminant non-zero vs. zero).

This script computes Pi(s) exactly for n = 3 and n = 4, the one-leg flattening ranks, and the
hyperdeterminant of the 2x2x2 tensor obtained by contracting the extra legs (n = 4) at e_1.
"""
import itertools
from fractions import Fraction
from math import comb


def per(A):
    n = len(A)
    if n == 0:
        return 1
    tot = 0
    for s in itertools.permutations(range(n)):
        p = 1
        for i in range(n):
            p *= A[i][s[i]]
            if p == 0:
                break
        tot += p
    return tot


def Pi_tensor(s):
    """Coefficients D_S(s) of per(diag(x) + s) as a dict S -> integer (S a tuple of 0/1)."""
    n = len(s)
    vals = {}
    for x in itertools.product([0, 1], repeat=n):
        A = [[s[i][j] if i != j else x[i] for j in range(n)] for i in range(n)]
        vals[x] = per(A)
    # Moebius inversion on the cube: coefficient of x^S = sum_{T subset S} (-1)^{|S|-|T|} f(T)
    coef = {}
    for S in itertools.product([0, 1], repeat=n):
        c = 0
        for T in itertools.product([0, 1], repeat=n):
            if all(t <= a for t, a in zip(T, S)):
                c += (-1) ** (sum(S) - sum(T)) * vals[T]
        coef[S] = c
    return coef


def rank_exact(M):
    M = [[Fraction(x) for x in row] for row in M]
    r = 0
    rows, cols = len(M), len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


def flattening_rank(coef, n, i):
    """Rank of Pi(s) flattened as (leg i) x (all other legs)."""
    rows = []
    for xi in (0, 1):
        row = []
        for rest in itertools.product([0, 1], repeat=n - 1):
            S = rest[:i] + (xi,) + rest[i:]
            row.append(coef[S])
        rows.append(row)
    return rank_exact(rows)


def hyperdet(a):
    """Cayley hyperdeterminant of a 2x2x2 tensor a[i][j][k]."""
    t = a
    return (t[0][0][0] ** 2 * t[1][1][1] ** 2 + t[0][0][1] ** 2 * t[1][1][0] ** 2
            + t[0][1][0] ** 2 * t[1][0][1] ** 2 + t[1][0][0] ** 2 * t[0][1][1] ** 2
            - 2 * (t[0][0][0] * t[1][1][1] * t[0][0][1] * t[1][1][0]
                   + t[0][0][0] * t[1][1][1] * t[0][1][0] * t[1][0][1]
                   + t[0][0][0] * t[1][1][1] * t[1][0][0] * t[0][1][1]
                   + t[0][0][1] * t[1][1][0] * t[0][1][0] * t[1][0][1]
                   + t[0][0][1] * t[1][1][0] * t[1][0][0] * t[0][1][1]
                   + t[0][1][0] * t[1][0][1] * t[1][0][0] * t[0][1][1])
            + 4 * (t[0][0][0] * t[0][1][1] * t[1][0][1] * t[1][1][0]
                   + t[0][0][1] * t[0][1][0] * t[1][0][0] * t[1][1][1]))


def contract_to_3(coef, n):
    """Keep legs 0,1,2; contract every further leg with e_1^* (pick coefficient x_j = 1)."""
    a = [[[0] * 2 for _ in range(2)] for _ in range(2)]
    for i, j, k in itertools.product([0, 1], repeat=3):
        a[i][j][k] = coef[(i, j, k) + (1,) * (n - 3)]
    return a


def configs(n):
    cyc = [[0] * n for _ in range(n)]
    cyc[0][1] = cyc[1][2] = cyc[2][0] = 1               # 3-cycle 1->2->3->1
    path = [[0] * n for _ in range(n)]
    path[0][1] = path[1][0] = path[1][2] = path[2][1] = 1  # path 1-2-3 (two 2-cycles sharing node 2)
    return {"3-cycle": cyc, "path 1-2-3": path}


if __name__ == "__main__":
    for n in (3, 4):
        print(f"n = {n}")
        for name, s in configs(n).items():
            coef = Pi_tensor(s)
            poly = " + ".join("x" + "".join(str(i + 1) for i in range(n) if S[i]) if any(S) else "1"
                              for S in sorted(coef) if coef[S])
            ranks = [flattening_rank(coef, n, i) for i in range(n)]
            a = contract_to_3(coef, n)
            print(f"  s = {name:11s}: per(diag x + s) = {poly}")
            print(f"      one-leg flattening ranks = {ranks}  (all 2 => every M_i(s_i) invertible)")
            print(f"      Cayley hyperdeterminant of the 2x2x2 tensor on legs 1,2,3 = {hyperdet(a)}")
        print("  Det != 0 (GHZ orbit) vs Det = 0 (W orbit): different GL_2^3-orbits => no star with"
              " 1-bit legs.\n")
    # sanity: the single-cut rank test passes for this skeleton (Prop. 2.2): rank of
    # (x_i | everything else except x_i) completions is 2 = 2^1 for every leaf, by per = x_i*per(A^{ii}) + per(A|x_i=0)
    print("Single-cut check for the star: each leaf cut hides only x_i; rank <= 2 = 2^{c}, so all cut tests pass.")
