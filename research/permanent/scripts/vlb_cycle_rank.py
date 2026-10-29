#!/usr/bin/env python3
"""vlb_cycle_rank.py -- exact check of Proposition 4.2 of vertex-local-bound.md.

Hard family for Model V: A = I + P_sigma (sigma a derangement), per(A) = 2^{c(sigma)}.  For a
vertex cut around a set Q of clusters {i,i'} with b crossing in-arcs and b crossing out-arcs
fixed, the private data of the two sides are bijections phi_L : in -> out (how sigma routes
through Q) and phi_R : out -> in, and the value is  2^{c(phi_R phi_L)} x (internal cycles).
The matrix  M[pi, rho] = 2^{c(rho pi)}  on S_b has rank  sum_{lambda : at most 2 rows} d_lambda^2
= Catalan(b)  (Schur-Weyl: 2^{c(pi)} = sum_lambda s_lambda(1,1) chi_lambda(pi)).
Checked here for b = 1..5 (exact ranks over Q); also the generic-q version q^{c} with q = 3
(sum over lambda with <= 3 rows) for b <= 4.
"""
import itertools
from fractions import Fraction
from math import comb


def cycles(p):
    n = len(p)
    seen = [False] * n
    c = 0
    for i in range(n):
        if not seen[i]:
            c += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
    return c


def compose(r, p):  # (r o p)(i) = r[p[i]]
    return tuple(r[p[i]] for i in range(len(p)))


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


def catalan(b):
    return comb(2 * b, b) // (b + 1)


def sum_dlambda_sq_rows_le(b, q):
    """Number of permutations of [b] with longest decreasing subsequence <= q (= sum d_lambda^2, l(lambda) <= q)."""
    cnt = 0
    for p in itertools.permutations(range(b)):
        # longest decreasing subsequence by patience sorting on the reversed sequence
        import bisect
        piles = []
        for x in reversed(p):
            k = bisect.bisect_left(piles, x)
            if k == len(piles):
                piles.append(x)
            else:
                piles[k] = x
        if len(piles) <= q:
            cnt += 1
    return cnt


if __name__ == "__main__":
    for q in (2, 3):
        print(f"q = {q}: rank of M[pi,rho] = q^{{c(rho pi)}} on S_b")
        for b in range(1, 6 if q == 2 else 5):
            perms = list(itertools.permutations(range(b)))
            M = [[q ** cycles(compose(r, p)) for r in perms] for p in perms]
            rk = rank_exact(M)
            pred = sum_dlambda_sq_rows_le(b, q)
            extra = f"  Catalan(b) = {catalan(b)}" if q == 2 else ""
            print(f"  b = {b}: rank = {rk:4d}   #perms with longest decreasing subsequence <= q = {pred}{extra}")
