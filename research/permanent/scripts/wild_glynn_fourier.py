#!/usr/bin/env python3
"""wild_glynn_fourier.py -- idea B: Fourier structure of Glynn's formula.

Glynn: per(A) = 2^{1-n} sum_{delta in {+-1}^n} (prod delta_i) prod_j <delta, A_j>.
Write G(delta) = prod_j <delta, A_j>.  per(A) = 2 * \\hat G([n]) (top Walsh coefficient).

Checks for random dense 0/1 A, n <= 8:
  * Glynn identity (exact).
  * Walsh spectrum of G: how many of the 2^n coefficients are nonzero, by level |S|.
    (Expectation: all coefficients with |S| = n mod 2 are generically nonzero -> no sparsity.)
  * the half-split matrix M[delta_1, delta_2] = G(delta_1, delta_2), delta_1 the first n/2 signs:
    its rank over Q is 2^{n/2} (full) -> no low-rank shortcut for the sign sum.
  * the "algebra barrier" matrix  [L + L' = (1,...,1)]  over 0/1 load vectors with |L| = |L'| = n/2 is a
    permutation matrix of size C(n, n/2): any commutative or noncommutative algebra R with a functional
    phi and generators r_j (or r_ij) such that phi(prod_i r_{i f(i)}) = [f bijective] has dim R >= C(n,n/2).
"""
import itertools, random, sys
from fractions import Fraction
from math import comb

def per(M):
    n = len(M); tot = 0
    for S in range(1, 1 << n):
        prod = 1
        for i in range(n):
            s = sum(M[i][j] for j in range(n) if S >> j & 1)
            prod *= s
            if prod == 0: break
        tot += (-1) ** (n - bin(S).count("1")) * prod
    return tot

def rank(M):
    A = [[Fraction(x) for x in row] for row in M]; r = 0; rows = len(A); cols = len(A[0])
    for c in range(cols):
        p = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == rows: break
    return r

def run(n, rng):
    A = [[rng.randint(0, 1) for _ in range(n)] for _ in range(n)]
    cols = list(zip(*A))
    G = {}
    for delta in itertools.product([1, -1], repeat=n):
        g = 1
        for c in cols:
            g *= sum(d * a for d, a in zip(delta, c))
        G[delta] = g
    glynn = sum((1 if sum(1 for d in delta if d < 0) % 2 == 0 else -1) * g for delta, g in G.items())
    assert glynn % 2 ** n == 0
    glynn //= 2 ** n  # sum over all delta = 2 * (sum over delta_1 = 1)
    p = per(A)
    # Walsh spectrum
    nz_by_level = [0] * (n + 1)
    for S in range(1 << n):
        coef = 0
        for delta, g in G.items():
            chi = 1
            for i in range(n):
                if S >> i & 1 and delta[i] < 0: chi = -chi
            coef += chi * g
        if coef != 0: nz_by_level[bin(S).count("1")] += 1
    tot_nz = sum(nz_by_level)
    # half split rank
    h = n // 2
    rows = list(itertools.product([1, -1], repeat=h)); colsd = list(itertools.product([1, -1], repeat=n - h))
    M = [[G[r + c] for c in colsd] for r in rows]
    rk = rank(M)
    print(f"n={n}: per={p} glynn={glynn} {'PASS' if p == glynn else 'FAIL'} | nonzero Walsh coeffs {tot_nz}/{2**n} "
          f"by level {nz_by_level} (levels with |S| = n mod 2 have {sum(comb(n,k) for k in range(n+1) if k%2==n%2)} slots) | "
          f"rank of half-split matrix {rk} (max {2**h})")
    return p == glynn

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    ok = all(run(n, rng) for n in [4, 5, 6, 7, 8])
    # algebra barrier matrix
    for n in [4, 6]:
        Ls = [L for L in itertools.product([0, 1], repeat=n) if sum(L) == n // 2]
        M = [[1 if all(a + b == 1 for a, b in zip(L, Lp)) else 0 for Lp in Ls] for L in Ls]
        print(f"algebra barrier: n={n}, matrix [L+L'=1] has size {len(Ls)} and rank {rank(M)} = C(n,n/2) = {comb(n, n//2)}")
    print("ALL PASS" if ok else "SOME FAIL")
