#!/usr/bin/env python3
"""Numerical sanity checks for research/permanent/barrier.md (exact rational ranks).

Check 1 (row cut, Model R).  For a cut that gives the rows I (|I| = k) to one side and the rows
[n] - I to the other, the matrix  M[A_I, A_rest] = per(A)  (A_I in {0,1}^{k x n}, A_rest in
{0,1}^{(n-k) x n}) has rank exactly C(n, k).  (Lemma 3.2 of barrier.md.)

Check 2 (vertex cut, Model V).  One side owns rows I and columns J (|I| = |J| = k), the other
the rest; the shared blocks I x J^c and I^c x J are fixed.  With the fixing of Lemma 3.4
(two fixed injections, zeros elsewhere) the matrix  M[X, Y] = per(A),  X = A[I, J],
Y = A[I^c, J^c], has rank exactly C(2k, k); and C(2k, k) is also the maximum over ALL fixings
of the shared blocks (Lemma 3.4 and the remark after it).

Ranks are computed exactly over the rationals (fractions), so no floating point is involved.
Large matrices are sampled: a random subset of rows/columns gives a lower bound on the rank, the
proven upper bound is printed next to it.
"""
import itertools, random, sys
from fractions import Fraction
from math import comb

random.seed(1)


def per(A):
    """Permanent of a square 0/1 matrix (list of lists) by Ryser-free brute force for tiny n."""
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


def rank_exact(M):
    """Rank over Q by Gaussian elimination on Fractions."""
    M = [[Fraction(x) for x in row] for row in M]
    r = 0
    rows, cols = len(M), (len(M[0]) if M else 0)
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
        if r == rows:
            break
    return r


def bits_to_matrix(bits, nrows, ncols):
    return [[bits[i * ncols + j] for j in range(ncols)] for i in range(nrows)]


def all_bits(m):
    return list(itertools.product([0, 1], repeat=m))


def sample_bits(m, cnt):
    if 2 ** m <= cnt:
        return all_bits(m)
    return [tuple(random.randint(0, 1) for _ in range(m)) for _ in range(cnt)]


# ---------------------------------------------------------------- Check 1: row cut
def check_row_cut(n, k, cnt=150):
    I = list(range(k))
    top = sample_bits(k * n, cnt)
    bot = sample_bits((n - k) * n, cnt)
    M = []
    for t in top:
        T = bits_to_matrix(t, k, n)
        row = []
        for b in bot:
            B = bits_to_matrix(b, n - k, n)
            row.append(per(T + B))
        M.append(row)
    r = rank_exact(M)
    exact = (2 ** (k * n) <= cnt) and (2 ** ((n - k) * n) <= cnt)
    tag = "exact" if exact else "sampled (lower bound)"
    print(f"row cut   n={n} k={k}: rank = {r:4d}  {tag:22s}  C(n,k) = {comb(n, k)}")
    return r


# ---------------------------------------------------------------- Check 2: vertex cut
def vertex_cut_matrix(n, k, fixing, cntX=150, cntY=150):
    """fixing: dict {(i,j): 0/1} for the shared entries (i<k, j>=k) and (i>=k, j<k)."""
    Xs = sample_bits(k * k, cntX)
    Ys = sample_bits((n - k) * (n - k), cntY)
    M = []
    for x in Xs:
        X = bits_to_matrix(x, k, k)
        row = []
        for y in Ys:
            Y = bits_to_matrix(y, n - k, n - k)
            A = [[0] * n for _ in range(n)]
            for i in range(k):
                for j in range(k):
                    A[i][j] = X[i][j]
            for i in range(n - k):
                for j in range(n - k):
                    A[k + i][k + j] = Y[i][j]
            for (i, j), v in fixing.items():
                A[i][j] = v
            row.append(per(A))
        M.append(row)
    return M, (2 ** (k * k) <= cntX and 2 ** ((n - k) * (n - k)) <= cntY)


def good_fixing(n, k):
    """beta: row i (i<k) -> column k+i ; gamma: column j (j<k) -> row k+j ; zeros elsewhere."""
    fx = {}
    for i in range(k):
        for j in range(k, n):
            fx[(i, j)] = 1 if j == k + i else 0
    for i in range(k, n):
        for j in range(k):
            fx[(i, j)] = 1 if i == k + j else 0
    return fx


def check_vertex_cut(n, k):
    M, exact = vertex_cut_matrix(n, k, good_fixing(n, k))
    r = rank_exact(M)
    tag = "exact" if exact else "sampled (lower bound)"
    print(f"vertex cut n={n} k={k}: rank with the fixing of Lemma 3.4 = {r:4d}  {tag:22s}  C(2k,k) = {comb(2 * k, k)}")
    return r


def check_vertex_cut_all_fixings(n, k):
    shared = [(i, j) for i in range(k) for j in range(k, n)] + [(i, j) for i in range(k, n) for j in range(k)]
    best = 0
    for bits in itertools.product([0, 1], repeat=len(shared)):
        fx = dict(zip(shared, bits))
        M, _ = vertex_cut_matrix(n, k, fx, cntX=10 ** 6, cntY=10 ** 6)
        best = max(best, rank_exact(M))
    print(f"vertex cut n={n} k={k}: max rank over all {2 ** len(shared)} fixings of the shared blocks = {best}  (upper bound C(2k,k) = {comb(2 * k, k)})")
    return best


if __name__ == "__main__":
    print("Check 1: row cut (Model R), rank should equal C(n,k)")
    for n, k in [(3, 1), (4, 1), (4, 2), (5, 1), (5, 2)]:
        check_row_cut(n, k)
    print()
    print("Check 2: vertex cut (Model V), rank should equal C(2k,k)")
    for n, k in [(4, 1), (4, 2), (5, 2), (6, 3)]:
        check_vertex_cut(n, k)
    print()
    print("Check 2b: maximum over all fixings of the shared blocks (small cases)")
    check_vertex_cut_all_fixings(4, 1)
    check_vertex_cut_all_fixings(4, 2)
