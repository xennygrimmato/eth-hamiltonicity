#!/usr/bin/env python3
"""Numerical evidence for the two bit-count barriers (exact rational rank computations).

(1) Ryser broadcast.  F_a(x) = prod_{i in R_a} (A x)_i, x in {0,1}^n, |R_a| = p.  Split the columns
    into a block C_b of size q and the rest.  The matrix F_a[x_b ; x_rest] has rank 2^{min(p,q,n-q)} for
    generic A (random 0/1 A can be degenerate and give less), so any factorisation of F_a across the cut needs min(p,q) shared bits,
    and the column node of block b sees sum_a min(p,q) ~ n bits.

(2) Block-pair rank.  per(A) = [top] prod_{i,j} (1 + A_ij e_i z_j) in Z[e,z]/(e_i^2, z_j^2)
    (commutative nilpotent variables; this is the Godsil-Gutman sign average written out: averaging
    det(A o S)^2 over independent signs S kills all cross terms and leaves exactly this product with
    e_i = psibar_i phibar_i, z_j = psi_j phi_j).  The factor of a block pair (R_a, C_b) expands as
    sum_{I subset R_a, J subset C_b, |I|=|J|} per(A[I,J]) e_I z_J; its (I ; J) matrix has rank
    sum_s min(C(p,s),C(q,s)) (= 2^p for p = q) for generic entries, the same as the Grassmann
    (determinant) block factor det(A[I,J]); for special 0/1 blocks the rank can be smaller, but a
    network must serve every A, so the worst case is what counts.  Hence the
    "determinant sieve" is a bijection-term network in disguise and costs U = 2 sum_{ab} min(p,q).

(3) Godsil-Gutman identity check for 0/1 A, n <= 3:  per(A) = 2^{-n^2} sum_S det(A o S)^2.

Run: python3 perm_rank_barrier.py  -> PASS/FAIL.
"""
import itertools, random, sys
from fractions import Fraction

def rank(M):
    M = [[Fraction(x) for x in row] for row in M]
    r = 0; nc = len(M[0]) if M else 0
    for c in range(nc):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return r

def permanent(A, rows, cols):
    rows, cols = list(rows), list(cols)
    if len(rows) != len(cols):
        return 0
    tot = 0
    for p in itertools.permutations(cols):
        t = 1
        for i, j in zip(rows, p):
            t *= A[i][j]
            if not t: break
        tot += t
    return tot

def det(M):
    n = len(M)
    if n == 0:
        return 1
    tot = 0
    for p in itertools.permutations(range(n)):
        s = 1; inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
        t = (-1) ** inv
        for i in range(n):
            t *= M[i][p[i]]
            if not t: break
        tot += t
    return tot

def main():
    rng = random.Random(11)
    ok = True
    # (1) Ryser row-group factor across a column cut
    print("(1) rank of F_a(x_b ; x_rest), F_a = prod_{i in R_a} (A x)_i")
    for n, p, q, zo in [(5, 2, 2, 0), (5, 2, 3, 0), (6, 3, 2, 0), (6, 3, 3, 0), (6, 2, 4, 0), (7, 3, 3, 0), (7, 4, 2, 0),
                        (6, 3, 3, 1), (7, 3, 3, 1), (7, 3, 4, 1)]:
        # zo = 0: generic small-integer entries (worst case over A); zo = 1: random 0/1 (rank can only be lower)
        A = [[(1 if rng.random() < 0.7 else 0) if zo else rng.randint(1, 9) for _ in range(n)] for _ in range(n)]
        Ra = list(range(p)); Cb = list(range(q)); rest = list(range(q, n))
        M = []
        for xb in itertools.product((0, 1), repeat=q):
            row = []
            for xr in itertools.product((0, 1), repeat=n - q):
                x = list(xb) + list(xr)
                v = 1
                for i in Ra:
                    v *= sum(A[i][j] * x[j] for j in range(n))
                row.append(v)
            M.append(row)
        r = rank(M); exp = 2 ** min(p, q, n - q)   # n-q: the trivial bound from the size of x_rest
        print(f"   n={n} p={p} q={q} {'0/1' if zo else 'generic'}: rank={r}  2^min(p,q,n-q)={exp}")
        ok &= (r == exp) if not zo else (r <= exp)
    # (2) block-pair rank of per(A[I,J]) and det(A[I,J])
    print("(2) rank of the block-pair matrix (I subset R_a ; J subset C_b) -> per(A[I,J]) and det(A[I,J])")
    from math import comb
    for p, q, zo in [(2, 2, 0), (2, 3, 0), (3, 3, 0), (3, 4, 0), (4, 4, 0), (3, 3, 1), (4, 4, 1)]:
        B = [[(1 if rng.random() < 0.7 else 0) if zo else rng.randint(1, 9) for _ in range(q)] for _ in range(p)]
        Is = [s for r in range(p + 1) for s in itertools.combinations(range(p), r)]
        Js = [s for r in range(q + 1) for s in itertools.combinations(range(q), r)]
        Mp = [[permanent(B, I, J) if len(I) == len(J) else 0 for J in Js] for I in Is]
        Md = [[det([[B[i][j] for j in J] for i in I]) if len(I) == len(J) else 0 for J in Js] for I in Is]
        rp, rd = rank(Mp), rank(Md); exp = sum(min(comb(p, s), comb(q, s)) for s in range(min(p, q) + 1))
        print(f"   p={p} q={q} {'0/1' if zo else 'generic'}: rank(per)={rp} rank(det)={rd}  sum_s min(C(p,s),C(q,s))={exp} (=2^p if p=q)")
        ok &= (rp == exp and rd == exp) if not zo else (rp <= exp and rd <= exp)
    # (3) Godsil-Gutman exact average
    print("(3) per(A) = 2^{-n^2} sum_S det(A o S)^2")
    for n in (2, 3):
        A = [[1 if rng.random() < 0.8 else 0 for _ in range(n)] for _ in range(n)]
        tot = 0
        for S in itertools.product((1, -1), repeat=n * n):
            M = [[A[i][j] * S[i * n + j] for j in range(n)] for i in range(n)]
            tot += det(M) ** 2
        pm = permanent(A, range(n), range(n))
        good = tot == pm * 2 ** (n * n)
        print(f"   n={n}: per={pm}  average={tot}/2^{n*n}  {'ok' if good else 'MISMATCH'}")
        ok &= good
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
