#!/usr/bin/env python3
"""wild_lowrank_sparse.py -- idea E1: per(C + D) for C of rank r and D sparse.

Identities checked (exact integers, random instances, n <= 7):

 (1) per(C + D) = sum over partial matchings M of the support of D of
                  prod_{(i,j) in M} D_ij * per(C[rows \\ M, cols \\ M])        (multilinearity)
 (2) Barvinok:  for C = U V^T (U, V integer n x r),
                  per(C[I,J]) = sum_{alpha in N^r, |alpha| = |I|} alpha! * [x^alpha] prod_{i in I} (u_i . x)
                                                                 * [y^alpha] prod_{j in J} (v_j . y)
 (3) combined:  per(C + D) = sum_alpha alpha! [x^alpha y^alpha] P_D(x, y),
                  P_D(x,y) = sum_M prod_M D_ij prod_{i notin M}(u_i . x) prod_{j notin M}(v_j . y),
                i.e. P_D is a *vertex-weighted matching generating polynomial of the sparse graph D*
                in 2r variables of degree <= n in each; (n+1)^{2r} evaluations determine it.

Prints PASS/FAIL per instance and a summary.
"""
import itertools, random, sys
from math import factorial
from collections import defaultdict

def per(M):
    n = len(M)
    if n == 0:
        return 1
    # Ryser
    tot = 0
    for S in range(1, 1 << n):
        prod = 1
        for i in range(n):
            s = 0
            for j in range(n):
                if S >> j & 1:
                    s += M[i][j]
            prod *= s
            if prod == 0:
                break
        tot += (-1) ** (n - bin(S).count("1")) * prod
    return tot

def sub(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]

def matchings(edges):
    """all partial matchings (as lists of edges) of a bipartite edge list"""
    edges = list(edges)
    res = []
    def rec(k, used_r, used_c, cur):
        if k == len(edges):
            res.append(list(cur)); return
        rec(k + 1, used_r, used_c, cur)
        i, j = edges[k]
        if i not in used_r and j not in used_c:
            cur.append((i, j)); rec(k + 1, used_r | {i}, used_c | {j}, cur); cur.pop()
    rec(0, frozenset(), frozenset(), [])
    return res

# ---- sparse multivariate polynomials as dict {exponent tuple: coeff} ----
def pmul(p, q):
    r = defaultdict(int)
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            r[tuple(a + b for a, b in zip(e1, e2))] += c1 * c2
    return {e: c for e, c in r.items() if c}

def padd(p, q, s=1):
    r = defaultdict(int, p)
    for e, c in q.items():
        r[e] += s * c
    return {e: c for e, c in r.items() if c}

def linform(vec, r, offset, total):
    """polynomial  sum_k vec[k] * z_{offset+k}  in `total` variables"""
    p = {}
    for k in range(r):
        if vec[k]:
            e = [0] * total; e[offset + k] = 1
            p[tuple(e)] = vec[k]
    return p

def prod_linforms(vecs, r, offset, total):
    p = {tuple([0] * total): 1}
    for v in vecs:
        p = pmul(p, linform(v, r, offset, total))
    return p

def afact(alpha):
    f = 1
    for a in alpha:
        f *= factorial(a)
    return f

def check(n, r, m, rng):
    U = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    V = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
    C = [[sum(U[i][k] * V[j][k] for k in range(r)) for j in range(n)] for i in range(n)]
    cells = rng.sample([(i, j) for i in range(n) for j in range(n)], m)
    D = [[0] * n for _ in range(n)]
    for (i, j) in cells:
        D[i][j] = rng.choice([-2, -1, 1, 2])
    A = [[C[i][j] + D[i][j] for j in range(n)] for i in range(n)]
    target = per(A)
    ok = True
    # (1)
    s1 = 0
    for M in matchings(cells):
        w = 1
        for (i, j) in M:
            w *= D[i][j]
        rows = [i for i in range(n) if i not in {e[0] for e in M}]
        cols = [j for j in range(n) if j not in {e[1] for e in M}]
        s1 += w * per(sub(C, rows, cols))
    ok &= (s1 == target)
    # (2) Barvinok on a random square submatrix
    k = rng.randint(1, n)
    I = sorted(rng.sample(range(n), k)); J = sorted(rng.sample(range(n), k))
    PU = prod_linforms([U[i] for i in I], r, 0, r)
    PV = prod_linforms([V[j] for j in J], r, 0, r)
    s2 = sum(afact(a) * PU[a] * PV.get(a, 0) for a in PU)
    ok &= (s2 == per(sub(C, I, J)))
    # (3) combined generating polynomial in 2r variables
    P = {}
    for M in matchings(cells):
        w = 1
        for (i, j) in M:
            w *= D[i][j]
        rows = [i for i in range(n) if i not in {e[0] for e in M}]
        cols = [j for j in range(n) if j not in {e[1] for e in M}]
        term = pmul(prod_linforms([U[i] for i in rows], r, 0, 2 * r),
                    prod_linforms([V[j] for j in cols], r, r, 2 * r))
        P = padd(P, term, w)
    s3 = 0
    for e, c in P.items():
        if e[:r] == e[r:]:
            s3 += afact(e[:r]) * c
    ok &= (s3 == target)
    print(f"n={n} r={r} m={m}: per={target}  (1) {s1==target}  (2) {s2==per(sub(C,I,J))}  (3) {s3==target}  -> {'PASS' if ok else 'FAIL'}")
    return ok

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    allok = True
    for n, r, m in [(3, 1, 2), (4, 1, 3), (4, 2, 4), (5, 1, 5), (5, 2, 5), (6, 2, 6), (6, 3, 5), (7, 2, 7), (7, 1, 9)]:
        allok &= check(n, r, m, rng)
    print("ALL PASS" if allok else "SOME FAIL")
    # accounting line
    print("accounting: per(C+D) = sum over (n+1)^{2r} evaluation points of a vertex-weighted matching sum on the")
    print("            sparse graph supp(D) (m edges); each evaluation is a local network with U = 2 m_cross bits.")
