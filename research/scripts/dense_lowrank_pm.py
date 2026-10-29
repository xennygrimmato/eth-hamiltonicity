#!/usr/bin/env python3
"""dense_lowrank_pm.py -- Theorem 3 of dense-structured.md: hafnian (#PM of general graphs) of L + D,
L = U C U^T (rank <= r, symmetric, diagonal ignored), D symmetric sparse.  Exact checks, n <= 10:
 (H1) haf(L+D) = sum_{M matching of supp D} D^M haf(L[V - V(M)]);
 (H2) haf(L[W]) = sum_{|alpha| = |W|} g^{(|W|)}_alpha alpha! [x^alpha] prod_{i in W} (u_i . x),
      g^{(2k)}(y) = (y^T C y / 2)^k / k!;
 (H3) hence haf(L+D) = sum_alpha g^{(|alpha|)}_alpha alpha! [x^alpha] P_D(x),
      P_D(x) = sum_M D^M prod_{i not in V(M)} (u_i . x)   (vertex-weighted matching polynomial of supp D:
      a local network; (n+1)^r evaluation points suffice).
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import factorial
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense_lib import pmul, padd
from dense_nd_graphs import brute_pm


def matchings(edges, n):
    res = []
    def rec(k, M, used):
        if k == len(edges): res.append(list(M)); return
        rec(k + 1, M, used)
        i, j = edges[k]
        if not (used >> i & 1) and not (used >> j & 1):
            M.append((i, j)); rec(k + 1, M, used | 1 << i | 1 << j); M.pop()
    rec(0, [], 0)
    return res


def gpoly(C, r, k):
    q = {}
    for a in range(r):
        for b in range(r):
            if C[a][b]:
                e = [0] * r; e[a] += 1; e[b] += 1
                q[tuple(e)] = q.get(tuple(e), 0) + Fr(C[a][b], 2)
    P = {tuple([0] * r): Fr(1)}
    for _ in range(k): P = pmul(P, q)
    return {e: c / factorial(k) for e, c in P.items()}


def main():
    rng = random.Random(11)
    allok = True
    for (n, r, m) in [(6, 1, 4), (6, 2, 5), (8, 2, 6), (8, 3, 7), (10, 2, 8), (10, 3, 9), (9, 2, 7), (8, 1, 10)]:
        U = [[rng.randint(-2, 2) for _ in range(r)] for _ in range(n)]
        C = [[0] * r for _ in range(r)]
        for a in range(r):
            for b in range(a, r):
                C[a][b] = C[b][a] = rng.randint(-2, 2)
        L = [[sum(U[i][a] * C[a][b] * U[j][b] for a in range(r) for b in range(r)) for j in range(n)] for i in range(n)]
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        D = [[0] * n for _ in range(n)]
        E = rng.sample(pairs, m)
        for i, j in E: D[i][j] = D[j][i] = rng.choice((-1, 1, 2))
        A = [[0 if i == j else L[i][j] + D[i][j] for j in range(n)] for i in range(n)]
        truth = brute_pm(A)
        Ms = matchings(E, n)
        def wM(M):
            p = 1
            for i, j in M: p *= D[i][j]
            return p
        h1 = sum(wM(M) * brute_pm([[L[i][j] if i != j else 0 for j in W] for i in W])
                 for M in Ms for W in [[v for v in range(n) if all(v not in e for e in M)]])
        PD = {}
        for M in Ms:
            P = {tuple([0] * r): wM(M)}
            for v in range(n):
                if any(v in e for e in M): continue
                lin = {}
                for a in range(r):
                    if U[v][a]:
                        e = [0] * r; e[a] = 1; lin[tuple(e)] = U[v][a]
                P = pmul(P, lin)
            PD = padd(PD, P)
        h3 = Fr(0)
        gs = {}
        for e, c in PD.items():
            d = sum(e)
            if d % 2: continue
            if d not in gs: gs[d] = gpoly(C, r, d // 2)
            af = 1
            for x in e: af *= factorial(x)
            h3 += gs[d].get(e, 0) * af * c
        ok = truth == h1 == h3
        allok &= ok
        print(f"n={n} r={r} m={m}: haf brute={truth} (H1)={h1} (H3)={h3} matchings={len(Ms)} points=(n+1)^r={(n+1)**r}  {'PASS' if ok else 'FAIL'}")
    print("ALL PASS" if allok else "SOME FAIL")


if __name__ == "__main__":
    main()
