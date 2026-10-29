#!/usr/bin/env python3
"""wild_hc_complement.py -- idea E2: dense Hamiltonian-cycle counting on K_n - D, D sparse.

Checked identities (exact, brute force, n <= 8, random sparse D):

 (1) per(J - B) = sum_k (-1)^k r_k(B) (n-k)!      (r_k = number of k-matchings of B)   [rook formula]

 (2) #HC(K_n - D) = sum_{F subset E(D)} (-1)^{|F|} H(F),
       H(F) = #Hamiltonian cycles of K_n containing F
            = (n-|F|-1)!/2 * 2^{p(F)} if F is a linear forest with p nontrivial paths (n-|F| >= 1; for |F| = n-1 this is 1),
            = 1 if F is itself a Hamiltonian cycle, 0 otherwise.

 (3) the linear-forest statistic as a determinant (local!):
       sum_{F: deg_F<=2, |F|=k, acyclic} 2^{p(F)}
         = [eps^{n-k}] sum_{F subset E(D): deg_F <= 2, |F| = k} det( L_F + eps * diag([deg_F(v) <= 1]) ),
     so that
       #HC(K_n - D) = sum_{k<=n-2} (-1)^k (n-k-1)!/2 * [eps^{n-k}] S_k(eps)  + (-1)^{n-1} #HamPaths(D) + (-1)^n #HC(D),
     where S_k(eps) is the determinant sum above.  Everything on the right is a sum over subgraphs of the
     SPARSE graph D with local vertex weights and a Grassmann (matrix-tree) edge factor: the shape of the
     team's blob network (exact-count-lowrank.md), with two interpolation variables (y for |F|, eps).
"""
import itertools, random, sys
from fractions import Fraction
from math import factorial

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

def det(M):
    n = len(M); A = [[Fraction(x) for x in row] for row in M]; d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None: return Fraction(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            if f:
                for k in range(c, n): A[r][k] -= f * A[c][k]
    return d

def num_matchings_by_size(B):
    n = len(B); edges = [(i, j) for i in range(n) for j in range(n) if B[i][j]]
    r = [0] * (n + 1)
    def rec(k, ur, uc, size):
        if k == len(edges): r[size] += 1; return
        rec(k + 1, ur, uc, size)
        i, j = edges[k]
        if i not in ur and j not in uc: rec(k + 1, ur | {i}, uc | {j}, size + 1)
    rec(0, frozenset(), frozenset(), 0)
    return r

def ham_cycles(n, adj):
    """number of Hamiltonian cycles of an undirected simple graph (brute force)"""
    if n < 3: return 0
    cnt = 0
    for perm in itertools.permutations(range(1, n)):
        if perm[0] > perm[-1]: continue  # orientation
        cyc = (0,) + perm
        if all(adj[cyc[t]][cyc[(t + 1) % n]] for t in range(n)): cnt += 1
    return cnt

def ham_paths(n, adj):
    cnt = 0
    for perm in itertools.permutations(range(n)):
        if perm[0] > perm[-1]: continue
        if all(adj[perm[t]][perm[t + 1]] for t in range(n - 1)): cnt += 1
    return cnt

def components(n, edges):
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for (a, b) in edges: par[f(a)] = f(b)
    return len({f(v) for v in range(n)})

def check_rook(n, m, rng):
    cells = rng.sample([(i, j) for i in range(n) for j in range(n)], m)
    B = [[0] * n for _ in range(n)]
    for (i, j) in cells: B[i][j] = 1
    A = [[1 - B[i][j] for j in range(n)] for i in range(n)]
    r = num_matchings_by_size(B)
    rhs = sum((-1) ** k * r[k] * factorial(n - k) for k in range(n + 1))
    ok = per(A) == rhs
    print(f"rook: n={n} m={m} per(J-B)={per(A)} formula={rhs} {'PASS' if ok else 'FAIL'}")
    return ok

def check_hc(n, m, rng):
    allpairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    Dedges = rng.sample(allpairs, m)
    adjD = [[0] * n for _ in range(n)]
    for (a, b) in Dedges: adjD[a][b] = adjD[b][a] = 1
    adjG = [[1 if i != j and not adjD[i][j] else 0 for j in range(n)] for i in range(n)]
    truth = ham_cycles(n, adjG)
    # (2) inclusion-exclusion over subsets of D, brute force H(F)
    s2 = 0
    # (3) determinant version
    # S_k(eps) as polynomial in eps: dict k -> list of coefficients
    from collections import defaultdict
    S = defaultdict(lambda: [Fraction(0)] * (n + 1))
    for mask in range(1 << m):
        F = [Dedges[t] for t in range(m) if mask >> t & 1]
        k = len(F)
        deg = [0] * n
        for (a, b) in F: deg[a] += 1; deg[b] += 1
        if max(deg) > 2: continue
        c = components(n, F)
        acyclic = (c == n - k)
        p = sum(1 for v in range(n) if deg[v] == 1) // 2
        if acyclic and n - k >= 1:
            H = Fraction(factorial(n - k - 1), 2) * 2 ** p
        elif k == n and c == 1 and n >= 3:
            H = 1  # F is a Hamiltonian cycle of D
        else:
            H = 0
        s2 += (-1) ** k * H
        # determinant polynomial in eps: det(L_F + eps * diag(d)) with d_v = [deg<=1]
        # compute coefficients by evaluating at n+1 points and interpolating (exact Fractions)
        L = [[0] * n for _ in range(n)]
        for (a, b) in F:
            L[a][a] += 1; L[b][b] += 1; L[a][b] -= 1; L[b][a] -= 1
        dvec = [1 if deg[v] <= 1 else 0 for v in range(n)]
        vals = []
        for e in range(n + 1):
            Me = [[L[i][j] + (e * dvec[i] if i == j else 0) for j in range(n)] for i in range(n)]
            vals.append(det(Me))
        # Lagrange -> coefficients (Newton / solve Vandermonde)
        coeffs = vandermonde_solve(list(range(n + 1)), vals)
        Sk = S[k]
        S[k] = [Sk[t] + coeffs[t] for t in range(n + 1)]
    s3 = Fraction(0)
    for k in range(0, n - 1):
        s3 += (-1) ** k * Fraction(factorial(n - k - 1), 2) * S[k][n - k]
    s3 += (-1) ** (n - 1) * ham_paths(n, adjD) + (-1) ** n * ham_cycles(n, adjD)
    ok = (s2 == truth) and (s3 == truth)
    print(f"#HC(K_n - D): n={n} m={m} truth={truth} incl-excl={s2} det-formula={s3} {'PASS' if ok else 'FAIL'}")
    return ok

def vandermonde_solve(xs, ys):
    n = len(xs)
    A = [[Fraction(x) ** j for j in range(n)] + [Fraction(y)] for x, y in zip(xs, ys)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [v / piv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    ok = True
    for n, m in [(3, 2), (4, 3), (5, 4), (5, 6), (6, 5), (6, 8), (7, 6)]:
        ok &= check_rook(n, m, rng)
    for n, m in [(4, 2), (4, 4), (5, 3), (5, 5), (6, 4), (6, 7), (7, 5), (7, 8), (8, 6)]:
        ok &= check_hc(n, m, rng)
    print("ALL PASS" if ok else "SOME FAIL")
