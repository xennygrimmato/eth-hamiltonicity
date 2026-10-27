"""Raz-Spieker / Cygan-Kratsch-Nederlof / Curticapean-Lindzey-Nederlof matchings-connectivity ranks.

(1) bipartite:     perfect matchings of K_{n,n} <-> permutations; M[s,t] = [s^{-1} t is an n-cycle].
                   Prediction (Fourier on S_n): rank_Q = sum_k binom(n-1,k)^2 = binom(2n-2, n-1).
(2) non-bipartite: perfect matchings on 2t points; H[P,Q] = [P u Q is a single cycle].
(3) cut with b crossing edges: rank(b) = sum_{k>=1} binom(b,2k) rank_Q(H_k)   (block diagonal in the
                   set X of used crossing edges); we report log2(rank)/b.
Q-rank: exact Gaussian elimination mod a 31-bit prime for small sizes, eigenvalues (symmetric
matrices with eigenvalues bounded away from 0) for large ones.  GF(2) rank: bitset elimination.
"""
import itertools, math, sys
import numpy as np

P = 2147483629  # prime < 2^31

def rank_modp(M, p=P):
    A = np.array(M, dtype=np.int64) % p
    n, m = A.shape; r = 0
    for c in range(m):
        piv = None
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        rows = np.nonzero(A[:, c])[0]
        rows = rows[rows != r]
        if len(rows):
            f = A[rows, c].reshape(-1, 1)
            A[rows] = (A[rows] - (f * A[r]) % p) % p
        r += 1
        if r == n:
            break
    return r

def rank_gf2(M):
    rows = []
    for row in M:
        v = 0
        for j, x in enumerate(row):
            if x & 1:
                v |= 1 << j
        rows.append(v)
    basis = {}  # leading bit -> vector
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                break
    return len(basis)

def rank_eig(M, tol=1e-6):
    w = np.linalg.eigvalsh(np.array(M, dtype=np.float64))
    return int(np.sum(np.abs(w) > tol)), w

def cycle_type(perm):
    n = len(perm); seen = [False] * n; ct = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = perm[j]; l += 1
            ct.append(l)
    return sorted(ct, reverse=True)

def bipartite_matrix(n):
    perms = list(itertools.permutations(range(n)))
    idx = {p: i for i, p in enumerate(perms)}
    N = len(perms)
    # M[s,t] = [s^{-1} t is n-cycle]; build via n-cycles c: t = s c
    ncyc = [c for c in perms if cycle_type(c) == [n]]
    M = np.zeros((N, N), dtype=np.int8)
    for i, s in enumerate(perms):
        for c in ncyc:
            t = tuple(s[c[k]] for k in range(n))
            M[i, idx[t]] = 1
    return M

def matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for i in range(1, len(points)):
        b = points[i]
        rest = points[1:i] + points[i + 1:]
        for m in matchings(rest):
            yield [(a, b)] + m

def n_cycles_union(P, Q, pts):
    pa = {}; qa = {}
    for a, b in P:
        pa[a] = b; pa[b] = a
    for a, b in Q:
        qa[a] = b; qa[b] = a
    seen = set(); c = 0
    for s in pts:
        if s in seen:
            continue
        c += 1; x = s; use_p = True
        while True:
            seen.add(x)
            y = pa[x] if use_p else qa[x]
            seen.add(y); x = y; use_p = not use_p
            if x == s and use_p:
                break
    return c

def nonbip_matrix(t):
    pts = list(range(2 * t))
    ms = list(matchings(pts))
    N = len(ms)
    M = np.zeros((N, N), dtype=np.int8)
    for i in range(N):
        for j in range(i, N):
            v = 1 if n_cycles_union(ms[i], ms[j], pts) == 1 else 0
            M[i, j] = M[j, i] = v
    return M

def hook_dim(shape):
    n = sum(shape); prod = 1
    conj = [sum(1 for r in shape if r > j) for j in range(shape[0])] if shape else []
    for i, r in enumerate(shape):
        for j in range(r):
            prod *= (r - j - 1) + (conj[j] - i - 1) + 1
    return math.factorial(n) // prod

def partitions(n, maxp=None):
    if maxp is None:
        maxp = n
    if n == 0:
        yield []
        return
    for k in range(min(n, maxp), 0, -1):
        for rest in partitions(n - k, k):
            yield [k] + rest

def main():
    out = []
    print("== bipartite (K_{n,n}) ==")
    print(" n   #PM   rank_Q  binom(2n-2,n-1)  rank_GF2   2^(n-1)")
    for n in range(2, 8):
        M = bipartite_matrix(n)
        if len(M) <= 720:
            rq = rank_modp(M)
        else:
            rq, _ = rank_eig(M)
        r2 = rank_gf2(M) if len(M) <= 5040 else None
        print(f"{n:2d} {len(M):5d} {rq:8d} {math.comb(2*n-2, n-1):10d} {r2!s:>12s} {2**(n-1):8d}", flush=True)
    print("== non-bipartite (2t points) ==")
    print(" t  #PM  rank_Q rank_GF2  surviving lambda (|-t, via eigenvalue multiplicities = dim S^{2 lambda})")
    rQ = {}
    for t in range(1, 6):
        M = nonbip_matrix(t)
        rq = rank_modp(M) if len(M) <= 945 else rank_eig(M)[0]
        r2 = rank_gf2(M)
        _, w = rank_eig(M)
        # group eigenvalues
        vals = {}
        for x in w:
            key = round(float(x), 4)
            vals[key] = vals.get(key, 0) + 1
        lam_dims = {tuple(l): hook_dim([2 * x for x in l]) for l in partitions(t)}
        rQ[t] = rq
        print(f"{t:2d} {len(M):5d} {rq:6d} {r2:6d}  eig multiplicities {sorted(vals.items())}")
        print(f"      dims of S^(2 lambda): {lam_dims}")
    print("== cut with b crossing edges: rank(b) = sum_k C(b,2k) rank_Q(H_k) ==")
    for b in range(2, 11):
        r = sum(math.comb(b, 2 * k) * rQ.get(k, 0) for k in range(1, b // 2 + 1) if k in rQ)
        print(f" b={b:2d} rank={r:8d} log2(rank)/b={math.log2(r)/b:.3f}")

if __name__ == '__main__':
    main()
