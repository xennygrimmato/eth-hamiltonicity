"""Escape (A)/(C) test: is the prime indicator on [N,2N) a fixed linear combination of
EXACT K-fold factorisation counts with dyadic box constraints on the factors
(the engine's nonlinear query class), optionally with Mobius-signed factors?
Features W_phi(m) = #{ordered (z_1..z_K): prod z = m, z_i in dyadic box a_i} (a=0 means z=1),
summed over permutations (span unchanged).  'mu' variant: weight mu(z_1).
Output: least-squares residual of 1_P in the feature span over m in [N,2N).
Residual 0 => a uniform exact identity (then pi(I) for every I would be Q exact counts).
Usage: python3 nonlin_span.py [log2N]
"""
import numpy as np, sys, itertools, math
from collections import defaultdict

b = int(sys.argv[1]) if len(sys.argv) > 1 else 12
N = 2 ** b; R = range(N, 2 * N)
M = 2 * N
spf = list(range(M + 1))
for p in range(2, int(M ** .5) + 1):
    if spf[p] == p:
        for q in range(p * p, M + 1, p):
            if spf[q] == q: spf[q] = p
def mu(n):
    r = 1
    while n > 1:
        p = spf[n]; n //= p
        if n % p == 0: return 0
        r = -r
    return r
divs = [[] for _ in range(M + 1)]
for d in range(1, M + 1):
    for m in range(d, M + 1, d): divs[m].append(d)
box = lambda z: 0 if z == 1 else z.bit_length()  # dyadic box index
isprime = np.array([1.0 if spf[m] == m else 0.0 for m in R])

def feats(K, signed):
    cols = defaultdict(lambda: np.zeros(N))
    def rec(m, k, acc, w, first):
        if k == 1:
            key = (acc[0],) + tuple(sorted(acc[1:] + (box(m),))) if signed else tuple(sorted(acc + (box(m),)))
            if signed and K == 1: key = (box(m),)
            return [(key, w * (mu(m) if (signed and first) else 1))]
        out = []
        for d in divs[m]:
            ww = w * (mu(d) if (signed and first) else 1)
            if ww == 0: continue
            out += rec(m // d, k - 1, acc + (box(d),), ww, False)
        return out
    for i, m in enumerate(R):
        for key, w in rec(m, K, (), 1, True):
            cols[key][i] += w
    A = np.array([c for c in cols.values() if c.any()]).T
    return A

def resid(A):
    x, *_ = np.linalg.lstsq(A, isprime, rcond=None)
    r = isprime - A @ x
    return np.linalg.matrix_rank(A), np.abs(r).max(), np.linalg.norm(r) / np.linalg.norm(isprime)

print(f"N=2^{b}, rows={N}, primes={int(isprime.sum())}")
acc = None
for signed in [False, True]:
    acc = None
    for K in [2, 3, 4, 5] if not signed else [2, 3, 4]:
        A = feats(K, signed)
        acc = A if acc is None else np.hstack([acc, A])
        rk, mx, rel = resid(acc)
        print(f"{'mu-signed' if signed else 'plain    '} K<={K}: #features={acc.shape[1]:5d} rank={rk:5d} "
              f"max|resid|={mx:.3f} rel L2 resid={rel:.3f}")
