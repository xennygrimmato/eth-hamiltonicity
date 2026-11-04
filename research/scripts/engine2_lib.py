"""Shared exact-arithmetic helpers for engine2_*.py (clique-evaluation engine, algebraic side)."""
import itertools, random

def rank_exact(M):
    """Exact rank over Q of an integer (or Fraction) matrix, Bareiss fraction-free elimination."""
    A = [list(map(int, r)) for r in M]
    if not A: return 0
    n, m = len(A), len(A[0]); r = 0; prev = 1
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c] != 0), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(r + 1, n):
            for j in range(c + 1, m):
                A[i][j] = (A[i][j] * A[r][c] - A[i][c] * A[r][j]) // prev
            A[i][c] = 0
        prev = A[r][c]; r += 1
        if r == n: break
    return r

def rank_mod(M, p):
    A = [[x % p for x in r] for r in M]
    n = len(A); m = len(A[0]) if n else 0; r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c]), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(n):
            if i != r and A[i][c]:
                f = A[i][c]; A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r

def edges(K):
    return [(a, b) for a in range(K) for b in range(a + 1, K)]

def legs(K, a):
    """ordered list of the edges incident to node a"""
    return [tuple(sorted((a, b))) for b in range(K) if b != a]

def clique_Z(K, D, T):
    """brute-force Z = sum over labellings of K(K-1)/2 edges (alphabet D) of prod_a T[a][labels of legs(a)]"""
    E = edges(K); Z = 0
    for lab in itertools.product(range(D), repeat=len(E)):
        x = dict(zip(E, lab)); p = 1
        for a in range(K):
            p *= T[a][tuple(x[e] for e in legs(K, a))]
            if p == 0: break
        Z += p
    return Z

def random_tables(K, D, lo=-3, hi=3, rng=random):
    return [{y: rng.randint(lo, hi) for y in itertools.product(range(D), repeat=K - 1)} for _ in range(K)]

def report(name, ok):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}")
    return ok
