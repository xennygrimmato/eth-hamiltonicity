#!/usr/bin/env python3
"""wild_modp_sum.py -- idea A(i): per(A) mod p as a character/exponential sum over F_p^n and the
"periodic load" observation.

 (1) For a prime p >= n + 2:
        per(A) == (-1)^n * sum_{x in F_p^n} prod_j x_j^{p-2} * prod_i (A x)_i      (mod p),
     because sum_{x in F_p} x^k = -1 if (p-1) | k, k > 0, and 0 otherwise, and the loads L_j of a map
     f: rows -> cols satisfy sum_j L_j = n, so "L_j + p - 2 == 0 mod (p-1) for all j" forces L_j = 1.
     p^n terms, each a product of n dense linear forms: the same broadcast structure as Ryser/Glynn.

 (2) For ANY q >= 2 (q-th roots of unity, exact over Z[w]):
        #{f : rows -> cols with prod A_{i f(i)} = 1 and L_j(f) == 1 mod q for all j} = per(A),
     checked by direct enumeration: loads == 1 mod q with sum n force all loads = 1.  So Glynn (q = 2)
     is the first member of a family of q^n-term formulas; none has fewer terms than 2^n.

 (3) The CRT framing: lg(n!) bits are needed; with per mod p for all primes p <= 2 n lg n one recovers per.
     (Prime-sum check: sum_{p <= 2 n lg n} lg p > lg n! for n >= 8.)
"""
import itertools, random, sys
from math import log2, factorial

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

def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))

def check1(n, p, rng):
    A = [[rng.randint(0, 1) for _ in range(n)] for _ in range(n)]
    s = 0
    for x in itertools.product(range(p), repeat=n):
        t = 1
        for j in range(n): t = t * pow(x[j], p - 2, p) % p
        if t == 0: continue
        for i in range(n):
            t = t * (sum(A[i][j] * x[j] for j in range(n)) % p) % p
            if t == 0: break
        s = (s + t) % p
    s = (-1) ** n * s % p
    ok = s == per(A) % p
    print(f"(1) n={n} p={p}: per mod p = {per(A) % p}, F_p-sum = {s} {'PASS' if ok else 'FAIL'}")
    return ok

def check2(n, q, rng):
    A = [[rng.randint(0, 1) for _ in range(n)] for _ in range(n)]
    cnt = 0
    for f in itertools.product(range(n), repeat=n):
        if all(A[i][f[i]] for i in range(n)):
            loads = [0] * n
            for i in range(n): loads[f[i]] += 1
            if all(L % q == 1 for L in loads): cnt += 1
    ok = cnt == per(A)
    print(f"(2) n={n} q={q}: #f with loads == 1 mod q = {cnt}, per = {per(A)} {'PASS' if ok else 'FAIL'}")
    return ok

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
    ok = True
    ok &= check1(3, 5, rng); ok &= check1(4, 7, rng); ok &= check1(5, 7, rng)
    ok &= check2(4, 2, rng); ok &= check2(5, 3, rng); ok &= check2(6, 2, rng); ok &= check2(6, 5, rng)
    for n in [8, 16, 64, 256]:
        bound = int(2 * n * log2(n))
        bits = sum(log2(p) for p in range(2, bound + 1) if is_prime(p))
        print(f"(3) n={n}: lg n! = {log2(factorial(n)):.1f}, sum of lg p over primes p <= 2 n lg n = {bits:.1f}, "
              f"#primes = {sum(1 for p in range(2, bound+1) if is_prime(p))}")
    print("ALL PASS" if ok else "SOME FAIL")
