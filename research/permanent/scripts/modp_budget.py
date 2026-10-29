"""modp_budget.py -- CRT / p-adic information budget for perm-mod-p.md sections 3 and 5.
(i)  values of per on n x n 0/1 matrices (n <= 4 exhaustive, n = 5 sampled): every m in [0, 2^{n-1}] occurs
(ii) primes needed: smallest P with sum_{p<=P} lg p >= lg n! + 1
(iii) BHL vanishing regime (k_p p < n): bits available from primes <= P' = sum (ceil(n/p)-1) lg p; smallest P'
(iv) single-modulus 2-adic route: k = ceil(lg(n!+1)); Valiant/BHL cost lg(n^k) vs n
(v)  entropy-respecting moduli: with the Lean N-bound each modulus may carry only o(n sqrt(lg n)/(lglg n)^2) bits
"""
import itertools, math, random
from math import lgamma, log2, log
random.seed(3)

def per(A):
    n = len(A); tot = 0
    for mask in range(1 << n):
        prod = 1
        for i in range(n):
            prod *= sum(A[i][j] for j in range(n) if mask >> j & 1)
            if not prod: break
        tot += (-1) ** (n - bin(mask).count('1')) * prod
    return tot

print("(i) values of per on 0/1 matrices")
for n in (2, 3, 4):
    vals = set()
    for bits in range(1 << (n * n)):
        A = [[(bits >> (i * n + j)) & 1 for j in range(n)] for i in range(n)]
        vals.add(per(A))
    print(f"  n={n}: {len(vals)} distinct values; [0,2^(n-1)] covered: {set(range(2**(n-1)+1)) <= vals}; max {max(vals)}")
n = 5; vals = set()
for _ in range(60000):
    d = random.random()
    A = [[1 if random.random() < d else 0 for _ in range(n)] for _ in range(n)]
    vals.add(per(A))
print(f"  n=5 (60000 samples): {len(vals)} distinct values; [0,16] covered: {set(range(17)) <= vals}")

def primes_upto(P):
    s = bytearray([1]) * (P + 1); s[0] = s[1] = 0
    for i in range(2, int(P ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(P + 1) if s[i]]

print("\n(ii)-(iv) budget; lgn! = bits of per; P = largest prime needed for plain CRT; P' = largest prime needed in BHL regime")
print("     n   lg n!   #primes   P     P/(n ln n)  | P'(BHL)  P'/n  BHL saving n/(P' lg P') | 2-adic k   lg(n^k)/n")
deficits = []
for n in (64, 256, 1024, 4096, 16384):
    L = lgamma(n + 1) / log(2) + 1
    pr = primes_upto(int(3 * n * log(n)) + 100)
    s = 0; cnt = 0
    for p in pr:
        s += log2(p); cnt += 1
        if s >= L: P = p; break
    s = 0; Pb = None
    for p in pr:
        if p >= n: break
        s += (math.ceil(n / p) - 1) * log2(p)
        if s >= L: Pb = p; break
    tot_bhl = sum((math.ceil(n / p) - 1) * log2(p) for p in pr if p < n)
    deficits.append((n, L, tot_bhl))
    k = math.ceil(L)
    sav = n / (Pb * log2(Pb)) if Pb else float('nan')
    print(f"  {n:5d} {L:8.0f} {cnt:7d} {P:7d}   {P/(n*log(n)):.3f}     | {str(Pb):>7}  {Pb/n if Pb else float('nan'):.3f}   {sav:8.4f}             | {k:7d}   {k*log2(n)/n:8.1f}")

print("  P' = None: even ALL primes p < n used in the vanishing regime k_p = ceil(n/p)-1 do not reach lg n!:")
for n, L, t in deficits:
    print(f"     n={n:6d}: lg n! = {L:9.0f}, sum_(p<n) (ceil(n/p)-1) lg p = {t:9.0f}, deficit = {(L-t)/n:.2f} n bits")
print("\n(v) entropy-respecting p-adic schemes: bits allowed per modulus b(n) = n*sqrt(lg n)/(lglg n)^2 (the Lean N-bound break-even);")
print("    minimum number of coprime moduli = lg n!/b(n); smallest P with pi(P) >= that; k_p for p=P")
for n in (2**10, 2**16, 2**20, 2**30, 2**40):
    Ln = (lgamma(n + 1) / log(2))
    b = n * math.sqrt(log2(n)) / (log2(log2(n))) ** 2
    m = math.ceil(Ln / b)
    pr = primes_upto(10000)
    P = pr[m - 1]
    print(f"  n=2^{int(log2(n)):2d}: lg n!/n = {Ln/n:6.2f}, b/n = {b/n:5.2f}, moduli >= {m:3d}, primes up to {P:4d}, k_P = {b/log2(P)/n:.2f} n  (k_P*P/n = {b/log2(P)*P/n:.1f}, BHL needs < 1)")
