"""p2 numerical checks: which functionals of the prime indicator the chain-lemma count gives.
Brute force both sides for x <= X (default 10^6). Run: python3 checks.py [X]"""
import sys, random
import numpy as np

X = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
random.seed(1)

# ---- sieves ----
isp = np.ones(X + 1, dtype=bool); isp[:2] = False
for i in range(2, int(X**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
primes = np.nonzero(isp)[0]
tau = np.zeros(X + 1, dtype=np.int64)
for d in range(1, X + 1):
    tau[d::d] += 1
issq = np.zeros(X + 1, dtype=bool); issq[np.arange(int(X**0.5) + 1)**2] = True
tault = np.where(issq, (tau - 1) // 2, tau // 2); tault[0] = 0

def chain(L, mod=None, wfun=None):
    """C_L(n) = sum_{d^2|n} w(d) C_{L-1}(d), C_0 = 1 (n>=1).  wfun(d-array) gives weights (default 1)."""
    C = np.ones(X + 1, dtype=object if mod is None else np.int64); C[0] = 0
    for _ in range(L):
        N = np.zeros(X + 1, dtype=C.dtype)
        for d in range(1, int(X**0.5) + 1):
            w = 1 if wfun is None else wfun[d]
            v = w * C[d]
            if mod: v %= mod
            N[d*d::d*d] += v
        if mod: N %= mod
        N[0] = 0; C = N
    return C

L = 5  # 2^(2^5) > 10^6
C2 = chain(L, mod=2)
term = (tault % 2) * C2 % 2          # summand parity
ok_term = np.array_equal(term.astype(bool), isp)
print(f"[base] term_zmod: tau^<(m)C_L(m) odd <=> m prime, all m<={X}: {ok_term}")
P = np.cumsum(term) % 2  # prefix parity of the count; = pi(x) mod 2 iff term check

def cnt_parity(S_mask, a, b):
    return int(term[a:b+1][S_mask[a:b+1]].sum() % 2), int(isp[a:b+1][S_mask[a:b+1]].sum() % 2)

# (i) residue classes: literal count over {m in [a,b], m = r mod q}, both sides, random intervals
bad = 0; tests = 0
qs = [2, 3, 4, 5, 6, 7, 8, 12, 16, 30, 64, 97, 210, 1009, 2**12, 65537, 99991, 300007]
idx = np.arange(X + 1)
for q in qs:
    for _ in range(40):
        r = random.randrange(q); a = random.randrange(1, X); b = random.randrange(a, X + 1)
        S = (idx % q) == r
        lhs, rhs = cnt_parity(S, a, b); tests += 1; bad += lhs != rhs
print(f"(i) AP parity, q up to 300007 incl. 2^j, {tests} random (q,r,[a,b]): mismatches {bad}")

# (i') how often is an AP odd while the interval is even? (the even-total question)
N0 = X // 2
tot = int(isp[N0:X+1].sum())
print(f"    pi([{N0},{X}]) = {tot} (parity {tot%2})")
for q in [3, 4, 8, 1009]:
    par = [int(isp[N0:X+1][(idx[N0:X+1] % q) == r].sum() % 2) for r in range(min(q, 50))]
    print(f"    q={q}: parities of first {len(par)} classes in [N,2N]: {''.join(map(str,par))}")

# (ii) Legendre classes via canonical sqrt witness y in [1,(q-1)/2]
def legendre_witness(q):
    w = np.zeros(q, dtype=np.int64)
    for y in range(1, (q - 1)//2 + 1): w[y*y % q] += 1
    return w
bad = tests = 0
for q in [3, 5, 7, 11, 13, 101, 1009, 10007]:
    wq = legendre_witness(q)  # w[r] in {0,1}
    W = wq[idx % q]
    for _ in range(30):
        a = random.randrange(1, X); b = random.randrange(a, X + 1)
        lhs = int((term[a:b+1] * W[a:b+1]).sum() % 2)
        rhs = sum(1 for p in primes[(primes >= a) & (primes <= b)] if pow(int(p), (q-1)//2, q) == 1) % 2
        tests += 1; bad += lhs != rhs
print(f"(ii) #{{p in I: (p/q)=1}} mod 2 via canonical-sqrt witness, {tests} tests: mismatches {bad}")
# cubic residues q=1 mod 3: witness count y^3=m has 3 (odd) solutions -> parity correct without canonical choice
bad = tests = 0
for q in [7, 13, 31, 1009]:
    w = np.zeros(q, dtype=np.int64)
    for y in range(1, q): w[pow(y, 3, q)] += 1
    W = w[idx % q]
    for _ in range(30):
        a = random.randrange(1, X); b = random.randrange(a, X + 1)
        lhs = int((term[a:b+1] * W[a:b+1]).sum() % 2)
        rhs = sum(1 for p in primes[(primes >= a) & (primes <= b)] if p % q and pow(int(p), (q-1)//3, q) == 1) % 2
        tests += 1; bad += lhs != rhs
print(f"(ii') cubic-residue classes, raw witness count 3 (odd): {tests} tests, mismatches {bad}")
# Jacobi symbol for composite q = q1*q2 via branch bits (residue / non-residue certificate, canonical)
def jacobi(a, n):
    a %= n; t = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): t = -t
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: t = -t
        a %= n
    return t if n == 1 else 0
bad = tests = 0
for (q1, q2) in [(3, 5), (7, 11), (101, 103)]:
    q = q1*q2
    def cert(qi):
        g = next(g for g in range(2, qi) if pow(g, (qi-1)//2, qi) == qi-1)
        res = np.zeros(qi, dtype=np.int64); non = np.zeros(qi, dtype=np.int64)
        ginv = pow(g, -1, qi)
        for y in range(1, (qi-1)//2 + 1):
            res[y*y % qi] += 1; non[y*y*ginv % qi] += 1   # y^2 = m*g  <=> m = y^2 g^{-1}
        return res, non
    r1, n1 = cert(q1); r2, n2 = cert(q2)
    a1, b1 = r1[idx % q1], n1[idx % q1]; a2, b2 = r2[idx % q2], n2[idx % q2]
    W = a1*a2 + b1*b2      # branches with an even number of non-residue bits
    for _ in range(30):
        a = random.randrange(1, X); b = random.randrange(a, X + 1)
        lhs = int((term[a:b+1] * W[a:b+1]).sum() % 2)
        rhs = sum(1 for p in primes[(primes >= a) & (primes <= b)] if jacobi(int(p), q) == 1) % 2
        tests += 1; bad += lhs != rhs
print(f"(ii'') Jacobi (p/q)=+1, q=q1q2, branch-bit witness: {tests} tests, mismatches {bad}")

# (iii) unions of k intervals: XOR of the k counts
bad = tests = 0
for k in [2, 5, 20]:
    for _ in range(30):
        pts = sorted(random.sample(range(1, X + 1), 2*k))
        ivs = [(pts[2*i], pts[2*i+1]) for i in range(k)]
        lhs = sum(int((P[b] - P[a-1]) % 2) for a, b in ivs) % 2
        rhs = sum(int(isp[a:b+1].sum()) for a, b in ivs) % 2
        tests += 1; bad += lhs != rhs
print(f"(iii) unions of k disjoint intervals (k=2,5,20), XOR of k counts: {tests} tests, mismatches {bad}")

# (v) bits of p: #{p in I: bit_j(p)=1} mod 2 for every j -> XOR of primes in I
bad = tests = 0
for _ in range(40):
    a = random.randrange(1, X); b = random.randrange(a, X + 1)
    xor = 0
    for j in range(20):
        S = ((idx >> j) & 1) == 1
        lhs, _ = cnt_parity(S, a, b); xor |= lhs << j
    true = int(np.bitwise_xor.reduce(primes[(primes >= a) & (primes <= b)])) if b >= 2 and ((primes >= a) & (primes <= b)).any() else 0
    tests += 1; bad += xor != true
print(f"(v) XOR of all primes in I from 20 bit-pattern queries: {tests} tests, mismatches {bad}")

# (iv) pi mod k: W_{k^2} chain with weight f(d), f = c^omega on squarefree d, c = -1 mod k^2,
#      realised as prod_{p^e||c} tau_p(d)^e (sopfr(c) full-width variables). Outer weight g(m)=prod tau_p(m)^e over p^e||k.
from sympy import factorint
def tau_K_arr(K, mod):
    """tau_K(n) mod `mod` for n<=X via multiplicative sieve (tau_K(p^a) = binom(a+K-1,K-1))."""
    from math import comb
    t = np.ones(X + 1, dtype=np.int64)
    for p in primes:
        p = int(p); pa = p; a = 1
        while pa <= X:
            # multiply numbers with exact power p^a
            v = comb(a + K - 1, K - 1) % mod
            sl = np.arange(pa, X + 1, pa); sl = sl[(sl // pa) % p != 0]
            t[sl] = t[sl] * v % mod
            pa *= p; a += 1
    return t
def tau_prod_arr(fac, mod):
    t = np.ones(X + 1, dtype=np.int64)
    for p, e in fac.items():
        tp = tau_K_arr(p, mod)
        for _ in range(e): t = t * tp % mod
    return t
def best_c(k):
    """min sopfr(c) over c = -1 mod k^2 (Dijkstra over units mod k^2, generators = primes p, cost p)."""
    import heapq
    M = k*k; target = M - 1
    gens = [p for p in range(2, 4*M + 50) if all(p % s for s in range(2, int(p**0.5)+1)) and np.gcd(p, k) == 1]
    dist = {1 % M: (0, 1)}; pq = [(0, 1 % M, 1)]
    while pq:
        dcost, u, c = heapq.heappop(pq)
        if u == target: return c, dcost
        if dist[u][0] < dcost: continue
        for p in gens:
            if dcost + p > (dist.get(target, (10**9,))[0]): break
            v = u * p % M
            if v not in dist or dist[v][0] > dcost + p:
                dist[v] = (dcost + p, c * p); heapq.heappush(pq, (dcost + p, v, c * p))
    return None
pi_pref = np.cumsum(isp)
for k in [2, 3, 4, 5, 6, 8]:
    M = k*k
    c, s = best_c(k)
    f = tau_prod_arr(factorint(c), M)
    W = chain(L, mod=M, wfun=f)
    g = tau_prod_arr(factorint(k), M)
    S = np.cumsum(g * W % M) % M
    xs = np.arange(1, X + 1)
    ok = np.array_equal(S[1:], (1 + k * pi_pref[1:]) % M)
    print(f"(iv) k={k}: c={c} (=-1 mod {M}, sopfr {s} vs naive k^2-1={M-1}); "
          f"sum_(m<=x) g(m)W(m) = 1 + k*pi(x) mod k^2 for all x<={X}: {ok}")

# (v') weighted mod-k: sum_{p in I} (p mod 5) mod 3 using witness u<r (m=5t+r)
k = 3; M = 9
c, s = best_c(k); W = chain(L, mod=M, wfun=tau_prod_arr(factorint(c), M)); g = tau_prod_arr(factorint(k), M)
fw = idx % 5
bad = tests = 0
for _ in range(40):
    a = random.randrange(2, X); b = random.randrange(a, X + 1)
    tot = int((g[a:b+1] * W[a:b+1] % M * fw[a:b+1]).sum() % M)
    lhs = (tot // 3) % 3 if tot % 3 == 0 else None
    rhs = int((primes[(primes >= a) & (primes <= b)] % 5).sum() % 3)
    tests += 1; bad += lhs != rhs
print(f"(v') sum_(p in I) (p mod 5) mod 3 via mod-9 count with witness weight: {tests} tests, mismatches {bad}")
