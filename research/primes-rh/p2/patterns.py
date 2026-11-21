"""Products of chain-lemma indicators: parity of twin primes, k-tuples, Sophie Germain, Goldbach r(2n), a^2+1.
term(m) = tau^<(m) C_L(m) mod 2 is odd iff m prime (checked in checks.py). Engine count of a conjunction of
copies = product of counts, so parity = product of term's. Brute-force both sides, x <= X."""
import sys, random
import numpy as np
X = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
random.seed(3)
isp = np.ones(X + 1, bool); isp[:2] = False
for i in range(2, int(X**.5) + 1):
    if isp[i]: isp[i*i::i] = False
tau = np.zeros(X + 1, np.int64)
for d in range(1, X + 1): tau[d::d] += 1
r = np.arange(X + 1); issq = np.zeros(X + 1, bool); issq[r[:int(X**.5)+1]**2] = True
tl = np.where(issq, (tau - 1)//2, tau//2); tl[0] = 0
C = np.ones(X + 1, np.int64); C[0] = 0
for _ in range(5):
    N = np.zeros(X + 1, np.int64)
    for d in range(1, int(X**.5) + 1): N[d*d::d*d] += C[d]
    N[0] = 0; C = N % 2
T = (tl * C) % 2   # the actual chain-count summand mod 2 (not isp!)
assert np.array_equal(T.astype(bool), isp)

def check(name, shifts_mul, tests=200):
    """pattern: m -> (a_i m + b_i) all prime; count over m in [A,B]."""
    bad = 0
    for _ in range(tests):
        A = random.randrange(1, X // 3); B = random.randrange(A, X // 3)
        m = np.arange(A, B + 1)
        lhs = np.ones(len(m), np.int64); rhs = np.ones(len(m), bool)
        for (a, b) in shifts_mul:
            v = a*m + b; ok = v <= X
            lhs = lhs * np.where(ok, T[np.minimum(v, X)], 0); rhs &= np.where(ok, isp[np.minimum(v, X)], False)
        bad += int(lhs.sum() % 2) != int(rhs.sum() % 2)
    print(f"{name}: {tests} random intervals, mismatches {bad}")
check("twin (p,p+2)", [(1, 0), (1, 2)])
check("cousin (p,p+4)", [(1, 0), (1, 4)])
check("triple (p,p+2,p+6)", [(1, 0), (1, 2), (1, 6)])
check("quadruple (p,p+2,p+6,p+8)", [(1, 0), (1, 2), (1, 6), (1, 8)])
check("Sophie Germain (p,2p+1)", [(1, 0), (2, 1)])
check("Chen-free: (p, 6p+1)", [(1, 0), (6, 1)])
# Goldbach unordered representations G(2n) = #{p<=n : 2n-p prime}; all 2n <= 2*10^4 plus random up to X
bad = tests = 0
ns = list(range(2, 10**4 + 1)) + [random.randrange(10**4, X // 2) for _ in range(300)]
for n in ns:
    m = np.arange(2, n + 1)
    lhs = int((T[m] * T[2*n - m]).sum() % 2); rhs = int((isp[m] & isp[2*n - m]).sum() % 2)
    tests += 1; bad += lhs != rhs
print(f"Goldbach G(2n) mod 2 (unordered, p<=n): {tests} values of n, mismatches {bad}")
# primes a^2+1 with a in [a1,a2]
bad = tests = 0
amax = int((X - 1)**.5)
for _ in range(300):
    a1 = random.randrange(1, amax); a2 = random.randrange(a1, amax + 1)
    a = np.arange(a1, a2 + 1); v = a*a + 1
    tests += 1; bad += int(T[v].sum() % 2) != int(isp[v].sum() % 2)
print(f"#{{a in [a1,a2]: a^2+1 prime}} mod 2: {tests} tests, mismatches {bad}")
# statistics: parity of twin count pi_2(x) along x
tw = isp[:-2] & isp[2:]
pi2 = np.cumsum(tw)
print("pi_2(10^k) for k=3..6 and parity:", [(10**k, int(pi2[10**k - 2])) for k in range(3, 7) if 10**k - 2 < len(pi2)])
