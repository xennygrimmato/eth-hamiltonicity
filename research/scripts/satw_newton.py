"""satw_newton.py -- research/sat-width.md, Lemma D (the 2-adic cut-off and why p = 2).

Run: python3 -I satw_newton.py

N1  [q even] = sum_i sigma_i C(q,i) with sigma_0 = 1, sigma_i = (-1)^i 2^(i-1)  (paper, before Lemma 12),
    for q = 0..60.
N2  Lemma 12 on random small instances: a list of r checks with |V_j| given, the sum over tuples
    (Pi_1..Pi_r), Pi_j subset of V_j, of prod sigma_|Pi_j|, truncated at sum |Pi_j| <= M' with
    M' = nu - 1 + r, is congruent to prod_j [|V_j| even] mod 2^nu; and the truncation at M' - 1 can fail.
N3  For primes p, the Newton (binomial-basis) coefficients c_i = Delta^i f(0) of f(q) = [q = 0 mod p]
    have v_p(c_i) >= ceil(i/(p-1)) - 1, with equality infinitely often (checked i <= 120): the best
    possible 'precision per mark' is 1/(p-1) p-adic digits = log2(p)/(p-1) bits, which is 1 for p = 2
    and < 1 for every odd p (log2 3/2 = 0.79, log2 5/4 = 0.58, ...). So, among cut-offs of this
    form, marks needed per bit of precision are minimised by p = 2.
N4  2-adic rate of an arbitrary check function: over ALL f : {0..14} -> {0,1} with f(0) = 1 (accepts a
    satisfying assignment) and f(1) = 0 (rejects a single violated clause), the Newton coefficients
    satisfy min_{1<=i<=14} (v_2(c_i) - (i-1)) <= 0, with 0 attained only by f = [q even]. So no check
    function gains 2-adic weight faster than parity, uniformly in the number of marks (checked up to 14).
    Moduli 4 and 8 ([q = 0 mod 4], [q = 0 mod 8]) are listed for comparison (rate about 1/2, 1/4).
"""
import random
from math import comb, log2, ceil
from itertools import product

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def sigma(i):
    return 1 if i == 0 else (-1) ** i * 2 ** (i - 1)


def vp(x, p):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


# N1
for q in range(61):
    check(sum(sigma(i) * comb(q, i) for i in range(q + 1)) == (1 if q % 2 == 0 else 0), f"N1 q={q}")
print("N1 done")

# N2
rng = random.Random(1)
n2_fail_tight = 0
for trial in range(300):
    r = rng.randint(1, 4)
    sizes = [rng.randint(0, 6) for _ in range(r)]
    nu = rng.randint(1, 6)
    Mp = nu - 1 + r
    exact = 1
    for s in sizes:
        exact *= 1 if s % 2 == 0 else 0

    def trunc(Mcap):
        # sum over (i_1..i_r) with i_j <= s_j, sum i_j <= Mcap, of prod C(s_j,i_j) sigma(i_j)
        tot = 0
        for t in product(*[range(s + 1) for s in sizes]):
            if sum(t) <= Mcap:
                term = 1
                for s, i in zip(sizes, t):
                    term *= comb(s, i) * sigma(i)
                tot += term
        return tot

    check((trunc(Mp) - exact) % (2 ** nu) == 0, f"N2 sizes={sizes} nu={nu}")
    if Mp - 1 >= 0 and (trunc(Mp - 1) - exact) % (2 ** nu) != 0:
        n2_fail_tight += 1
check(n2_fail_tight > 0, "N2: truncation at M'-1 never failed (expected to fail sometimes)")
print(f"N2 done (truncation at M'-1 fails in {n2_fail_tight}/300 random cases, as it may)")

# N3
print("N3  p : min over i of v_p(c_i) - (ceil(i/(p-1)) - 1) [should be 0]; bits per mark log2(p)/(p-1)")
for p in [2, 3, 5, 7]:
    N = 121
    f = [1 if q % p == 0 else 0 for q in range(N + 1)]
    # finite differences c_i = sum_j (-1)^(i-j) C(i,j) f(j)
    c = [sum((-1) ** (i - j) * comb(i, j) * f[j] for j in range(i + 1)) for i in range(N)]
    # identity check: f(q) = sum_i c_i C(q,i)
    for q in range(N):
        check(sum(c[i] * comb(q, i) for i in range(q + 1)) == f[q], f"N3 newton identity p={p} q={q}")
    slack = []
    for i in range(1, N):
        lb = ceil(i / (p - 1)) - 1
        v = vp(c[i], p)
        check(v >= lb, f"N3 p={p} i={i} v={v} < {lb}")
        slack.append(v - lb)
    eq = sum(1 for s in slack if s == 0)
    check(eq >= 10, f"N3 p={p}: bound attained only {eq} times")
    bpm = log2(p) / (p - 1)
    print(f"    p={p}: min slack {min(slack)}, attained {eq} times for i<{N}; bits/mark {bpm:.3f};"
          f" marks for n=1000 bits ~ {ceil(1001 / bpm)}")
    if p > 2:
        check(bpm < 1, f"N3 p={p} bits per mark not < 1")
    if p == 2:
        check(all(c[i] == sigma(i) for i in range(N)), "N3 p=2 coefficients are sigma_i")

# N4
best, arg, nbest = -99, None, 0
L = 14
for tail in product([0, 1], repeat=L - 1):
    f = [1, 0] + list(tail)
    c = [sum((-1) ** (i - j) * comb(i, j) * f[j] for j in range(i + 1)) for i in range(L + 1)]
    sl = min(vp(c[i], 2) - (i - 1) for i in range(1, L + 1))
    if sl > best:
        best, arg, nbest = sl, f, 1
    elif sl == best:
        nbest += 1
check(best == 0 and nbest == 1 and arg == [1 - q % 2 for q in range(L + 1)], f"N4 best={best} arg={arg}")
print(f"N4 done: best uniform 2-adic slack over all 2^{L-1} check functions = {best}, attained by parity only ({nbest})")
for mod in [4, 8]:
    f = [1 if q % mod == 0 else 0 for q in range(65)]
    c = [sum((-1) ** (i - j) * comb(i, j) * f[j] for j in range(i + 1)) for i in range(64)]
    print(f"    [q = 0 mod {mod}]: v_2(c_i), i=1..24:", [vp(c[i], 2) for i in range(1, 25)])

print("PASS" if FAILS == 0 else f"FAIL ({FAILS})")
