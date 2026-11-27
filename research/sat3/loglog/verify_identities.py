#!/usr/bin/env python3
"""Brute-force checks for research/sat3/loglog.md (exact integers, small formulas).

(A) Level identity (loglog.md, Lemma L):  for a chain  Phi_0 < Phi_1 < ... < Phi_T = Phi  and
    N_t >= max{ |V_{t+1}(xi)| : xi |= Phi_t },   V_{t+1}(xi) = clauses of Phi_{t+1} \\ Phi_t violated by xi,

        #SAT(Phi) = sum_{xi |= Phi_0}  prod_{t<T}  sum_{i<=N_t} (-1)^i C(|V_{t+1}(xi)|, i),

    over the integers, with no parity checks and no reduction modulo a power of two.
    Also: the certificate  X_t(N) = sum_{xi |= Phi_0} prod_{t'<t} tau_{t'}(xi) * C(|V_{t+1}(xi)|, N+1)
    equals  sum_{xi |= Phi_t} C(|V_{t+1}(xi)|, N+1)  and vanishes exactly for N >= N_t.
    Mutation test: with N_t lowered by one at one level the identity must fail on some instance.

(B) Merged monomials of a list of parity checks (Lemma M):  for a 0/1 matrix A (rows = checks,
    columns = clauses) the multilinear polynomial  K(v) = prod_j [ <A_j, v> even ]  has
        coefficient of v^Pi  =  (-2)^{|Pi|} 2^{-rank(A_Pi)}   if the all-ones vector on Pi lies in the
                                                               row space of A restricted to Pi,
                             =  0                              otherwise,
    so its 2-adic valuation is the nullity |Pi| - rank(A_Pi) of the columns Pi.

(C) Cap on the valuation per mark (Lemma V): if f(q) = sum_i c_i C(q,i) is integer valued with f(0)=1
    and f(1)=f(3)=0, then min(v2(c_2), v2(c_3)) <= 1.  Exhaustive over f(2) in a range.
"""
import itertools, random, sys
from math import comb
from fractions import Fraction

def rand_cnf(n, m, rng, k=3):
    cl = set()
    while len(cl) < m:
        vs = tuple(sorted(rng.sample(range(n), k)))
        sg = tuple(rng.randint(0, 1) for _ in range(k))
        cl.add((vs, sg))
    return sorted(cl)

def violated(cl, xi):
    # literal (v, s): s = 1 positive, s = 0 negative; violated iff every literal is false
    vs, sg = cl
    return all(((xi >> v) & 1) != s for v, s in zip(vs, sg))

def trunc_ie(q, N):
    return sum((-1) ** i * comb(q, i) for i in range(0, N + 1))

def check_levels(n, m, T, rng, mutate=False):
    phi = rand_cnf(n, m, rng)
    idx = list(range(m)); rng.shuffle(idx)
    cuts = sorted(rng.sample(range(1, m), T)) if m > T else list(range(1, T + 1))
    level_of = {}
    bounds = [0] + cuts + [m]
    for t in range(T + 1):
        for j in idx[bounds[t]:bounds[t + 1]]:
            level_of[j] = t          # clause j enters at level t (level 0 = Phi_0)
    viol = [[0] * (T + 1) for _ in range(1 << n)]
    for xi in range(1 << n):
        for j, cl in enumerate(phi):
            if violated(cl, xi):
                viol[xi][level_of[j]] += 1
    nsat = sum(1 for xi in range(1 << n) if sum(viol[xi]) == 0)
    # N_t = max |V_{t+1}| over xi satisfying levels 0..t
    N = []
    for t in range(T):
        N.append(max([viol[xi][t + 1] for xi in range(1 << n) if sum(viol[xi][: t + 1]) == 0], default=0))
    Nuse = list(N)
    if mutate:
        cand = [t for t in range(T) if N[t] >= 1]
        if not cand:
            return None
        Nuse[rng.choice(cand)] -= 1
    tot = 0
    for xi in range(1 << n):
        if viol[xi][0]:
            continue
        p = 1
        for t in range(T):
            p *= trunc_ie(viol[xi][t + 1], Nuse[t])
            if p == 0:
                break
        tot += p
    ok = (tot == nsat)
    # certificates
    cert_ok = True
    if not mutate:
        for t in range(T):
            for Ntest in range(0, N[t] + 2):
                lhs = 0
                for xi in range(1 << n):
                    if viol[xi][0]:
                        continue
                    p = comb(viol[xi][t + 1], Ntest + 1)
                    for tp in range(t):
                        p *= trunc_ie(viol[xi][tp + 1], N[tp])
                    lhs += p
                rhs = sum(comb(viol[xi][t + 1], Ntest + 1) for xi in range(1 << n)
                          if sum(viol[xi][: t + 1]) == 0)
                cert_ok &= (lhs == rhs) and ((lhs == 0) == (Ntest >= N[t]))
    return ok, cert_ok, nsat, N

def gf2_rank(rows):
    rows = [r for r in rows]
    rk = 0
    for bit in range(max([r.bit_length() for r in rows] + [0])):
        piv = None
        for i in range(rk, len(rows)):
            if (rows[i] >> bit) & 1:
                piv = i; break
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and (rows[i] >> bit) & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk

def check_merged(a, m, rng):
    A = [rng.getrandbits(m) for _ in range(a)]          # row j as bitmask over clauses
    # values of K on all 0/1 vectors v (bitmask)
    K = [1 if all(bin(r & v).count("1") % 2 == 0 for r in A) else 0 for v in range(1 << m)]
    # Moebius: c_Pi = sum_{S subset Pi} (-1)^{|Pi|-|S|} K(S)
    c = list(K)
    for b in range(m):
        for v in range(1 << m):
            if (v >> b) & 1:
                c[v] -= c[v ^ (1 << b)]
    for Pi in range(1 << m):
        cols = [b for b in range(m) if (Pi >> b) & 1]
        rowsP = [sum((((r >> b) & 1) << i) for i, b in enumerate(cols)) for r in A]
        rk = gf2_rank(rowsP)
        ones = (1 << len(cols)) - 1
        inspan = (gf2_rank(rowsP + [ones]) == rk) if cols else True
        pred = Fraction((-2) ** len(cols), 2 ** rk) if inspan else 0
        if pred != c[Pi]:
            return False
    return True

def v2(x):
    if x == 0:
        return 10 ** 9
    x = abs(x); k = 0
    while x % 2 == 0:
        x //= 2; k += 1
    return k

def check_cap():
    worst = 0
    for f2 in range(-4096, 4097):
        # f(0)=1, f(1)=0, f(2)=f2, f(3)=0
        c2 = 1 - 2 * 0 + f2                    # c_2 = f(0) - 2 f(1) + f(2)
        c3 = -1 + 3 * 0 - 3 * f2 + 0           # c_3 = -f(0) + 3 f(1) - 3 f(2) + f(3)
        worst = max(worst, min(v2(c2), v2(c3)))
    return worst

if __name__ == "__main__":
    rng = random.Random(20261127)
    fails = 0
    runs = 0
    stats = []
    for trial in range(300):
        n = rng.randint(6, 11); m = rng.randint(n, 5 * n); T = rng.randint(1, 4)
        ok, cert_ok, nsat, N = check_levels(n, m, T, rng)
        runs += 1
        if not (ok and cert_ok):
            fails += 1
        stats.append((n, m, T, nsat, N))
    print(f"(A) level identity + certificates: {runs - fails}/{runs} PASS")
    broke = 0; tried = 0
    for trial in range(300):
        n = rng.randint(6, 10); m = rng.randint(2 * n, 5 * n); T = rng.randint(1, 3)
        res = check_levels(n, m, T, rng, mutate=True)
        if res is None:
            continue
        tried += 1
        if not res[0]:
            broke += 1
    print(f"(A) mutation (one N_t lowered by 1): identity fails on {broke}/{tried} instances (must be > 0)")
    okB = all(check_merged(rng.randint(1, 6), rng.randint(1, 9), rng) for _ in range(200))
    print(f"(B) merged-monomial coefficient = (-2)^|Pi| 2^-rank or 0: {'PASS' if okB else 'FAIL'} (200 matrices)")
    w = check_cap()
    print(f"(C) max over f(2) in [-4096,4096] of min(v2(c_2), v2(c_3)) = {w} (claim: 1)")
    print("sample (n, m, T, #SAT, N_t):", stats[:5])
    sys.exit(0 if (fails == 0 and broke > 0 and okB and w == 1) else 1)
