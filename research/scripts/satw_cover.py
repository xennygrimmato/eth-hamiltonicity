"""satw_cover.py -- research/sat-width.md, Lemmas A, C and E (rank, hitting set, averaging).

Run: python3 -I satw_cover.py

C1  Lemma E (averaging) against Lemma 13's family: GF(2^s) family of the paper (16m <= 2^s < 32m,
    Gamma_u = {E : first log v - 1 bits of u1*th_E + u2 are 0 and <u3^iota(E), u4> = 1},
    Omega = {u : |Gamma_u| <= 16m/v}), by Monte Carlo over u. Checks (a) |Gamma_u| <= 16m/v on Omega,
    (Omega >= 15/16 of F^4 up to sampling error), (c) for random V with |V| = v+1 the fraction of
    u in Omega with |Gamma_u cap V| odd is >= 1/4 (up to sampling error), and the averaging bound
    mean_Omega |Gamma_u| >= (1/4) m/(v+1), which every family with property (c) must satisfy.
    Prints the ratio mean|Gamma| / (m/(4(v+1))) (Lemma 13 is within a constant of optimal).
C2  Lemma C (n̄-implication) on random small CNFs: after the greedy of Step 2 (exact X by brute force,
    random candidate checks) reaches X = 0, the union Lambda* of the checks satisfies
    |V_{Phi'}(xi)| <= nbar for every xi in sol(Lambda*), Phi' = Phi minus Lambda* (the true statement);
    and F(Lambda) = #SAT ((63)). It also records how often the NAIVE hitting bound
    sum_{E in Phi'} 2^-|E| <= nbar fails (it is false in general: a clause of Phi' may be implied, or
    nearly implied, by Lambda*); a failure of the naive bound is reported, not counted as FAIL.
C3  Lemma A (rank): the 0/1 equality matrix on the C(t,mu) strings of length t with mu ones has rank
    C(t,mu) over Q, so Psi_ab = [same marks] factors through c bits only if 2^c >= C(t,mu).
"""
import random
from itertools import combinations, product
from math import comb, log2

import numpy as np

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


# ---------- GF(2^s)
def gf_mul(a, b, s, poly):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> s & 1:
            a ^= poly
    return r


def irreducible(s):
    # search for an irreducible polynomial of degree s (brute-force divisibility test)
    for low in range(1, 1 << s, 2):
        poly = (1 << s) | low
        ok = True
        for d in range(2, 1 << (s // 2 + 1)):
            if d.bit_length() - 1 > s // 2:
                break
            # polynomial remainder poly mod d
            x = poly
            dl = d.bit_length()
            while x.bit_length() >= dl:
                x ^= d << (x.bit_length() - dl)
            if x == 0:
                ok = False
                break
        if ok:
            return poly
    raise ValueError


def gf_pow(a, e, s, poly):
    r = 1
    while e:
        if e & 1:
            r = gf_mul(r, a, s, poly)
        a = gf_mul(a, a, s, poly)
        e >>= 1
    return r


def lemma13_mc(m, v, samples, rng):
    s = 1
    while (1 << s) < 16 * m:
        s += 1
    poly = irreducible(s)
    th = list(range(1, m + 1))  # distinct field elements
    iota = list(range(m))
    lv = int(log2(v))
    cap = 16 * m / v
    Vs = [rng.sample(range(m), v + 1) for _ in range(40)]
    kept, sizes, odd = 0, [], [0] * len(Vs)
    for _ in range(samples):
        u1, u2, u3, u4 = (rng.randrange(1 << s) for _ in range(4))
        G = []
        p = 1  # u3^iota(E), iota(E) = E, with u3^0 = 1 also for u3 = 0
        for E in range(m):
            if E > 0:
                p = gf_mul(p, u3, s, poly)
            h = gf_mul(u1, th[E], s, poly) ^ u2
            if lv - 1 > 0 and h >> (s - (lv - 1)) != 0:
                continue
            if bin(p & u4).count("1") % 2 == 1:
                G.append(E)
        if len(G) <= cap:
            kept += 1
            sizes.append(len(G))
            Gs = set(G)
            for i, V in enumerate(Vs):
                if sum(1 for E in V if E in Gs) % 2 == 1:
                    odd[i] += 1
    return s, kept / samples, sizes, [o / kept for o in odd], cap


rng = random.Random(3)
print("C1  Lemma 13 family (Monte Carlo)")
for m, v in [(64, 4), (128, 8), (256, 8), (256, 16)]:
    s, frac, sizes, oddf, cap = lemma13_mc(m, v, 800, rng)
    mean = sum(sizes) / len(sizes)
    lb = m / (4 * (v + 1))
    check(frac >= 15 / 16 - 0.03, f"C1 m={m} v={v} Omega fraction {frac}")
    check(max(sizes) <= cap, "C1 (a)")
    check(min(oddf) >= 0.25 - 0.04, f"C1 (c) m={m} v={v} min odd fraction {min(oddf):.3f}")
    check(mean >= lb, f"C1 averaging m={m} v={v}: mean {mean} < {lb}")
    print(f"    m={m:4d} v={v:3d} s={s}: |Omega|/|F^4|~{frac:.3f}, min_V Pr[odd]~{min(oddf):.3f}, "
          f"mean|Gamma|={mean:.2f}, s_bar=16m/v={cap:.0f}, lower bound m/(4(v+1))={lb:.2f}, ratio {mean/lb:.2f}")


# ---------- C2
def rand_cnf(n, m, k, rng):
    F = []
    for _ in range(m):
        w = rng.randint(k - 1, k)
        vs = rng.sample(range(n), w)
        F.append([(x, rng.random() < 0.5) for x in vs])
    return F


def violated(F, xi):
    return [e for e, C in enumerate(F) if all((xi >> x & 1) != pos for x, pos in C)]


print("C2  n̄-implication (Lemma C) after the Step-2 greedy")
naive_fail = 0
for trial in range(14):
    n, k = 10, 3
    m = rng.randint(20, 45)
    F = rand_cnf(n, m, k, rng)
    nbar = rng.choice([1, 2, 4])
    Vx = [violated(F, xi) for xi in range(1 << n)]
    lam = []
    bad = [(sum(1 << e for e in Vx[xi]), comb(len(Vx[xi]), nbar + 1)) for xi in range(1 << n) if len(Vx[xi]) > nbar]

    def Xval(lam_):
        masks = [sum(1 << e for e in L) for L in lam_]
        return sum(w for vm, w in bad if all(bin(vm & L).count("1") % 2 == 0 for L in masks))

    X = Xval(lam)
    rounds = 0
    while X > 0 and rounds < 200:
        rate = min(0.5, 1.0 / nbar)
        cands = [set(e for e in range(m) if rng.random() < rate) for _ in range(30)]
        best = min(cands, key=lambda L: Xval(lam + [L]))
        lam.append(best)
        X = Xval(lam)
        rounds += 1
    check(X == 0, f"C2 greedy did not finish (trial {trial})")
    star = set().union(*lam) if lam else set()
    rest = sum(2.0 ** -len(F[e]) for e in range(m) if e not in star)
    starmask = sum(1 << e for e in star)
    for xi in range(1 << n):
        vm = sum(1 << e for e in Vx[xi])
        if vm & starmask == 0:
            check(len(Vx[xi]) <= nbar, f"C2 xi in sol(Lambda*) violates {len(Vx[xi])} > nbar clauses")
    if rest > nbar:
        naive_fail += 1
    # (63): F(Lambda) = #SAT
    Fval = 0
    nsat = 0
    for xi in range(1 << n):
        V = Vx[xi]
        eta = sum((-1) ** t * comb(len(V), t) for t in range(min(len(V), nbar) + 1))
        if all(sum(1 for e in V if e in L) % 2 == 0 for L in lam):
            Fval += eta
        nsat += len(V) == 0
    check(Fval == nsat, f"C2 (63) F={Fval} #SAT={nsat}")
    if trial < 5:
        print(f"    n={n} m={m} nbar={nbar}: r={len(lam)} checks, |Lambda*|={len(star)}, m-2^k nbar={m-8*nbar},"
              f" sum_(outside) 2^-|E| = {rest:.3f} (nbar={nbar}), #SAT={nsat}")
print(f"    naive hitting bound sum_(Phi') 2^-|E| <= nbar violated in {naive_fail}/14 instances"
      " (so only the n̄-implication form is a theorem)")

# explicit counterexample to the naive hitting bound: Phi = (x0) and (x0 or x_i), i = 1..q; one check {(x0)}
n, q, nbar = 8, 7, 1
F = [[(0, True)]] + [[(0, True), (i, True)] for i in range(1, q + 1)]
Vx = [violated(F, xi) for xi in range(1 << n)]
ok = all(len(V) <= nbar or (0 in V) for V in Vx)  # every bad xi violates (x0), so the check {(x0)} is odd
rest = sum(2.0 ** -len(C) for C in F[1:])
check(ok and rest > nbar, "C2 explicit witness")
print(f"    witness: Phi=(x0),(x0|x_i) i<=7, Lambda=({{(x0)}}): X=0 but sum_(Phi') 2^-|E| = {rest} > nbar = {nbar}")

# ---------- C3
for t in range(1, 9):
    for mu in range(t + 1):
        N = comb(t, mu)
        strs = list(combinations(range(t), mu))
        A = np.array([[1 if a == b else 0 for b in strs] for a in strs])
        check(np.linalg.matrix_rank(A) == N, "C3")
print("C3  equality matrices on C(t,mu) strings have full rank (t <= 8)")
print("PASS" if FAILS == 0 else f"FAIL ({FAILS})")
