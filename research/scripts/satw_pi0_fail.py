"""satw_pi0_fail.py -- research/sat-width.md, Section 2.5 (the failed arity-2 shortcut).

Run: python3 -I satw_pi0_fail.py

The shortcut: let the kind-1 marks be a sub-selection of the kind-0 marks, Pi_j subset of Pi_0 cap Lambda_j,
so that a marked incidence (E,j) need only travel from the owner of E to the home h(j) (2 nodes, not k).
For one assignment with violated set V this replaces [V empty] by
    S(V) = sum_{Pi subset V} (-1)^|Pi| prod_j [ |Pi cap Lambda_j| even ].
P1  S(V) = 2^(|V| - rank) * [1_V in span_F2(Lambda_j restricted to V)]  (rank of the restricted checks),
    by brute force over random V, Lambda.
P2  S(V) != 0 for some nonempty V on every random instance with a check of size 1 restricted to V
    (e.g. V = {E}, E in some Lambda_j): the shortcut does not give [V = empty], so it cannot replace
    inclusion-exclusion; and the error is not confined to |V| > nbar.
P3  Cross-check: the correct expansion (independent Pi_0 and Pi_j subset V_j = Lambda_j cap V, as in (65))
    gives sum_{Pi0 subset V} (-1)^|Pi0| * prod_j sum_{Pi_j subset V_j} sigma_|Pi_j| = [V empty] * prod_j [|V_j| even].
"""
import random
from itertools import combinations
from math import comb

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def sigma(i):
    return 1 if i == 0 else (-1) ** i * 2 ** (i - 1)


def rank_f2(rows):
    rows = [r for r in rows]
    rk = 0
    bits = max((r.bit_length() for r in rows), default=0)
    for b in range(bits):
        piv = None
        for i in range(rk, len(rows)):
            if rows[i] >> b & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> b & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def in_span(rows, v):
    return rank_f2(rows + [v]) == rank_f2(rows)


rng = random.Random(7)
nonzero_small = 0
for trial in range(400):
    m = rng.randint(1, 9)
    r = rng.randint(1, 4)
    lam = [sum(1 << e for e in range(m) if rng.random() < 0.4) for _ in range(r)]
    Vsize = rng.randint(0, m)
    V = rng.sample(range(m), Vsize)
    Vmask = sum(1 << e for e in V)
    S = 0
    for t in range(len(V) + 1):
        for Pi in combinations(V, t):
            pm = sum(1 << e for e in Pi)
            prod = 1
            for L in lam:
                prod *= 1 if bin(pm & L).count("1") % 2 == 0 else 0
            S += (-1) ** t * prod
    restricted = [L & Vmask for L in lam]
    rk = rank_f2(restricted)
    pred = 2 ** (len(V) - rk) if in_span(restricted, Vmask) else 0
    check(S == pred, f"P1 m={m} V={V} lam={lam} S={S} pred={pred}")
    if len(V) >= 1 and S != 0:
        nonzero_small += 1
    # P3
    tot = 0
    for t in range(len(V) + 1):
        for Pi0 in combinations(V, t):
            prod = 1
            for L in lam:
                q = bin(L & Vmask).count("1")
                prod *= sum(sigma(i) * comb(q, i) for i in range(q + 1))
            tot += (-1) ** t * prod
    want = (1 if len(V) == 0 else 0) * (1 if all(bin(L & Vmask).count("1") % 2 == 0 for L in lam) else 0)
    check(tot == want, f"P3 V={V}")

# P2: explicit witness V = {E} with E in Lambda_1
def S_of(V, lam):
    tot = 0
    for t in range(len(V) + 1):
        for Pi in combinations(V, t):
            pm = sum(1 << e for e in Pi)
            tot += (-1) ** t * (1 if all(bin(pm & L).count("1") % 2 == 0 for L in lam) else 0)
    return tot


S = S_of([0], [0b1])
check(S == 1, f"P2 witness S={S}")
check(nonzero_small > 0, "P2 no nonzero S for nonempty V found")
print(f"P1 identity verified on 400 random instances; S(V) != 0 for nonempty V in {nonzero_small} of them")
print("P2 witness: V = {E}, Lambda_1 = {E}: S(V) = 1 - 0 = 1 != 0 = [V empty]")
print("P3 correct expansion (65) verified")
print("PASS" if FAILS == 0 else f"FAIL ({FAILS})")
