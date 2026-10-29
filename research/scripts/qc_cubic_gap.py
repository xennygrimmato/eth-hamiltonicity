"""Cubic phases (IQP / poly3-NONBALANCED of Dalzell-Harrow-Koh-La Placa): which truncation works.

Run: python3 -I qc_cubic_gap.py [seed] [instances]

For f = sum_{t in T} m_t (mod 2), m_t a monomial of degree <= 3 over F2, gap(f) = sum_x (-1)^{f(x)}.

C1  exact expansion   gap(f) = sum_{S subset T} (-2)^{|S|} 2^{n-|V(S)|}           (V(S) = variables covered by S)
C2  2-adic truncation gap(f) == sum_{|S| <= n+1} (-2)^{|S|} 2^{n-|V(S)|}  (mod 2^{n+2}), and the balanced lift
    of that residue is gap(f) exactly (|gap| <= 2^n)
C3  sharpness: every term with |S| > |V(S)|+1 is divisible by 2^{n+2}; truncating at n' < n+1 marks fails on some
    instance (so the mark budget is Theta(n), not n/log Delta as in [A, App. D])
C4  the CNF mechanism of [A, App. D] does not transfer: there, assignments with many violated clauses contribute 0
    to #SAT and are killed by parity checks; here every x contributes +-1 = sum_{Pi subset V(x)} (-2)^{|Pi|}, and the
    x with |V(x)| > nbar carry a nonzero total in general.
"""
import itertools
import random
import sys

FAILS = 0
TERMS = 0


def check(c, msg):
    global FAILS
    if not c:
        FAILS += 1
        print("  FAIL:", msg)


def popcount(v):
    return bin(v).count("1")


def run(seed, count):
    rng = random.Random(seed)
    trunc_fail_seen = False
    c4_seen = False
    global TERMS
    for _ in range(count):
        n = rng.randint(3, 7)
        nmono = n + n * (n - 1) // 2 + n * (n - 1) * (n - 2) // 6
        m = rng.randint(1, min(14, nmono))
        T = set()
        while len(T) < m:
            d = rng.choice([1, 2, 3, 3])
            T.add(sum(1 << i for i in rng.sample(range(n), d)))
        T = sorted(T)
        gap = 0
        nviol = {}
        for x in range(1 << n):
            v = sum(1 for t in T if x & t == t)
            gap += -1 if v % 2 else 1
            nviol[x] = v
        # C1 / C2
        exact = 0
        trunc = 0
        bymarks = {}
        for r in range(0, m + 1):
            for S in itertools.combinations(T, r):
                cov = 0
                for t in S:
                    cov |= t
                term = (-2) ** r * 2 ** (n - popcount(cov))
                TERMS += 1
                exact += term
                if r <= n + 1:
                    trunc += term
                bymarks[r] = bymarks.get(r, 0) + term
                if r > popcount(cov) + 1:
                    check(term % (1 << (n + 2)) == 0, "C3 valuation")
        check(exact == gap, "C1 exact expansion")
        M = 1 << (n + 2)
        res = trunc % M
        if res >= M // 2:
            res -= M
        check(res == gap, "C2 2-adic truncation")
        # C3: a shorter truncation n' = n//2 fails somewhere
        short = sum(v for r, v in bymarks.items() if r <= max(1, n // 2)) % M
        if short >= M // 2:
            short -= M
        if short != gap:
            trunc_fail_seen = True
        # C4: assignments with many 'violated' monomials still contribute
        nbar = max(1, n // 3)
        heavy = sum((-1) ** v for x, v in nviol.items() if v > nbar)
        if heavy != 0:
            c4_seen = True
    check(trunc_fail_seen, "C3: short truncation never failed (no sharpness witness)")
    check(c4_seen, "C4: no instance with nonzero heavy contribution")
    return trunc_fail_seen, c4_seen


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    print("witnesses (short truncation fails, heavy x contribute):", run(seed, count))
    print("subset terms enumerated:", TERMS)
    print("PASS" if FAILS == 0 else f"FAIL ({FAILS} failures)")
