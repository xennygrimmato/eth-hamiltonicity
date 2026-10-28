"""Checks for Section 5 of research/tsp-theorem.md (weights beyond poly(n)).

Run: python3 tsp_largew.py [seed]

L1  residue counting cannot determine the optimum: two weightings of one graph with exactly two
    Hamiltonian cycles, tour weights {4,5} and {1,2}, have identical residue-class counts
    N_q(j) = #{H : w(H) = j mod q} for q = 2 and q = 3 (and for q = 6), computed through the
    product-form identity with exponents reduced mod q; the optima differ.  (Section 5.3.)
L2  the Kronecker integer sum_X Y^{w(X)} tau(X) has about b (n W + 1) bits: measured bit-lengths
    on a fixed graph with all weights = W, for W = 1, 2, 4, ..., 64, against the formula.
    (Section 5.2: B is linear in W, so W = 2^{o(n)} is the exact limit of Theorem TSP-1'.)
L3  the window lemma for truncated weights: with w'_e = floor(w_e / 2^s) and h* = min_H w'(H),
    2^s h* <= OPT < 2^s (h* + n), on random instances with 40-bit weights.
L4  the (1+eps)-approximation by scaling with the heaviest-edge guess (Proposition 5.4):
    output <= (1+eps) OPT, eps = 1/2, 1/4, 1/8, exact brute-force OPT for comparison.
"""
import random
import sys

from tsp_lib import *


FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def residue_counts(n, E, w, q, Y_b=None):
    """N_q(j) = #{H : w(H) = j (mod q)} via the product-form sum
       sum_X Y^{sum_{e in X} (w_e mod q)} tau(X) / n,  then folding exponents mod q."""
    wq = [x % q for x in w]
    P = twofactor_poly(n, E, wq)             # exponents are sums of residues, < n q
    out = [0] * q
    for e, c in P.items():
        assert c % n == 0
        out[e % q] += c // n
    return out


def two_cycle_graph():
    """a graph with exactly two Hamiltonian cycles: C_6 plus the chord {0,3}... has 1; use the
    'theta' of two 5-cycles sharing a path: vertices 0..5, edges of C_6 = 0-1-2-3-4-5-0 plus
    chords 0-2 and 3-5: Hamiltonian cycles are 0-1-2-3-4-5-0 and 0-2-1-... no.  We search."""
    rng = random.Random(3)
    while True:
        n = 6
        E = random_graph(n, 8, rng, min_deg2=True)
        H = ham_cycles(n, E)
        if len(H) == 2 and H[0] != H[1]:
            return n, E, H


def main(seed=1):
    rng = random.Random(seed)
    # ---- L1
    n, E, (H1, H2) = two_cycle_graph()
    m = len(E)
    priv1 = sorted(H1 - H2); priv2 = sorted(H2 - H1)
    assert priv1 and priv2
    def weighting(a, b):
        w = [0] * m
        w[priv1[0]] = a; w[priv2[0]] = b
        return w
    wA = weighting(4, 5); wB = weighting(1, 2)
    TA = tour_poly(n, E, wA); TB = tour_poly(n, E, wB)
    check(TA == {4: 1, 5: 1} and TB == {1: 1, 2: 1}, f"L1 tour weights {TA} {TB}")
    for q in (2, 3):
        NA = residue_counts(n, E, wA, q); NB = residue_counts(n, E, wB, q)
        check(NA == NB, f"L1 q={q}: {NA} vs {NB}")
        print(f"  L1 q={q}: residue counts A={NA} B={NB} (equal), optima {plowest(TA)} vs {plowest(TB)}")
    check(plowest(TA) != plowest(TB), "L1 optima differ")
    # the modulus 6 = 2*3 > max tour weight distinguishes them, but counting mod 6 is the full
    # distribution: the modulus must exceed n W, which is the Kronecker degree (exponential bits).
    NA6 = residue_counts(n, E, wA, 6); NB6 = residue_counts(n, E, wB, 6)
    check(NA6 != NB6, "L1 q=6 (full distribution) should distinguish")
    print(f"  L1 q=6 (= prod of the primes, > nW): A={NA6} B={NB6} differ, as the full distribution")
    # ---- L2
    n2, E2 = 6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (0, 3), (1, 4), (2, 5)]
    b = len(E2) + 5
    rows = []
    for W in (1, 2, 4, 8, 16, 32, 64):
        w = [W] * len(E2)
        P = twofactor_poly(n2, E2, w)
        val = kron_eval(P, 1 << b)
        rows.append((W, val.bit_length(), b * (n2 * W + 1)))
    print("  L2 (W, bits of sum_X Y^{w(X)} tau(X), b(nW+1)):", rows)
    check(all(abs(bits - formula) <= b for W, bits, formula in rows), "L2 bits ~ b(nW+1)")
    check(rows[-1][1] > 20 * rows[0][1], "L2 growth")
    # ---- L3, L4
    for trial in range(10):
        n = rng.randint(5, 7)
        m = rng.randint(n + 2, min(2 * n, n * (n - 1) // 2))
        E = random_graph(n, m, rng, min_deg2=True)
        H = ham_cycles(n, E)
        if not H:
            continue
        L = 40
        w = [rng.randrange(1 << L) if rng.random() < 0.8 else rng.randrange(1 << (L // 2)) for _ in E]
        OPT = min(sum(w[k] for k in C) for C in H)
        # L3: window lemma
        for s in (L - 6, L - 10, L // 2, 0):
            wp = [x >> s for x in w]
            P = twofactor_poly(n, E, wp)
            hstar = plowest(P)
            check((hstar << s) <= OPT < ((hstar + n) << s), f"L3 s={s}: h*={hstar} OPT={OPT}")
        # L4: scaling with heaviest-edge guess
        for eps_inv in (2, 4, 8):
            best = None
            for f in range(m):
                Ef = [k for k in range(m) if w[k] <= w[f]]
                sub = [E[k] for k in Ef]
                if not ham_cycles(n, sub):
                    continue
                # scale: 2^s <= eps * w_f / n  (so the rounding error n 2^s <= eps w_f <= eps OPT_f)
                s = 0
                while (1 << (s + 1)) * n * eps_inv <= w[f]:
                    s += 1
                if (1 << s) * n * eps_inv > w[f]:
                    s = 0
                wp = [w[k] >> s for k in Ef]
                # optimal tour for the rounded weights by self-reduction (pinning edges out)
                keep = list(range(len(sub)))
                Pfull = twofactor_poly(n, sub, wp)
                h = plowest(Pfull)
                for k in range(len(sub)):
                    trial_keep = [x for x in keep if x != k]
                    Pk = twofactor_poly(n, [sub[x] for x in trial_keep], [wp[x] for x in trial_keep])
                    if plowest(Pk) == h:
                        keep = trial_keep
                tour = [sub[x] for x in keep]
                dg = [0] * n
                for (i, j) in tour:
                    dg[i] += 1; dg[j] += 1
                check(len(tour) == n and all(d == 2 for d in dg) and is_spanning_tree(n, tour[1:]),
                      f"L4 self-reduction did not return a Hamiltonian cycle: {tour}")
                val = sum(w[Ef[x]] for x in keep)
                best = val if best is None else min(best, val)
            check(best is not None and OPT <= best <= OPT + OPT // eps_inv, f"L4 eps=1/{eps_inv}: {best} vs OPT {OPT}")
        print(f"  trial {trial}: n={n} m={m} OPT={OPT} ({OPT.bit_length()} bits) approx ok")
    print("ALL CHECKS PASSED" if FAILS == 0 else f"{FAILS} FAILURES")
    return FAILS == 0


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    sys.exit(0 if main(seed) else 1)
