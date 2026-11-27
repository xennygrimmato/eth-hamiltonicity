#!/usr/bin/env python3
"""Route 1/2 of research/sat3/loglog.md: lower bounds for sparsification on the same variables.

Formula T(b, J): J blocks of b variables, all clauses (-x v -y v -z) on three variables of one block
("at most two ones per block"); n = bJ variables, C(b,3) J clauses, |SAT| = (1 + b + C(b,2))^J.

(1) Fibre lemma (Lemma F): if chi is a CNF of width <= 3 on b variables whose satisfying assignments
    all have weight <= 2, and M is the number of its clauses with at least two negative literals, then
    |SAT(chi)| <= 3b + 2 + 3M.   Randomised adversarial search for a counterexample, b = 6..10.

(2) Numbers for the two lower bounds:
    (a) pieces that are restrictions (branching on variables):   density c  needs  2^{eps n} pieces
        with  eps >= 1/(15 sqrt(c+1) + 1);
    (b) pieces that are arbitrary 3-CNFs on the same variables:  eps >= 1/(69400 c^3)  (c >= 1).
    Printed against Calabro's upper bound  O(eps^-2 log^2(1/eps))  (constant set to 1).
"""
import random, sys
from math import comb, log2, sqrt, ceil

def sat_set(b, clauses):
    out = []
    for x in range(1 << b):
        ok = True
        for neg, pos in clauses:
            # clause false iff all neg vars are 1 and all pos vars are 0
            if (x & neg) == neg and (x & pos) == 0:
                ok = False; break
        if ok:
            out.append(x)
    return out

def random_chi(b, rng, p_types):
    """Add clauses until no satisfying assignment has weight >= 3."""
    clauses = []
    while True:
        S = sat_set(b, clauses)
        heavy = [x for x in S if bin(x).count("1") >= 3]
        if not heavy:
            return clauses, S
        x = rng.choice(heavy)
        ones = [i for i in range(b) if (x >> i) & 1]
        zeros = [i for i in range(b) if not (x >> i) & 1]
        r = rng.random()
        nneg = 3 if r < p_types[0] else (2 if r < p_types[0] + p_types[1] else (1 if r < sum(p_types[:3]) else 0))
        nneg = min(nneg, len(ones))
        npos = rng.randint(0, min(3 - nneg, len(zeros)))
        if nneg + npos == 0:
            npos = 1 if zeros else 0
            nneg = 0 if zeros else 1
        negs = rng.sample(ones, nneg); poss = rng.sample(zeros, npos)
        clauses.append((sum(1 << i for i in negs), sum(1 << i for i in poss)))

def fibre_test(trials, rng):
    worst = 0.0; viol = 0; best = {}
    for t in range(trials):
        b = rng.randint(6, 10)
        w = [rng.random() for _ in range(4)]
        # bias towards few clauses with >= 2 negatives in half of the runs
        if t % 2 == 0:
            w[0] *= 0.3; w[1] *= 0.3
        s = sum(w); p = [x / s for x in w]
        cl, S = random_chi(b, rng, p)
        M = sum(1 for neg, pos in cl if bin(neg).count("1") >= 2)
        bound = 3 * b + 2 + 3 * M
        if len(S) > bound:
            viol += 1
        worst = max(worst, len(S) / bound)
        key = (b, M)
        best[key] = max(best.get(key, 0), len(S))
    return viol, worst, best

def eps_restr(c):
    return 1.0 / (15 * sqrt(c + 1) + 1)

def eps_gen(c):
    return 1.0 / (69400 * c ** 3)

if __name__ == "__main__":
    rng = random.Random(7)
    viol, worst, best = fibre_test(4000, rng)
    print(f"(1) fibre lemma |SAT| <= 3b+2+3M: violations {viol}/4000, max |SAT|/bound = {worst:.3f}")
    for b in (8, 10):
        row = sorted((M, v) for (bb, M), v in best.items() if bb == b)[:8]
        print(f"    b={b}: (M, max |SAT| found) {row}   ball = {1 + b + comb(b, 2)}")
    print("(2) density c forced at 2^{eps n} pieces (lower bounds), and Calabro's eps^-2 log^2(1/eps):")
    print("    log2(1/eps)   restrictions c>=   general c>=   upper ~")
    for L in (4, 6, 8, 10, 12, 16, 20):
        eps = 2.0 ** (-L)
        # invert eps_restr: c+1 = ((1/eps - 1)/15)^2 ; eps_gen: c = (1/(69400 eps))^(1/3)
        c_r = max(0.0, ((1 / eps - 1) / 15) ** 2 - 1)
        c_g = (1 / (69400 * eps)) ** (1 / 3)
        up = eps ** -2 * L * L
        print(f"    {L:10d}   {c_r:14.3g}   {c_g:11.3g}   {up:9.3g}")
    # what it means for the exponent: cost  eps n + C e n log2(density(eps)),  e = (log n)^(-1/2)
    print("(3) log2(density) at eps = e = (log2 n)^(-1/2), in units of log2 log2 n:")
    for ln in (2 ** 10, 2 ** 20, 2 ** 40, 2 ** 80):
        e = ln ** -0.5; lln = log2(ln)
        c_r = max(1.0, ((1 / e - 1) / 15) ** 2 - 1); c_g = max(1.0, (1 / (69400 * e)) ** (1 / 3))
        print(f"    log2 n = 2^{int(log2(ln))}: restrictions {log2(c_r) / lln:.3f} (-> 1), general {log2(c_g) / lln:.3f} (-> 1/6)")
    sys.exit(0 if viol == 0 else 1)
