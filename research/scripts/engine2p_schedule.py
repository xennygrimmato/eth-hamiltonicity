#!/usr/bin/env python3
"""engine2p_schedule.py -- mechanism 5 (dense/sparse splits, non-uniform schedules) and the
decomposition-convexity lemma of mechanism 1, for research/engine2-probabilistic.md.

Units: a (K,lam)-clique costs 2^{e K^2 lam}; E = K(K-1)/2 edges; brute force e_bf = (K-1)/(2K).

(A) Prefix / bit-split lemma.  Brute-forcing lam1 bits of every edge and recursing on the
    remaining lam2 = lam - lam1 bits costs 2^{lam1*E + e*K^2*lam2}.  Since E >= e K^2 for every
    achievable e (e <= e_bf), the exponent is >= e K^2 lam: no split helps.  Checked over a grid.

(B) Decomposition convexity.  Decompose the equality I_D on a set S of edges into m terms of
    rank <= 2^{lam'} each (m >= 2^{lam-lam'}) and recurse: exponent |S| log m + e(K^2 lam - |S|(lam-lam'))
    >= e K^2 lam iff log m >= e(lam - lam') ... with m >= 2^{lam-lam'} this holds since e <= 1.
    More precisely with E edges: exponent = E log2 m + e K^2 (lam - log2 m) >= e K^2 lam iff
    E >= e K^2.  Checked.

(C) Schedules.  General one-level recurrence (Theorem A(b), Prop. 3 with a g x g grid):
        e' = (rho + a*K/g) e + b/K,   K' = g^2,   g >= K (any power of two).
    DP over schedules: for each reachable lg K' (up to a cap) keep the smallest e.  Compare the
    optimum with the lower bound e >= (1/2) rho^{floor(log2(lg K / lg K0))} and with Anthropic's
    fixed schedule g = 2^{3l+x0} K.  Also the fixed point e* = t/(4(1-rho)) when the piece count
    is 2^{t lam}.
"""
from fractions import Fraction as Fr
from math import log2, sqrt, floor

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL "), name)
    ok = ok and cond

# (A) prefix lemma
print("(A) bit-split lemma: exponent(lam1) - e K^2 lam >= 0 for all splits")
worst = None
for K in (3, 4, 8, 16, 64):
    E = K*(K-1)//2
    ebf = Fr(K-1, 2*K)
    for e in (Fr(1,4), Fr(1,8), Fr(1, K), Fr(K-1, K*K), ebf):
        if e > ebf: continue
        for lam in (1, 2, 5, 10):
            for lam1 in range(0, lam+1):
                expo = lam1*E + e*K*K*(lam-lam1)
                d = expo - e*K*K*lam
                if worst is None or d < worst: worst = d
check("bit-split never lowers the exponent (min difference = %s)" % worst, worst >= 0)

# (B) decomposition convexity, m terms per edge of rank 2^{lam - log2 m}
print("(B) decomposition convexity: E log m + e K^2 (lam - log m) >= e K^2 lam")
worst = None
for K in (3, 4, 8, 16, 64):
    E = K*(K-1)//2
    for e in (Fr(1,4), Fr(1,8), Fr(1,K), Fr(K-1,2*K)):
        for lam in (2, 5, 10):
            for lm in range(0, lam+1):           # log2 m = lam - lam'
                d = E*lm + e*K*K*(lam-lm) - e*K*K*lam
                if worst is None or d < worst: worst = d
check("decomposition never lowers the exponent (min difference = %s)" % worst, worst >= 0)

# (C) schedules
def dp_schedules(rho, x0=18, a=1.0, b=3.0, lg_cap=4000, max_jump=200):
    """state: lgK -> best e.  transitions: g = 2^{lgK + j}, j = 0..max_jump, K' = g^2."""
    best = {x0: 0.5}
    frontier = [x0]
    while frontier:
        new = []
        for lgK in frontier:
            e = best[lgK]
            for j in range(0, max_jump+1):
                lgg = lgK + j
                lgKp = 2*lgg
                if lgKp > lg_cap: break
                ep = (rho + a*2.0**(-j))*e + b*2.0**(-lgK)
                if ep < best.get(lgKp, 9):
                    best[lgKp] = ep
                    new.append(lgKp)
        frontier = sorted(set(new))
    return best

rho = 1/sqrt(2)
best = dp_schedules(rho)
alpha = log2(1/rho)
print("(C) schedule DP, rho = 1/sqrt2, x0 = 18: lgK, best e, e*(lgK)^alpha, lower bound (1/2)rho^L")
viol = False
rows = []
for lgK in sorted(best):
    L = floor(log2(lgK/18))
    lb = 0.5*rho**L
    rows.append((lgK, best[lgK], best[lgK]*lgK**alpha, lb))
    if best[lgK] < lb - 1e-12: viol = True
for r in rows[:6] + rows[-4:]:
    print("   lgK=%5d  e=%.4f  e*lgK^a=%.3f  LB=%.4f" % r)
check("every schedule obeys e >= (1/2) rho^{floor(log2(lgK/lgK0))}", not viol)
# Anthropic's own schedule for comparison
K = 2**18; e = 0.5; l = 0; anth = []
while K.bit_length()-1 <= 4000:
    anth.append((K.bit_length()-1, e))
    e = (rho + 3*2.0**(-l-5))*e + (3.0/K if K < 2**1000 else 0.0)
    K = (2**(3*l+18)*K)**2; l += 1
print("   Anthropic fixed schedule: ", ["(%d, %.4f)" % t for t in anth])
ratio = max(best[lg]*lg**alpha for lg in best if lg >= 200) / min(best[lg]*lg**alpha for lg in best if lg >= 200)
print("   spread of e*(lgK)^alpha over optimal schedules (lgK>=200): factor %.2f" % ratio)
check("optimal schedules change e only by a bounded factor (<= 4) at the same rate", ratio <= 4)

# fixed point with 2^{t lam} pieces
for t in (0.0, 0.01, 0.1, 1.0, 2.0):
    e = 0.5
    for _ in range(200): e = rho*e + t/4
    print("   t=%.2f: fixed point e* = %.4f (formula t/(4(1-rho)) = %.4f)" % (t, e, t/(4*(1-rho))))
check("fixed point matches t/(4(1-rho))", abs(e - 2.0/(4*(1-rho))) < 1e-9)
print("ALL PASS" if ok else "SOME FAIL")
