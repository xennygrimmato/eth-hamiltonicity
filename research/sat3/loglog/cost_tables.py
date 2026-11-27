#!/usr/bin/env python3
"""Arithmetic behind research/sat3/loglog.md (no search, only the formulas of the note).

(1) Where log log n comes from: the bound (68) of the first paper's Appendix D with the clause density
    D = max(2, m/n) in place of the occurrence bound:  U/n <= 6k + 28 k log2(96 D log2(2D)),  against
    the clause network of its section 6 (U/n ~ k D up to a constant) -- the crossover density.
(2) Balancing sparsification against the engine:  minimise  eps + c e log2(D(eps))  over eps for
    D(eps) = eps^-a  (a = 2: Calabro, k = 3; a = 1/3: the lower bound of loglog.md):  the minimum is
    ~ a c e log2(1/e), i.e. Theta(e log log n) for every a > 0.
(3) Scale formula for adaptive parity checks:  cost/n ~ sum_t h_t * t  with  h_t = (1/n) log2 #{xi :
    m/2^(t+1) < |V(xi)| <= m/2^t},  for two model spectra: planted random (h_t = t/2^t) and example H
    (h_t = 1/2 for every t up to log2 D).
(4) Level identity on a planted random formula: densities C_1 < C_2 < ... with C_{j+1} = exp(c C_j / 2);
    marks at level j cost  n * C_{j+1} exp(-c C_j) * (c C_j):  the sum over the tower.
"""
from math import log2, exp, log, sqrt

def U_marks(k, D):
    return 6 * k + 28 * k * log2(96 * D * log2(2 * D))

if __name__ == "__main__":
    k = 3
    print("(1) U/n of the mark network (constants of (68), k=3) against a clause network with U/n = 2(k-1)D:")
    print("      D      marks U/n   clause-network U/n")
    for D in (2, 4, 16, 64, 256, 1024, 2 ** 20):
        print(f"  {D:7d}   {U_marks(k, D):9.1f}   {2 * (k - 1) * D:12.1f}")
    lo = 2
    while U_marks(k, lo) > 2 * (k - 1) * lo:
        lo += 1
    print(f"    crossover at D = {lo}; growth of the mark network: 28k = {28 * k} bits per variable per doubling of D")

    print("(2) min over eps of eps + c e log2(eps^-a), c = 1, in units of e log2(1/e):")
    print("    log2 n     a=2     a=1/3")
    for L in (2 ** 10, 2 ** 20, 2 ** 40, 2 ** 80):
        e = L ** -0.5
        row = []
        for a in (2.0, 1.0 / 3):
            best = min(eps + e * a * log2(1 / eps) for eps in [e * 2 ** (j / 8) for j in range(-80, 200)] if eps < 1)
            row.append(best / (e * log2(1 / e)))
        print(f"    2^{int(log2(L)):<3d}   {row[0]:6.3f}  {row[1]:6.3f}   (limits: 2 and 1/3)")

    print("(3) scale formula, cost/n = sum_{t<=log2 D} h_t * t:")
    print("      D     planted (h_t = t/2^t)   example H (h_t = 1/2)")
    for D in (4, 16, 256, 2 ** 16, 2 ** 32):
        T = int(log2(D))
        pl = sum(t * t / 2 ** t for t in range(1, T + 1))
        hh = sum(0.5 * t for t in range(1, T + 1))
        print(f"  {D:10d}   {pl:10.3f}              {hh:10.1f}")
    print("    (single finest scale only, as in both papers: H costs ~ (1/2) log2 D per variable; the multi-scale")
    print("     sum is worse for H, bounded for planted formulas)")

    print("(4) level identity on a planted formula, c = 0.2, C_1 = 60:")
    c = 0.2; C = 60.0; tot = 0.0; j = 1
    while c * C / 2 < 700 and j < 8:
        Cn = exp(c * C / 2)
        cost = Cn * exp(-c * C) * (c * C)
        tot += cost
        print(f"    level {j}: C_j = {C:.3g}, next density {Cn:.3g}, marks cost/n = {cost:.3g}")
        C = Cn; j += 1
    print(f"    total marks cost/n over the tower: {tot:.3g}  (plus k*C_1 for the exact first level)")
