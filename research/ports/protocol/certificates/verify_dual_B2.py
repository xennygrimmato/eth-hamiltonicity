#!/usr/bin/env python3
"""Exact LOWER bound (dual certificate) for the B = 2 bucket game.   python3 verify_dual_B2.py

Standard library only.  For a type tau and a price vector y >= 0 on the six supply edges with
sum y = 1: any mixture/routing has  max_edge load >= sum_edges y_e load_e
                                              >= sum_pairs min_option  sum_wires len(w) * dist_y(w),
where dist_y is the y-shortest path in K_{2,3} over ALL paths.  So the bound holds for the referee's
model (all simple paths) and a fortiori for the notes' model (fewer paths).  Here the rank bounds are
replaced by rational LOWER bounds (floor(D*sqrt)/D); loads are monotone in r, r', so this is a lower
bound for the game with the exact corner bounds sqrt(10)/3, 4/3.

Combined with cert_B2.json:  L_2 <= n*(2) <= c_2.
"""
import math
from fractions import Fraction as F
from verify import P, Q, A, VP, EDGES, option_wires, DEN

rho_lo = F(math.isqrt(DEN * DEN * 10 // 9), DEN)          # floor(D*sqrt(10/9))/D
assert rho_lo >= 0 and rho_lo * rho_lo <= F(10, 9)
# buckets for B = 2 (x in [0,10/9] and [10/9,20/9]); bucket 1 = (r, r') <= (sqrt(10)/3, 4/3)
BK = [(A, rho_lo), (rho_lo, A)]
WORST = (1, 1, 1)
a, b = F(207504941, 10 ** 9), F(117917490, 10 ** 9)
c = (1 - 2 * a - 2 * b) / 2
Y = dict(zip(EDGES, [a, b, c, c, b, a]))                  # u1v1,u1v2,u1v3,u2v1,u2v2,u2v3


def dist():
    INF = F(10 ** 9)
    d = [[F(0) if i == j else INF for j in range(5)] for i in range(5)]
    for (u, v), p in Y.items():
        d[u][v] = d[v][u] = min(d[u][v], p)
    for k in range(5):
        for i in range(5):
            for j in range(5):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    return d


def lower(tau):
    assert all(p >= 0 for p in Y.values()) and sum(Y.values()) == 1
    d = dist()
    tot = F(0)
    for e in range(3):
        r, rp = BK[tau[e]]
        tot += min(sum(l * d[x][y] for (x, y), l in option_wires(e, kind, o, o2, r, rp).items())
                   for kind in (0, 1) for o in range(5) for o2 in range(5))
    return tot


if __name__ == '__main__':
    L = lower(WORST)
    print('price y =', [str(Y[e]) for e in EDGES])
    print('type %s: n*(2) >= %s ~ %.10f' % (WORST, L, float(L)))
