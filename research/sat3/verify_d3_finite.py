#!/usr/bin/env python3
"""Independent finite check of the Delta3 nine-tripod configuration (no far-leg formula).
Points live in the l2-product of nine tripods; a point is a list of (arm, radius) per factor.
Legs are explicit points at distance M along the geodesic lines; value_k = (L - H_k)/delta_k."""
import math, itertools
nodes = [(r, c) for r in range(3) for c in range(3)]
def lines(n):  # (class, index) of the three merge lines through n
    r, c = n
    return [(0, r), (1, c), (2, (r - c) % 3)]
def d1(p, q):
    (a, x), (b, y) = p, q
    return abs(x - y) if (a == b or x == 0 or y == 0) else x + y
def dist(P, Q):
    return math.sqrt(sum(d1(p, q) ** 2 for p, q in zip(P, Q)))
rho = 1.0
# hub (k,g): in factor n0 it is on arm k at radius rho iff the line (k,g) passes through n0
def hub(k, g):
    return [((k, rho) if (k, g) in lines(n0) else (0, 0.0)) for n0 in nodes]
hubs = {(k, g): hub(k, g) for k in range(3) for g in range(3)}
edges = [((r, c), ((r + 1) % 3, (c - 1) % 3)) for r in range(3) for c in range(3)]
def run(M):
    L = 0.0; H = [0.0] * 3
    for (n, m) in edges:
        # factors n0 off the class-4 line of the edge: n0 shares line of class k1 with n and k2 with m
        legn, legm = [], []
        cnt = 0
        for n0 in nodes:
            sn = [k for (k, g) in lines(n) if (k, g) in lines(n0)]
            sm = [k for (k, g) in lines(m) if (k, g) in lines(n0)]
            if n0 not in (n, m) and len(sn) == 1 and len(sm) == 1:
                legn.append((sn[0], 1.0)); legm.append((sm[0], 1.0)); cnt += 1
            else:
                legn.append((0, 0.0)); legm.append((0, 0.0))
        s = M / math.sqrt(cnt)
        X = [(a, x * s) for a, x in legn]; Y = [(a, x * s) for a, x in legm]
        L += dist(X, Y)
        for k in range(3):
            H[k] += dist(X, hubs[lines(n)[k]]) + dist(Y, hubs[lines(m)[k]])
    out = []
    for k in range(3):
        delta = max(dist(hubs[(k, a)], hubs[(k, b)]) for a, b in itertools.combinations(range(3), 2))
        out.append((L - H[k]) / delta)
    return out
for M in (1e2, 1e4, 1e6):
    print(M, [round(v, 6) for v in run(M)])
print("flat 3*sqrt3 =", 3 * math.sqrt(3), "; cap 9/sqrt2 =", 9 / math.sqrt(2))
