"""Tripod branch of Delta_3: every node n has a point z(n) that is the midpoint of all three pairs of its hubs."""
import sys, itertools
from relax import *
net = delta3()
H = [('h',) + h for h in net.hubs]
def Z(n): return ('z',) + tuple(sorted((('h',) + net.hub_of(n, k) for k in range(3)), key=repr))
Zs = [Z(n) for n in net.nodes]
edges = net.edges
def pts(level):
    P = list(Zs)
    if level >= 1:
        base = H + Zs
        P += [canon_mid(a, b) for a, b in itertools.combinations(base, 2)]
    if level >= 2:
        c0s = [canon_mid(Z(e[0]), Z(e[1])) for e in edges]
        base = H + Zs
        P += [canon_mid(c, a) for c in c0s for a in base if a != c]
    if level >= 3:
        c0s = [canon_mid(Z(e[0]), Z(e[1])) for e in edges]
        base = H + Zs
        L1 = [canon_mid(a, b) for a, b in itertools.combinations(base, 2)]
        P += [canon_mid(c0s[0], a) for a in L1 if a != c0s[0]]
    return P
for lev in map(int, sys.argv[1:]):
    print("TRIPOD branch with z-points, level", lev, flush=True)
    solve(net, pts(lev), lazy_triangle=2)
