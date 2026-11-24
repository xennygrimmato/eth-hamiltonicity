# K4 instance (the smallest three-merge case in the repo notes): 4 nodes, one wire of dimension N=2 on each of the 6 edges.
# Each node holds 3 legs.  Cuts = the three 2|2 splits of the nodes; each is crossed by 4 wires (rank 16).
import sys, itertools, numpy as np
from split import *
N = 2
edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
# 12 legs: leg id = (node, edge index); order legs so that a party = 3 consecutive legs
legs = [(a, e) for a in range(4) for e in range(6) if a in edges[e]]
pairs = [(legs.index((edges[e][0], e)), legs.index((edges[e][1], e))) for e in range(6)]
T12 = wires(N, pairs, 12)
side = lambda nodes: [i for i, (a, e) in enumerate(legs) if a in nodes]
C = [side({0, 1}), side({0, 2}), side({0, 3})]
print("cut ranks:", [np.linalg.matrix_rank(flatten(T12, c)[0]) for c in C]); sys.stdout.flush()
def search(cuts, tot, restarts=4, iters=800):
    hits = []
    for comp in itertools.product(range(tot+1), repeat=len(cuts)):
        if sum(comp) != tot or list(comp) != sorted(comp, reverse=True): continue
        r = best(T12, cuts, list(comp), restarts=restarts, iters=iters)
        print("    ranks", comp, "residual %.1e" % r); sys.stdout.flush()
        if r < 1e-9: hits.append(comp)
    return hits
for name, cuts, tots in [("two cuts", C[:2], [8, 7, 6]), ("three cuts", C, [7, 6, 5])]:
    print(name)
    for tot in tots:
        print("  total", tot); h = search(cuts, tot); print("  ->", h); sys.stdout.flush()
        if not h: break
