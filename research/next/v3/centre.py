"""rho_2 as the metric "1 on edges, sqrt 2 on non-edges" of the bilinear forms graph, and its common centre.

1. adjacency spectrum of the rank-one graph on Mat_2(F_2)
2. chain of forced midpoints: every rank-two pair is linked to (0, I) through flat squares, so all 48 pairs have
   the same midpoint m and all 16 points are at distance 1/sqrt 2 from it
3. the 5-point table of K_{2,3} = {0, I, three tips} is not Euclidean
"""
import itertools, numpy as np
from rank2 import mats, rk, add, cell, Z, I

A = np.array([[1.0 if rk[add(a, b)] == 1 else 0.0 for b in mats] for a in mats])
ev = np.round(np.linalg.eigvalsh(A), 6); vals, cnt = np.unique(ev, return_counts=True)
print("rank-one graph: degree %d, eigenvalues %s" % (int(A[0].sum()), dict(zip(vals.tolist(), cnt.tolist()))))
print("  least eigenvalue < -2, so the 1 / sqrt 2 metric is not Euclidean (centred Gram = P(I + A/2)P)")

# flat squares: {a, c, b, d} with rk(a-b) = rk(c-d) = 2 and all four sides of rank one.  Then mid[a,b] = mid[c,d].
pairs = [frozenset((a, b)) for a, b in itertools.combinations(mats, 2) if rk[add(a, b)] == 2]
parent = {p: p for p in pairs}
def find(p):
    while parent[p] != p: parent[p] = parent[parent[p]]; p = parent[p]
    return p
for p, q in itertools.combinations(pairs, 2):
    if p & q: continue
    a, b = tuple(p); c, d = tuple(q)
    if all(rk[add(x, y)] == 1 for x in (a, b) for y in (c, d)): parent[find(p)] = find(q)
classes = {find(p) for p in pairs}
print("rank-two pairs: %d; classes under 'opposite diagonals of a flat unit square': %d" % (len(pairs), len(classes)))
print("  one class => one common midpoint m, at distance 1/sqrt 2 from all 16 points; rank-one pairs subtend a right angle at m")

tips = [cell[(0, 1)], cell[(1, 2)], cell[(2, 0)]]; five = [Z, I] + tips
D2 = np.array([[rk[add(a, b)] for b in five] for a in five], float); J = np.eye(5) - np.ones((5, 5))/5
print("K_{2,3} table {0, I, tips}: squared distances\n", D2.astype(int))
print("  centred Gram eigenvalues", np.round(np.linalg.eigvalsh(-J @ D2 @ J/2), 4), "(negative => not Euclidean)")
