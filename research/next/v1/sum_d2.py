# Control: same game, 4x4 disjointness matrix, but NO cancellation (0/1 rectangles partitioning the ones).
import itertools, pickle
from ovgame import tau_star
n = 4
ones = [(a, b) for a in range(n) for b in range(n) if a & b == 0]
rects = []
for A in range(1, 16):
    for B in range(1, 16):
        cells = [(a, b) for a in range(n) if A >> a & 1 for b in range(n) if B >> b & 1]
        if all(c in ones for c in cells): rects.append((A, B, frozenset(cells)))
profs = set()
def rec(left, r, c):
    if not left: profs.add((tuple(r), tuple(c))); return
    cell = min(left)
    for A, B, cells in rects:
        if cell in cells and cells <= left:
            r2 = [r[a] + (A >> a & 1) for a in range(n)]; c2 = [c[b] + (B >> b & 1) for b in range(n)]
            rec(left - cells, r2, c2)
rec(frozenset(ones), [0]*n, [0]*n)
dom = lambda p, q: all(x <= y for x, y in zip(q[0] + q[1], p[0] + p[1])) and q != p
pl = list(profs); par = [p for p in pl if not any(dom(p, q) for q in pl)]
base = [([1, 1], [2, 1], 1), ([2, 1], [1, 1], 1), ([1, 2], [1, 2], 1)]
print("no-cancellation profiles:", len(pl), "Pareto:", len(par))
print("tau* no cancellation, d0<=2:", tau_star(base[:2] + [(list(r), list(c), 2) for r, c in par]))
g2 = pickle.load(open("par_gf2_d2.pkl", "rb"))
print("GF(2) Pareto profiles not available without cancellation:", len([p for p in g2 if not any(dom(p, q) or p == q for q in pl)]), "of", len(g2))
