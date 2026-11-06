"""q3_threemerge.py -- (a) independent recomputation of the asymptotic flattening certificate D on Delta_3 with merges
rows, cols (2 merges) and rows, cols, diagonals r-c (3 merges), with the per-merge LP of flatcert.py solved by linprog
(not the closed form), over all 3^9 orientations; distribution of the certified value.
(b) finite exact test with a third merge: f = R + C + D (row, column, diagonal networks, bonds (2,2,2)) and
R + C + D with other bond patterns."""
import itertools, numpy as np
from scipy.optimize import linprog
from flat_finite import bound
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
merges = {'rows': lambda v: v[0], 'cols': lambda v: v[1], 'diags': lambda v: (v[0] - v[1]) % 3}
pairs = [(0, 1), (0, 2), (1, 2)]
def lp3(n):
    A = [[-1, -1, 0], [-1, 0, -1], [0, -1, -1]]   # e01+e02 >= |n0|, e01+e12 >= |n1|, e02+e12 >= |n2|
    r = linprog(np.ones(3), A_ub=A, b_ub=[-abs(x) for x in n], bounds=[(0, None)] * 3, method='highs')
    return round(r.fun, 9)
cache = {}
def d(n):
    k = tuple(sorted(abs(x) for x in n))
    if k not in cache: cache[k] = lp3(n)
    return cache[k]
for ms in (('rows', 'cols'), ('rows', 'cols', 'diags')):
    best = -1; hist = {}; arg = None
    for o in itertools.product((0, 1, -1), repeat=9):
        if not any(o): continue
        flow = {v: 0 for v in nodes}
        for (u, v), oe in zip(edges, o): flow[u] += oe; flow[v] -= oe
        val = min(d([sum(flow[v] for v in nodes if merges[m](v) == g) for g in range(3)]) for m in ms)
        hist[val] = hist.get(val, 0) + 1
        if val > best: best, arg = val, o
    print(f'merges {ms}: flattening certificate D = {best} of 9 (rho >= {best/9:.4f}); attained at o = {arg}; histogram {dict(sorted(hist.items()))}')
def finite(terms, label):
    worst = None
    for o in itertools.product((0, 1, -1), repeat=9):
        if not any(o): continue
        xs = {m: [0]*3 for m in merges}; ys = {m: [0]*3 for m in merges}
        for (u, v), oe in zip(edges, o):
            if oe == 0: continue
            a, b = (u, v) if oe == 1 else (v, u)
            for m, gf in merges.items(): xs[m][gf(a)] += 1; ys[m][gf(b)] += 1
        rk = 2 ** sum(1 for x in o if x)
        tot = sum(bound(xs[m], ys[m], b) for m, b in terms)
        if worst is None or tot - rk < worst[0]: worst = (tot - rk, rk, tot, o)
    print(f'finite test {label}: worst slack {worst[0]} (rank {worst[1]}, sum of bounds {worst[2]}, o = {worst[3]})', '-> REFUTED' if worst[0] < 0 else '-> passes')
finite([('rows', (2, 2, 2)), ('cols', (2, 2, 2))], 'R+C (2,2,2)')
finite([('rows', (2, 2, 2)), ('cols', (2, 2, 2)), ('diags', (2, 2, 2))], 'R+C+D (2,2,2)')
finite([('rows', (2, 2, 2)), ('diags', (2, 2, 2))], 'R+D (2,2,2)')
finite([('rows', (2, 2, 2)), ('cols', (2, 2, 2)), ('diags', (2, 2, 2)), ('rows', (2, 2, 2))], 'R+C+D+R (2,2,2)')
finite([('rows', (2, 2, 4)), ('cols', (2, 2, 4)), ('diags', (2, 2, 4))], 'R+C+D (2,2,4)')
