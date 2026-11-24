# Single-price hub method on Delta_3 with three merges (rows, columns, diagonals).
# For a pseudometric on legs+hubs, a piece selected by the price satisfies
#   c_k >= (L - H_k)/delta_k  (units of lambda), L = sum of edge lengths,
#   H_k = sum over legs of distance to own hub under merge k, delta_k = max hub-pair distance.
# We maximise sum_{k in S} (L - H_k)/delta_k over ALL pseudometrics (an upper bound for prices).
import itertools, sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

nodes = [(r, c) for r in range(3) for c in range(3)]
tri = {v: (v[0] + v[1]) % 3 for v in nodes}
legs = []   # (node, other node)
for u in nodes:
    for v in nodes:
        if u != v and tri[u] == tri[v]:
            legs.append((u, v))
edges = [(i, legs.index((b, a))) for i, (a, b) in enumerate(legs) if a < b]
assert len(legs) == 18 and len(edges) == 9
merge = {'R': lambda v: v[0], 'C': lambda v: v[1], 'D': lambda v: (v[0] - v[1]) % 3}

def solve(S, delta):
    pts = [('leg', i) for i in range(18)] + [('hub', k, g) for k in S for g in range(3)]
    n = len(pts)
    idx = {}
    for a, b in itertools.combinations(range(n), 2):
        idx[(a, b)] = len(idx)
    def var(a, b):
        return idx[(min(a, b), max(a, b))]
    m = len(idx)
    cobj = np.zeros(m)
    for k in S:
        w = 1.0 / delta[k]
        for (a, b) in edges:
            cobj[var(a, b)] -= w   # maximise L
        for i, (u, v) in enumerate(legs):
            h = pts.index(('hub', k, merge[k](u)))
            cobj[var(i, h)] += w
    rows = []
    trip = list(itertools.combinations(range(n), 3))
    A = lil_matrix((3 * len(trip), m))
    r = 0
    for (a, b, c) in trip:
        for (x, y, z) in ((a, b, c), (a, c, b), (b, c, a)):
            # d(x,y) <= d(x,z) + d(z,y)
            A[r, var(x, y)] = 1; A[r, var(x, z)] = -1; A[r, var(z, y)] = -1; r += 1
    ub = np.zeros(3 * len(trip))
    bounds = [(0, None)] * m
    for k in S:
        for g, g2 in itertools.combinations(range(3), 2):
            a = pts.index(('hub', k, g)); b = pts.index(('hub', k, g2))
            bounds[var(a, b)] = (0, delta[k])
    # normalise: all distances <= some big constant to keep bounded
    bounds = [(lo, hi if hi is not None else 50.0) for lo, hi in bounds]
    res = linprog(cobj, A_ub=A.tocsr(), b_ub=ub, bounds=bounds, method='highs')
    d = res.x
    L = sum(d[var(a, b)] for a, b in edges)
    out = {}
    for k in S:
        H = sum(d[var(i, pts.index(('hub', k, merge[k](u))))] for i, (u, v) in enumerate(legs))
        out[k] = (L - H) / delta[k]
    return -res.fun, out, L

if __name__ == '__main__':
    for S in (['R'], ['R', 'C'], ['R', 'C', 'D']):
        best = None
        grid = [0.25, 0.5, 1, 2, 4] if len(S) > 1 else [1]
        for ts in itertools.product(grid, repeat=len(S) - 1):
            delta = dict(zip(S, (1,) + ts))
            val, out, L = solve(S, delta)
            if best is None or val > best[0] + 1e-9:
                best = (val, delta, out, L)
            print(S, delta, round(val, 4), {k: round(x, 4) for k, x in out.items()}, flush=True)
        print('BEST', S, best, flush=True)
