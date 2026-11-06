"""floor.py -- the flatcert (net-flow LP) flattening floor of Delta_3 with two merges (rows, columns):
D = max over orientations of min_k max_G |n_G| (closed form for 3 groups), in units of log2 N0, as a fraction of 9.
 N0 = 2: orientations in {0,+,-}^9 (reproduces flatcert4.out: 4 of 9);  N0 = 4: bit orientations (flat_bits.py: 4 of 9);
 N0 -> infinity: fractional orientations o in [-1,1]^9 (36 LPs: choice of the binding row group, column group and signs).  [C]"""
import itertools, numpy as np
from scipy.optimize import linprog
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
def flows(o):
    nr = np.zeros(3); nc = np.zeros(3)
    for (u, v), x in zip(edges, o):
        nr[u[0]] += x; nr[v[0]] -= x; nc[u[1]] += x; nc[v[1]] -= x
    return nr, nc
best = 0
for o in itertools.product((0, 1, -1), repeat=9):
    nr, nc = flows(o); best = max(best, min(np.abs(nr).max(), np.abs(nc).max()))
print(f'N0 = 2: D = {best} of 9')
# linear maps o -> n_G
Ar = np.zeros((3, 9)); Ac = np.zeros((3, 9))
for e, (u, v) in enumerate(edges):
    Ar[u[0], e] += 1; Ar[v[0], e] -= 1; Ac[u[1], e] += 1; Ac[v[1], e] -= 1
fb = -1
for G, sg, H, sh in itertools.product(range(3), (1, -1), range(3), (1, -1)):
    # max t s.t. t <= sg*Ar[G].o, t <= sh*Ac[H].o, -1 <= o <= 1
    A = np.array([np.r_[-sg * Ar[G], 1], np.r_[-sh * Ac[H], 1]])
    res = linprog(np.r_[np.zeros(9), -1], A_ub=A, b_ub=[0, 0], bounds=[(-1, 1)] * 9 + [(None, None)], method='highs')
    if -res.fun > fb: fb = -res.fun; ob = res.x[:9]
print(f'fractional (N0 -> infinity): D = {fb:.6f} of 9 at o = {np.round(ob, 3).tolist()}')
