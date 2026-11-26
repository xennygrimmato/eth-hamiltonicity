"""Polymatroid (Shannon) LP for the subspace ansatz on Delta_3.

Hubs: points (u,v) of AG(2,3); class = u (vertical lines).  Nodes: the 9 non-vertical lines
n_{t,i} = {(u, i+t*u)}.  Edges of Delta_3: (n_{t,i}, n_{t,i+1}).
Ansatz: hub (u,v) is a k-dimensional subspace V_h of K^N (a 0/1 filtration), W_n = sum of the three
hubs of n, and W_n, W_n' independent for parallel nodes.  Then the placement value is sqrt(k/w),
w = max dim W_n.  Records: trees 2/3 <-> w/k = 9/4; cap 1/sqrt2 <-> w/k = 2.

This script minimises w over all polymatroids (rank functions) with r(h) = 1 -- a lower bound for
w/k over subspace arrangements (rank functions of subspace arrangements are polymatroids).
"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

H = [(u, v) for u in range(3) for v in range(3)]
idx = {h: i for i, h in enumerate(H)}
def line(t, i): return frozenset(idx[(u, (i + t*u) % 3)] for u in range(3))
nodes = {(t, i): line(t, i) for t in range(3) for i in range(3)}
def mask(S): return sum(1 << i for i in S)

NV = 1 << 9
W = NV  # index of variable w
rows = []; rhs = []
def add(coefs, b):
    rows.append(coefs); rhs.append(b)
full = NV - 1
# monotone: r(full) >= r(full - i)
for i in range(9):
    add({full ^ (1 << i): 1, full: -1}, 0)
# submodular elemental: r(S+i)+r(S+j) >= r(S+i+j)+r(S)
for i in range(9):
    for j in range(i+1, 9):
        for S in range(NV):
            if S >> i & 1 or S >> j & 1: continue
            c = {}
            for key, val in ((S | 1 << i | 1 << j, 1), (S, 1), (S | 1 << i, -1), (S | 1 << j, -1)):
                if key == 0: continue
                c[key] = c.get(key, 0) + val
            add(c, 0)
# r(n) <= w
for n in nodes.values():
    add({mask(n): 1, W: -1}, 0)
A = lil_matrix((len(rows), NV + 1))
for r, c in enumerate(rows):
    for key, val in c.items(): A[r, key] = val
Aeq = []; beq = []
def addeq(c, b): Aeq.append(c); beq.append(b)
for i in range(9): addeq({1 << i: 1}, 1)
mode = sys.argv[1] if len(sys.argv) > 1 else "pair"
for t in range(3):
    if mode == "pair":
        for i in range(3):
            a, b = mask(nodes[(t, i)]), mask(nodes[(t, (i+1) % 3)])
            addeq({a | b: 1, a: -1, b: -1}, 0)
    elif mode == "triple":   # all three parallel nodes jointly independent
        a, b, c = (mask(nodes[(t, i)]) for i in range(3))
        addeq({a | b | c: 1, a: -1, b: -1, c: -1}, 0)
E = lil_matrix((len(Aeq), NV + 1))
for r, c in enumerate(Aeq):
    for key, val in c.items(): E[r, key] = val
cost = np.zeros(NV + 1); cost[W] = 1
bounds = [(0, 0)] + [(0, None)] * NV
res = linprog(cost, A_ub=A.tocsr(), b_ub=rhs, A_eq=E.tocsr(), b_eq=beq, bounds=bounds, method="highs")
print(mode, res.status, "min w/k =", res.fun, " value sqrt(k/w) =", (1/res.fun) ** 0.5)
r = res.x
print("r(full) =", r[full])
print("r(nodes) =", [round(r[mask(n)], 4) for n in nodes.values()])
print("r(classes) =", [round(r[mask([idx[(u, v)] for v in range(3)])], 4) for u in range(3)])
