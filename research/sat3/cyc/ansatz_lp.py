"""Shannon (polymatroid) lower bound for the subspace ansatz on the 3-net of a group G.

Hubs: (class, value) for classes R, C, D (3|G| hubs).  Nodes (r,c) with hubs R_r, C_c, D_{r c^{-1}}.
Generic pairs of nodes: all three hubs differ.  Ansatz (cyclic-cap.md section 3): hub = k-dimensional
subspace V_h, W_n = sum of the three hubs of n, W_n and W_n' independent for every generic pair.
Then every generic edge has s^k = delta*sqrt(k/w) for all three merges, w = max dim W_n.
The LP minimises w over polymatroids with r(h) = 1: a lower bound for w/k.

usage: ansatz_lp.py GROUP     GROUP in Z3, Z4, Z5, Z2xZ2
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

name = sys.argv[1]
if name == "Z2xZ2":
    els = [0, 1, 2, 3]; sub = lambda a, b: a ^ b
else:
    g = int(name[1:]); els = list(range(g)); sub = lambda a, b: (a - b) % g
g = len(els); nh = 3*g
hub = lambda k, v: k*g + v
nodes = [(hub(0, r), hub(1, c), hub(2, sub(r, c))) for r in els for c in els]
generic = [(a, b) for a in range(len(nodes)) for b in range(a+1, len(nodes))
           if all(nodes[a][k] != nodes[b][k] for k in range(3))]
print(name, "hubs", nh, "nodes", len(nodes), "generic pairs", len(generic)); sys.stdout.flush()
mask = lambda S: sum(1 << i for i in S)
NV = 1 << nh; W = NV; full = NV - 1
ri, ci, vi = [], [], []; nrow = 0
def add(entries):
    global nrow
    for c, v in entries: ri.append(nrow); ci.append(c); vi.append(v)
    nrow += 1
for i in range(nh): add([(full ^ (1 << i), 1), (full, -1)])
allS = np.arange(NV)
for i in range(nh):
    for j in range(i+1, nh):
        S = allS[((allS >> i) & 1 == 0) & ((allS >> j) & 1 == 0)]
        m = len(S); rows = nrow + np.arange(m)
        bi, bj = 1 << i, 1 << j
        ri.extend(rows); ci.extend(S | bi | bj); vi.extend([1.0]*m)
        ri.extend(rows); ci.extend(S | bi); vi.extend([-1.0]*m)
        ri.extend(rows); ci.extend(S | bj); vi.extend([-1.0]*m)
        nz = S != 0
        ri.extend(rows[nz]); ci.extend(S[nz]); vi.extend([1.0]*int(nz.sum()))
        nrow += m
for n in nodes: add([(mask(n), 1), (W, -1)])
A = coo_matrix((vi, (ri, ci)), shape=(nrow, NV+1)).tocsr()
er, ec, ev = [], [], []; ne = 0
for i in range(nh): er.append(ne); ec.append(1 << i); ev.append(1.0); ne += 1
beq = [1.0]*nh
for a, b in generic:
    ma, mb = mask(nodes[a]), mask(nodes[b])
    er += [ne]*3; ec += [ma | mb, ma, mb]; ev += [1.0, -1.0, -1.0]; ne += 1; beq.append(0.0)
E = coo_matrix((ev, (er, ec)), shape=(ne, NV+1)).tocsr()
cost = np.zeros(NV+1); cost[W] = 1
t = time.time()
res = linprog(cost, A_ub=A, b_ub=np.zeros(nrow), A_eq=E, b_eq=beq,
              bounds=[(0, 0)] + [(0, None)]*NV, method="highs")
print(name, "status", res.status, "min w/k =", round(res.fun, 6), " sqrt(k/w) =", round((1/res.fun)**.5, 6),
      " r(all) =", round(res.x[full], 4), " time", round(time.time()-t, 1), "s")
