"""Orbit-reduced Shannon LP for the subspace ansatz on the generic edges of the 3-net of Z_g.

Same LP as ansatz_lp.py, with the rank function assumed invariant under the automorphism group of the net
(affine maps of Z_g^2 permuting the three directions r, c, r-c).  The LP is convex and invariant, so the
optimum is unchanged.  usage: ansatz_lp_sym.py g
"""
import sys, time, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from math import gcd

g = int(sys.argv[1]); nh = 3*g
MODE = sys.argv[2] if len(sys.argv) > 2 else "all"   # "all": every non-collinear pair independent; "nospecial": drop the
# pairs with difference (a,b), b = -a, b = 2a or a = 2b (the pairs for which the 5/2 argument applies)
hub = lambda k, v: k*g + (v % g)
node_hubs = lambda r, c: (hub(0, r), hub(1, c), hub(2, r - c))
nodes = [(r, c) for r in range(g) for c in range(g)]
lines = {}
for k in range(3):
    for v in range(g):
        lines[frozenset(n for n in nodes if node_hubs(*n)[k] == hub(k, v))] = hub(k, v)
perms = set()
for a, b, c, d in itertools.product(range(g), repeat=4):
    if gcd((a*d - b*c) % g, g) != 1: continue
    for t in ((0, 0),):
        img = {}
        ok = True
        for L, h in lines.items():
            L2 = frozenset(((a*r + b*cc) % g, (c*r + d*cc) % g) for (r, cc) in L)
            if L2 not in lines: ok = False; break
            img[h] = lines[L2]
        if ok: perms.add(tuple(img[h] for h in range(nh)))
# translations
for tr in range(g):
    for tc in range(g):
        img = {}
        for L, h in lines.items():
            img[h] = lines[frozenset(((r + tr) % g, (cc + tc) % g) for (r, cc) in L)]
        perms.add(tuple(img[h] for h in range(nh)))
# close under composition (linear o translation)
lin = [p for p in perms]
G = set(lin)
frontier = list(G)
while frontier:
    new = []
    for p in frontier:
        for q in lin:
            r_ = tuple(p[q[i]] for i in range(nh))
            if r_ not in G: G.add(r_); new.append(r_)
    frontier = new
G = [np.array(p) for p in G]
print("g =", g, "hubs", nh, "|G| =", len(G)); sys.stdout.flush()
NV = 1 << nh
S = np.arange(NV, dtype=np.int64)
canon = S.copy()
t0 = time.time()
for p in G:
    im = np.zeros(NV, dtype=np.int64)
    for i in range(nh): im |= ((S >> i) & 1) << int(p[i])
    np.minimum(canon, im, out=canon)
reps, oid = np.unique(canon, return_inverse=True)
nvar = len(reps); W = nvar
print("orbits of subsets:", nvar, " (%.0f s)" % (time.time() - t0)); sys.stdout.flush()
mask = lambda T: sum(1 << i for i in T)
# pair orbits
seen = set(); pair_reps = []
for i in range(nh):
    for j in range(i+1, nh):
        if (i, j) in seen: continue
        pair_reps.append((i, j))
        for p in G:
            a, b = int(p[i]), int(p[j]); seen.add((min(a, b), max(a, b)))
rows = []
for (i, j) in pair_reps:
    T = S[((S >> i) & 1 == 0) & ((S >> j) & 1 == 0)]
    bi, bj = 1 << i, 1 << j
    R = np.stack([oid[T | bi | bj], oid[T], oid[T | bi], oid[T | bj]], axis=1)
    R[:, 2:] = np.sort(R[:, 2:], axis=1)
    rows.append(np.unique(R, axis=0))
R = np.unique(np.concatenate(rows), axis=0)
m = len(R); print("submodular rows:", m); sys.stdout.flush()
ri = np.repeat(np.arange(m), 4); ci = R.reshape(-1); vi = np.tile([1.0, 1.0, -1.0, -1.0], m)
full = NV - 1
extra_r = [m, m]; extra_c = [oid[full ^ 1], oid[full]]; extra_v = [1.0, -1.0]
ING = len(sys.argv) > 3 and sys.argv[3].startswith('ingleton')
if ING:
    # Ingleton inequalities (valid for subspace arrangements, not for all polymatroids):
    #   r(AB)+r(AC)+r(AD)+r(BC)+r(BD) >= r(A)+r(B)+r(ABC)+r(ABD)+r(CD)
    # for A,B,C,D among the single hubs (and the nodes, with 'ingleton2')
    sets = [1 << i for i in range(nh)]
    if sys.argv[3] == 'ingleton2': sets += sorted(set(mask(node_hubs(*n)) for n in nodes))
    sets = np.array(sets, dtype=np.int64); ns_ = len(sets)
    I, J = np.triu_indices(ns_, 1)
    rows_i = []
    for a, b in zip(I, J):
        A_, B_ = sets[a], sets[b]
        C_ = sets[I]; D_ = sets[J]
        keep = (I != a) & (I != b) & (J != a) & (J != b)
        C_, D_ = C_[keep], D_[keep]
        pos = np.stack([np.full(len(C_), oid[A_ | B_]), oid[A_ | C_], oid[A_ | D_], oid[B_ | C_], oid[B_ | D_]], axis=1)
        neg = np.stack([np.full(len(C_), oid[A_]), np.full(len(C_), oid[B_]), oid[A_ | B_ | C_], oid[A_ | B_ | D_], oid[C_ | D_]], axis=1)
        rows_i.append(np.unique(np.concatenate([np.sort(pos, axis=1), np.sort(neg, axis=1)], axis=1), axis=0))
    RI = np.unique(np.concatenate(rows_i), axis=0); mi = len(RI)
    print("Ingleton rows:", mi); sys.stdout.flush()
    ri2 = np.repeat(m + 1 + np.arange(mi), 10); ci2 = RI.reshape(-1); vi2 = np.tile([-1.0]*5 + [1.0]*5, mi)
    A = coo_matrix((np.concatenate([vi, extra_v, vi2]), (np.concatenate([ri, extra_r, ri2]), np.concatenate([ci, extra_c, ci2]))),
                   shape=(m + 1 + mi, nvar)).tocsr()
    m = m + mi
else:
    A = coo_matrix((np.concatenate([vi, extra_v]), (np.concatenate([ri, extra_r]), np.concatenate([ci, extra_c]))),
                   shape=(m + 1, nvar)).tocsr()
node_masks = [mask(node_hubs(*n)) for n in nodes]
er, ec, ev, beq = [0], [oid[1]], [1.0], [1.0]; ne = 1
gen = set()
for a in range(len(nodes)):
    for b in range(a+1, len(nodes)):
        ha, hb = node_hubs(*nodes[a]), node_hubs(*nodes[b])
        da, db = (nodes[b][0]-nodes[a][0]) % g, (nodes[b][1]-nodes[a][1]) % g
        special = (da + db) % g == 0 or (db - 2*da) % g == 0 or (da - 2*db) % g == 0
        if all(ha[k] != hb[k] for k in range(3)) and not (MODE == 'nospecial' and special):
            gen.add((oid[node_masks[a] | node_masks[b]],))
nid = oid[node_masks[0]]
for (u,) in gen:
    er += [ne, ne]; ec += [u, nid]; ev += [1.0, -2.0]; beq.append(0.0); ne += 1
E = coo_matrix((ev, (er, ec)), shape=(ne, nvar)).tocsr()
cost = np.zeros(nvar); cost[nid] = 1
bounds = [(0, None)]*nvar; bounds[oid[0]] = (0, 0)
res = linprog(cost, A_ub=A, b_ub=np.zeros(A.shape[0]), A_eq=E, b_eq=beq, bounds=bounds, method="highs")
print(MODE, sys.argv[3] if len(sys.argv) > 3 else "", end=" "); print("Z%d: status %d  min w/k = %.6f  sqrt(k/w) = %.6f  r(all)/k = %.4f  generic-pair orbits %d" %
      (g, res.status, res.fun, (1/res.fun)**.5, res.x[oid[full]], len(gen)))
