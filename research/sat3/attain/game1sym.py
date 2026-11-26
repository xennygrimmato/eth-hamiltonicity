#!/usr/bin/env python3
"""Level-1 game on the full level of the 3-net of a group, using translation symmetry of the dual LP
(the dual is a concave programme invariant under translations, so y may be taken constant on translation
classes of edges).  Usage: game1sym.py GROUP [nt] [w0,w1,w2 ...]"""
import sys, math, itertools
import numpy as np
from scipy.optimize import linprog
from game1 import net, canon, mval, group_ops


def setup(name):
    g, nodes, lab = net(name)
    _, sub = group_ops(name)
    n = len(nodes)
    idx = {nd: i for i, nd in enumerate(nodes)}
    def diff(i, j):  # direction n_j - n_i as node index
        return idx[(sub[nodes[j][0], nodes[i][0]], sub[nodes[j][1], nodes[i][1]])]
    neg = [diff(i, 0) for i in range(n)]            # index of -v
    cls = {}
    for v in range(1, n):
        key = min(v, neg[v])
        cls.setdefault(key, len(cls))
    def eclass(i, j):
        v = diff(i, j)
        return cls[min(v, neg[v])]
    return g, nodes, lab, n, cls, eclass


def solve_sym(name, w, tgrid, detail=False):
    g, nodes, lab, n, cls, eclass = setup(name)
    C = len(cls)
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    size = np.zeros(C)
    for (i, j) in edges:
        size[eclass(i, j)] += 1
    w = np.asarray(w, float)
    rawc = np.zeros(C)
    reps = {}
    for v, c in cls.items():
        reps[c] = (0, v)
        rawc[c] = sum(w[k] for k in range(3) if lab[0, k] != lab[v, k])
    A, rhs, info = [], [], []
    for c, (a, cc) in reps.items():
        for (b, d) in edges:
            if (b, d) == (a, cc):
                continue
            c2 = eclass(b, d)
            pats = tuple(canon((lab[a, k], lab[b, k], lab[cc, k], lab[d, k])) for k in range(3))
            for t in tgrid:
                m = mval(pats, t, 1 - t, w)
                if m >= t * rawc[c] + (1 - t) * rawc[c2] - 1e-12:
                    continue
                row = np.zeros(C); row[c] += t; row[c2] += 1 - t
                A.append(row); rhs.append(m); info.append((c, c2, t, pats))
    if not A:
        return float(size @ rawc), rawc, size, []
    res = linprog(-size, A_ub=np.array(A), b_ub=np.array(rhs), bounds=[(0, rawc[c]) for c in range(C)], method='highs')
    assert res.status == 0
    act = []
    if detail:
        mu = -res.ineqlin.marginals
        act = [(mu[i],) + info[i] for i in np.nonzero(mu > 1e-9)[0]]
    return -res.fun, res.x, size, act


if __name__ == '__main__':
    name = sys.argv[1]
    nt = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    ws = [tuple(float(x) for x in s.split(',')) for s in sys.argv[3:]] or \
        [(0.5, 0.5, 0.0), (1 / 3, 1 / 3, 1 / 3), (0.45, 0.45, 0.1), (0.5, 0.45, 0.05), (0.6, 0.2, 0.2)]
    tgrid = [i / (nt + 1) for i in range(1, nt + 1)]
    g, nodes, lab, n, cls, eclass = setup(name)
    E = n * (n - 1) // 2
    Egen = g * g * (g - 1) * (g - 2) // 2
    two = (g * g * (g - 1) ** 2 / 2 / math.sqrt(2) + g * g * (g - 1) / 2) / E
    print(f"net {name}: g={g} E={E}; two-merge value {(two):.6f}; 1/sqrt2={1/math.sqrt(2):.6f}")
    for w in ws:
        v, y, size, _ = solve_sym(name, w, tgrid)
        rawv = sum(sum(w[k] for k in range(3) if lab[a, k] != lab[c, k]) for a in range(n) for c in range(a + 1, n))
        print(f"  w={tuple(round(x,3) for x in w)}: h/E={v/E:.6f}  raw/E={rawv/E:.6f}", flush=True)
