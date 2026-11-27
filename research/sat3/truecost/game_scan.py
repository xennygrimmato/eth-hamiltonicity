#!/usr/bin/env python3
"""Scan of merge weights for the lower-bound game O1 (and O2): is the minimum over w at a two-merge corner?
    game_scan.py NET [step]      weights on the simplex grid with the given step (default 0.1), up to symmetry
"""
import sys, itertools, numpy as np
import game_true as G, game1
name = sys.argv[1]; step = float(sys.argv[2]) if len(sys.argv) > 2 else 0.1
modes = sys.argv[3].split(',') if len(sys.argv) > 3 else ['O1', 'O2']
g, nodes, lab = game1.net(name); edges = game1.all_edges(nodes); E = len(edges)
tgrid = [i / 10 for i in range(1, 10)]
n = int(round(1 / step))
best = {m: (9, None) for m in modes}
print(f"net {name}, g={g}; two-merge formula {G.two_merge_formula(g):.6f}; lower bound g/(sqrt2 (g+1)) = {g/(2**.5*(g+1)):.6f}")
for i in range(n + 1):
    for j in range(i + 1):
        k = n - i - j
        if k > j or k < 0: continue          # w1 >= w2 >= w3  (the three classes of a net of a group are equivalent)
        w = (i / n, j / n, k / n)
        row = []
        for m in modes:
            v = G.solve(lab, edges, w, tgrid, m)[0] / E
            row.append(v)
            if v < best[m][0]: best[m] = (v, w)
        print("  w =", tuple(round(x, 3) for x in w), " ".join(f"{m} {v:.6f}" for m, v in zip(modes, row)), flush=True)
for m in modes:
    print(f"min over the grid, {m}: {best[m][0]:.6f} at w = {best[m][1]}")
