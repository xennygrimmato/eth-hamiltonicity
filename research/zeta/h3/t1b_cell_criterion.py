#!/usr/bin/env python3
"""Rigorous-style sufficient criterion for the single-pair inequality (*) (kernel from cgdl_r_64.npz, |x|<=XMAX):
cells = connected components of {G_y<0}; g_c = max_c G_y^-; packing lemma (masses<=2, K>=kappa on the cell, kappa>=4g/3):
cell contributes >= -8 g_c.  Crude criterion: R1(y) = 8 sum_c g_c / self(y) < 1.
Refined: occupy a subset S of cells with one double each, at the cell's worst point; inter-cell energy 4*2*2/2... included:
  E(S) = sum_{c in S} 8 G_y(x_c) + sum_{c!=c' in S} 4 K(x_c - x_c')  ; R2(y) = -min_S E(S)/self(y) (greedy+local search)."""
import numpy as np
exec(open('t1b_onebody2.py').read().split("rng = np.random")[0])
XMAX = 15.5
mask = np.abs(xs) <= XMAX
for y in [0.005, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.3, 0.5, 0.8]:
    Gt = tab(rr[inb]*np.cosh(w[inb]*y), w[inb])[0]-K1t+Kt
    selfy = 2*((rr[inb]*np.cosh(2*w[inb]*y)).sum()-K10)
    neg = (Gt < 0) & mask
    # components
    cells = []; i = 0; n = len(xs)
    while i < n:
        if neg[i]:
            j = i
            while j+1 < n and neg[j+1]: j += 1
            seg = slice(i, j+1); k = i+np.argmin(Gt[seg]); cells.append((xs[i], xs[j], -Gt[k], xs[k])); i = j+1
        else: i += 1
    g = np.array([c[2] for c in cells]); xc = np.array([c[3] for c in cells]); diam = np.array([c[1]-c[0] for c in cells])
    kap = np.array([np.interp(dd, xs, Kt) for dd in diam])
    ok_pack = bool((kap >= 4*g/3).all())
    R1 = 8*g.sum()/selfy
    # refined: local search over subsets
    Kc = np.interp(xc[:, None]-xc[None, :], xs, Kt); np.fill_diagonal(Kc, 0)
    best = 0.0
    for start in range(30):
        S = np.random.default_rng(start).random(len(xc)) < 0.5
        improved = True
        while improved:
            improved = False
            for c in range(len(xc)):
                T = S.copy(); T[c] = ~T[c]
                e = lambda U: -8*g[U].sum()+4*Kc[np.ix_(U, U)].sum()
                if e(T) < e(S)-1e-15: S = T; improved = True
        best = min(best, -8*g[S].sum()+4*Kc[np.ix_(S, S)].sum())
    print(f"y={y:5.3f} self={selfy:.5f} #cells={len(cells):3d} max diam={diam.max():.3f} packing ok={ok_pack}  R1={R1:.3f}  R2={-best/selfy:.3f}")
