#!/usr/bin/env python3
"""Accurate value of one type-A depth-2 strategy (see depth2b.py): exact maximisation over theta2 at
breakpoints/stationary points, fine grid plus two zooms over theta1."""
import math, itertools
import numpy as np
from game1 import mval, consts
from depth2b import Game, leaf_consts_vec, SGRID


def nest_exact(Ks, Scs, Sbs, w, r, s):
    """max over theta2 of sum_k w_k min(K_k, Sc_k + rho, Sb_k + rho'), rho = min(R cos, r+s), rho' = min(R sin, r+s)."""
    R = math.sqrt(2 * (r * r + s * s)); cap = r + s
    cand = {0.0, math.pi / 2, math.pi / 4}
    def ac(x):
        if 0 <= x <= 1: cand.add(math.acos(x))
    def asn(x):
        if 0 <= x <= 1: cand.add(math.asin(x))
    if R <= 0: return float(sum(wk * min(K, Sc, Sb) for wk, K, Sc, Sb in zip(w, Ks, Scs, Sbs)))
    ac(cap / R); asn(cap / R)
    for K, Sc, Sb in zip(Ks, Scs, Sbs):
        ac((K - Sc) / R); asn((K - Sb) / R)
        x = (Sb - Sc) / (R * math.sqrt(2))
        if -1 <= x <= 1:
            th = math.acos(x) - math.pi / 4
            if 0 <= th <= math.pi / 2: cand.add(th)
        asn((Sc + cap - Sb) / R); ac((Sb + cap - Sc) / R)
    for br in itertools.product((0, 1, 2), repeat=3):
        a = sum(w[k] for k in range(3) if br[k] == 1); b = sum(w[k] for k in range(3) if br[k] == 2)
        if a > 0 and b > 0: cand.add(math.atan2(b, a))
    th = np.array(sorted(cand))
    rho = np.minimum(R * np.cos(th), cap); rho2 = np.minimum(R * np.sin(th), cap)
    tot = np.zeros(len(th))
    for wk, K, Sc, Sb in zip(w, Ks, Scs, Sbs):
        tot += wk * np.minimum(K, np.minimum(Sc + rho, Sb + rho2))
    return float(tot.max())


def acc_val(G, i, j, t, s, e3, n1=801, zooms=2, detail=False):
    w, lab = G.w, G.lab
    (a, c), (b, d) = G.edges[i], G.edges[j]; (x, y) = G.edges[e3]
    p, q = t, 1 - t
    pats = G.pats(i, j)
    R1 = math.sqrt(2 * (p * p + q * q))
    c1 = [consts(*pats[k], p, q) for k in range(3)]
    def f(th1):
        rc = min(R1 * math.cos(th1), p + q); rb = min(R1 * math.sin(th1), p + q)
        stop = sum(w[k] * min(min(c1[k][0], c1[k][3] + 2 * min(p, q)), c1[k][1] + rc, c1[k][2] + rb) for k in range(3)) + s * G.raw[e3]
        out = [stop]
        for cut1, r in (('c', rc), ('b', rb)):
            Ks, Scs, Sbs = [], [], []
            for k in range(3):
                L = (lab[a, k], lab[b, k], lab[c, k], lab[d, k], lab[x, k], lab[y, k])
                K, Sc, Sb = leaf_consts_vec(L, p, q, s, np.array([r]), cut1)
                Ks.append(float(K[0])); Scs.append(float(Sc[0])); Sbs.append(float(Sb[0]))
            out.append(nest_exact(Ks, Scs, Sbs, w, r, s))
        return min(out), out
    _, th1s, _ = mval(pats, p, q, w, detail=True)
    lo, hi = 0.0, math.pi / 2
    best = (-1, None, None)
    for z in range(zooms + 1):
        ths = np.unique(np.concatenate([np.linspace(lo, hi, n1), [min(max(th1s, lo), hi)]]))
        vals = [f(float(th)) for th in ths]
        k = int(np.argmax([v[0] for v in vals]))
        if vals[k][0] > best[0]: best = (vals[k][0], float(ths[k]), vals[k][1])
        step = (hi - lo) / (n1 - 1)
        lo, hi = max(0.0, ths[k] - 2 * step), min(math.pi / 2, ths[k] + 2 * step)
    return best if detail else best[0]

if __name__ == '__main__':
    import sys
    w = tuple(float(v) for v in sys.argv[2].split(','))
    G = Game(sys.argv[1], w, sys.argv[3]); G.level1_rows(); h1 = G.solve()
    print("level-1", h1 / G.E)
