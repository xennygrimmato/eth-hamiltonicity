#!/usr/bin/env python3
"""Depth-2 certified game on a net level, type A: cross the hub-hub bond of a level-1 piece with a third wire
(attain-notes.md, section 10).

Level-1: pair of edges e=(a,c) [p bits], e'=(b,d) [q bits], adversary theta1 -> bonds r (cut ab|cd), r' (cut ad|bc).
Depth 2: the cover commits to a cut of the first piece (cut1 = c or b), i.e. to hubs O, O' and the bond (O,O'; r1),
and crosses that bond with a third wire (x,y; s): adversary theta2 -> rho, rho' with rho^2+rho'^2 = 2(r1^2+s^2);
the leaf is evaluated under merge k by the min 0-extension of its hubs O,O',U,U' to the groups of k, with the
second cut chosen per merge.  For the tree-shaped leaf systems the 0-extension is an exact small DP:
    cost_k = min( M_c, S_c + rho, M_b, S_b + rho' ).

Test (sufficient for "depth 2 gives nothing at weights w", type A): take the level-1 dual optimum y* (bits prices
of the edges; sum = h_1(w)).  For every first pair and split t the adversary plays the level-1 maximiser theta1*;
the test passes if for both committed cuts, every third wire and every s in the grid
    nest := max_theta2 sum_k w_k cost_k  >=  p y_e + q y_e' + s y_e''.
Then every type-A strategy has weighted value >= its bits priced by y*, hence h_2(w) = h_1(w) (for these moves and
grids; the theta2-maximum is taken on a grid, which only lowers `nest`, so a pass is safe).
Failures are listed with their deficit; a failure is only a candidate (the adversary may have another theta1).

Usage: depth2.py GROUP w0,w1,w2 [mode full|generic] [nt]
"""
import sys, math, itertools
import numpy as np
from game1 import net, canon, mval, solve, all_edges
from game1sym import solve_sym, setup

NTH2 = 257
TH2 = np.linspace(0, math.pi / 2, NTH2)
C2, S2 = np.cos(TH2), np.sin(TH2)
SGRID = [0.25, 0.5, 1.0, 1.5, 2.5, 5.0]


def leaf_consts(L, p, q, s, r, cut1):
    """L = labels of (a,b,c,d,x,y) under one merge. returns K = min(M_c, M_b), S_c, S_b."""
    La, Lb, Lc, Ld, Lx, Ly = L
    if cut1 == 'c':
        O = ((La, p), (Lb, q)); O2 = ((Lc, p), (Ld, q))
    else:
        O = ((La, p), (Ld, q)); O2 = ((Lb, q), (Lc, p))
    cand = set(L) | {-1}
    def side(legs, Lz):
        G = min(sum(b for (l, b) in legs if l != Lh) for Lh in cand)
        cap = r + G
        return {Lh: min(sum(b for (l, b) in legs if l != Lh), cap) + (s if Lz != Lh else 0.0) for Lh in cand}
    out = []
    for (zu, zu2) in ((Lx, Ly), (Ly, Lx)):
        A = side(O, zu); B = side(O2, zu2)
        M = min(A[h] + B[h] for h in cand)
        Smin = min(A.values()) + min(B.values())
        out.append((M, Smin))
    return min(out[0][0], out[1][0]), out[0][1], out[1][1]


def run(name, w, mode='full', nt=9, verbose=True):
    g, nodes, lab = net(name)
    n = len(nodes)
    w = np.asarray(w, float)
    tgrid = [i / (nt + 1) for i in range(1, nt + 1)]
    edges = all_edges(nodes)
    if mode == 'generic':
        edges = [(a, c) for (a, c) in edges if all(lab[a, k] != lab[c, k] for k in range(3))]
        h1, y, _ = solve(lab, edges, w, tgrid)
        reps = list(range(len(edges)))
    else:
        h1, ycls, size, _ = solve_sym(name, w, tgrid)
        _, _, _, _, cls, eclass = setup(name)
        y = np.array([ycls[eclass(a, c)] for (a, c) in edges])
        # representatives of edges up to translation and scalars: (0, v), v = one direction per slope
        seen, reps = set(), []
        for idx, (a, c) in enumerate(edges):
            if a != 0: continue
            v = nodes[c]
            key = tuple(sorted({tuple(lab[c2] ) for c2 in range(n) if any((nodes[c2][0] - m * v[0]) % g == 0 and (nodes[c2][1] - m * v[1]) % g == 0 for m in range(1, g))}, key=lambda z: tuple(z)))
            if key in seen: continue
            seen.add(key); reps.append(idx)
    E = len(edges)
    raw = np.array([sum(w[k] for k in range(3) if lab[a, k] != lab[c, k]) for (a, c) in edges])
    ex = np.array([a for (a, c) in edges]); ey = np.array([c for (a, c) in edges])
    worst = (1e9, None); nfail = 0; ntest = 0; fails = []
    for i in reps:
        a, c = edges[i]
        for j in range(E):
            if j == i: continue
            b, d = edges[j]
            pats = tuple(canon((lab[a, k], lab[b, k], lab[c, k], lab[d, k])) for k in range(3))
            for t in tgrid:
                p, q = t, 1 - t
                m, th1, _ = mval(pats, p, q, w, detail=True)
                base = p * y[i] + q * y[j]
                # the level-1 option at theta1* is fine iff m >= base (LP feasibility); raw pairs are covered by y <= raw
                R1 = math.sqrt(2 * (p * p + q * q))
                for cut1 in 'cb':
                    r = min(R1 * (math.cos(th1) if cut1 == 'c' else math.sin(th1)), p + q)
                    for s in SGRID:
                        R2 = math.sqrt(2 * (r * r + s * s))
                        rho = np.minimum(R2 * C2, r + s); rho2 = np.minimum(R2 * S2, r + s)
                        tot = np.zeros((E, NTH2))
                        for k in range(3):
                            pl = (lab[a, k], lab[b, k], lab[c, k], lab[d, k])
                            lx = lab[ex, k]; ly = lab[ey, k]
                            inx = np.isin(lx, pl); iny = np.isin(ly, pl)
                            # type code: label if among the pair's labels, else g (new) / g+1 (second new label)
                            tx = np.where(inx, lx, g)
                            ty = np.where(iny, ly, np.where((~inx) & (lx == ly), g, g + 1))
                            code = tx * (g + 2) + ty
                            K = np.empty(E); Sc = np.empty(E); Sb = np.empty(E)
                            for cd in np.unique(code):
                                Lx, Ly = int(cd) // (g + 2), int(cd) % (g + 2)
                                kk, sc, sb = leaf_consts((pl[0], pl[1], pl[2], pl[3], Lx, Ly), p, q, s, r, cut1)
                                msk = code == cd
                                K[msk] = kk; Sc[msk] = sc; Sb[msk] = sb
                            tot += w[k] * np.minimum(K[:, None], np.minimum(Sc[:, None] + rho[None, :], Sb[:, None] + rho2[None, :]))
                        nest = tot.max(axis=1)
                        marg = nest - (base + s * y)
                        ntest += E
                        jm = int(np.argmin(marg))
                        if marg[jm] < worst[0]:
                            worst = (float(marg[jm]), (edges[i], edges[j], edges[jm], t, s, cut1, th1))
                        bad = np.nonzero(marg < -1e-9)[0]
                        nfail += len(bad)
                        for jb in bad[:3]:
                            if len(fails) < 2000:
                                fails.append((float(marg[jb]), edges[i], edges[j], edges[jb], t, s, cut1, th1))
    return dict(h1=h1, E=E, y=y, worst=worst, nfail=nfail, ntest=ntest, fails=sorted(fails)[:20], raw=raw, edges=edges, lab=lab, nodes=nodes)


if __name__ == '__main__':
    name = sys.argv[1]
    w = tuple(float(x) for x in sys.argv[2].split(','))
    mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
    nt = int(sys.argv[4]) if len(sys.argv) > 4 else 9
    res = run(name, w, mode, nt)
    print(f"net {name} mode {mode} w={w}: level-1 h/E = {res['h1']/res['E']:.6f}; type-A depth-2 tests {res['ntest']}, failures {res['nfail']}")
    print("  worst margin nest - priced bits:", res['worst'])
    for f in res['fails'][:10]:
        print("   fail", f)
