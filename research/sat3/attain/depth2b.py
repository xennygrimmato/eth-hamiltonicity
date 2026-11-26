#!/usr/bin/env python3
"""Depth-2 certified game, type A (bond of a level-1 piece crossed with a third wire), as an LP with
constraint generation (attain-notes.md, section 10).

Strategy F = (e, e', e''; p, q, s): step 1 crosses e=(a,c) [p] and e'=(b,d) [q]; after seeing theta1 the cover
either stops (level-1 realisation per merge, third wire raw), or commits to cut c or cut b of the piece and crosses
the resulting hub-hub bond with e''=(x,y) [s]; adversary theta2; the leaf is evaluated per merge by the exact
0-extension of its four hubs (tree DP), second cut chosen per merge.
    val_w(F) = max_theta1 min( stop + s*raw_w(e''),  max_theta2 sum_k w_k cost_k(cut1 = c),  same for cut1 = b ).
Dual LP (y constant on translation classes of edges):  max sum y_e  s.t. y <= raw, level-1 constraints,
and  p y_e + q y_e' + s y_e'' <= val_w(F)  for the generated strategies.  Its value is an UPPER bound for h_2(w)
restricted to these strategies (the adversary's maxima are taken on grids, which makes val slightly too small:
the final binding strategies are re-evaluated on fine grids).

Usage: depth2b.py GROUP w0,w1,w2 [full|generic] [rounds] [nproc]
"""
import sys, math, itertools
import numpy as np
from multiprocessing import Pool
from scipy.optimize import linprog
from game1 import net, canon, mval, consts, all_edges, group_ops

SGRID = [0.25, 0.5, 1.0, 1.5, 2.5, 5.0]
TGRID = [0.2, 0.35, 0.5, 0.65, 0.8]
LP_TGRID = [i / 10 for i in range(1, 10)]


def grids(n1, n2):
    return np.linspace(0, math.pi / 2, n1), np.linspace(0, math.pi / 2, n2)


def leaf_consts_vec(L, p, q, s, r, cut1):
    """labels L of (a,b,c,d,x,y) under one merge; r = array of first bonds. returns K, Sc, Sb (arrays like r)."""
    La, Lb, Lc, Ld, Lx, Ly = L
    if cut1 == 'c':
        O = ((La, p), (Lb, q)); O2 = ((Lc, p), (Ld, q))
    else:
        O = ((La, p), (Ld, q)); O2 = ((Lb, q), (Lc, p))
    cand = list(set(L) | {-1})
    def side(legs, Lz):
        mv = [sum(b for (l, b) in legs if l != Lh) for Lh in cand]
        cap = r + min(mv)
        return [np.minimum(m, cap) + (s if Lz != Lh else 0.0) for m, Lh in zip(mv, cand)]
    res = []
    for (zu, zu2) in ((Lx, Ly), (Ly, Lx)):
        A = side(O, zu); B = side(O2, zu2)
        M = np.minimum.reduce([x + y for x, y in zip(A, B)])
        Smin = np.minimum.reduce(A) + np.minimum.reduce(B)
        res.append((M, Smin))
    return np.minimum(res[0][0], res[1][0]), res[0][1], res[1][1]


class Game:
    def __init__(self, name, w, mode):
        self.name, self.mode = name, mode
        self.w = np.asarray(w, float)
        g, nodes, lab = net(name)
        self.g, self.nodes, self.lab = g, nodes, lab
        n = len(nodes)
        edges = all_edges(nodes)
        if mode == 'generic':
            edges = [(a, c) for (a, c) in edges if all(lab[a, k] != lab[c, k] for k in range(3))]
        self.edges = edges; self.E = len(edges)
        _, sub = group_ops(name)
        idx = {nd: i for i, nd in enumerate(nodes)}
        def diff(i, j):
            return idx[(sub[nodes[j][0], nodes[i][0]], sub[nodes[j][1], nodes[i][1]])]
        neg = [diff(i, 0) for i in range(n)]
        cls = {}
        self.ecls = np.zeros(self.E, dtype=int)
        for e, (i, j) in enumerate(edges):
            v = diff(i, j); key = min(v, neg[v])
            self.ecls[e] = cls.setdefault(key, len(cls))
        self.C = len(cls)
        self.size = np.bincount(self.ecls, minlength=self.C).astype(float)
        self.raw = np.array([sum(self.w[k] for k in range(3) if lab[a, k] != lab[c, k]) for (a, c) in edges])
        self.rawc = np.array([self.raw[np.nonzero(self.ecls == c)[0][0]] for c in range(self.C)])
        self.reps = [int(np.nonzero(self.ecls == c)[0][0]) for c in range(self.C)]
        self.ex = np.array([a for (a, c) in edges]); self.ey = np.array([c for (a, c) in edges])
        self.rows, self.rhs = [], []

    def pats(self, i, j):
        (a, c), (b, d) = self.edges[i], self.edges[j]
        lab = self.lab
        return tuple(canon((lab[a, k], lab[b, k], lab[c, k], lab[d, k])) for k in range(3))

    def level1_rows(self):
        for i in self.reps:
            for j in range(self.E):
                if j == i: continue
                pats = self.pats(i, j)
                for t in LP_TGRID:
                    m = mval(pats, t, 1 - t, self.w)
                    if m < t * self.raw[i] + (1 - t) * self.raw[j] - 1e-12:
                        row = np.zeros(self.C); row[self.ecls[i]] += t; row[self.ecls[j]] += 1 - t
                        self.rows.append(row); self.rhs.append(m)

    def solve(self):
        if not self.rows:
            self.y = self.rawc.copy(); return float(self.size @ self.y)
        res = linprog(-self.size, A_ub=np.array(self.rows), b_ub=np.array(self.rhs),
                      bounds=[(0, self.rawc[c]) for c in range(self.C)], method='highs')
        assert res.status == 0
        self.y = res.x
        return -res.fun

    def strat_vals(self, i, j, t, n1=17, n2=129):
        """val[s_index, e''] for all third wires, and stop/nest arrays."""
        w, lab, g = self.w, self.lab, self.g
        (a, c), (b, d) = self.edges[i], self.edges[j]
        p, q = t, 1 - t
        pats = self.pats(i, j)
        _, th1s, _ = mval(pats, p, q, w, detail=True)
        TH1, TH2 = grids(n1, n2)
        TH1 = np.unique(np.concatenate([TH1, [th1s]]))
        R1 = math.sqrt(2 * (p * p + q * q))
        rc = np.minimum(R1 * np.cos(TH1), p + q); rb = np.minimum(R1 * np.sin(TH1), p + q)
        stop = np.zeros(len(TH1))
        for k in range(3):
            S, Ac, Ab, A3 = consts(*pats[k], p, q)
            stop += w[k] * np.minimum(min(S, A3 + 2 * min(p, q)), np.minimum(Ac + rc, Ab + rb))
        C2, S2 = np.cos(TH2), np.sin(TH2)
        E = self.E
        vals = np.empty((len(SGRID), E))
        for si, s in enumerate(SGRID):
            best = stop[None, :] + s * self.raw[:, None]          # [E, th1]
            for cut1, r in (('c', rc), ('b', rb)):
                R2 = np.sqrt(2 * (r * r + s * s))
                rho = np.minimum(R2[:, None] * C2[None, :], (r + s)[:, None])    # [th1, th2]
                rho2 = np.minimum(R2[:, None] * S2[None, :], (r + s)[:, None])
                tot = np.zeros((E, len(TH1), n2))
                for k in range(3):
                    pl = (lab[a, k], lab[b, k], lab[c, k], lab[d, k])
                    lx = lab[self.ex, k]; ly = lab[self.ey, k]
                    inx = np.isin(lx, pl); iny = np.isin(ly, pl)
                    tx = np.where(inx, lx, g)
                    ty = np.where(iny, ly, np.where((~inx) & (lx == ly), g, g + 1))
                    code = tx * (g + 2) + ty
                    K = np.empty((E, len(TH1))); Sc = np.empty_like(K); Sb = np.empty_like(K)
                    for cd in np.unique(code):
                        Lx, Ly = int(cd) // (g + 2), int(cd) % (g + 2)
                        kk, sc, sb = leaf_consts_vec((pl[0], pl[1], pl[2], pl[3], Lx, Ly), p, q, s, r, cut1)
                        msk = code == cd
                        K[msk] = kk; Sc[msk] = sc; Sb[msk] = sb
                    tot += w[k] * np.minimum(K[:, :, None], np.minimum(Sc[:, :, None] + rho[None], Sb[:, :, None] + rho2[None]))
                nest = tot.max(axis=2)                              # [E, th1]
                best = np.minimum(best, nest)
            vals[si] = best.max(axis=1)
        return vals

    def sweep_pair(self, args):
        i, j = args
        out = []
        for t in TGRID:
            vals = self.strat_vals(i, j, t)
            priced = t * self.y[self.ecls[i]] + (1 - t) * self.y[self.ecls[j]] + np.array(SGRID)[:, None] * self.y[self.ecls][None, :]
            viol = priced - vals
            si, e3 = np.unravel_index(int(np.argmax(viol)), viol.shape)
            out.append((float(viol[si, e3]), i, j, int(e3), t, SGRID[si], float(vals[si, e3])))
        return max(out)

GAME = None
def _work(args):
    return GAME.sweep_pair(args)


def main():
    global GAME
    name = sys.argv[1]
    w = tuple(float(x) for x in sys.argv[2].split(','))
    mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
    rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    G = Game(name, w, mode); GAME = G
    G.level1_rows()
    h1 = G.solve()
    print(f"net {name} {mode} w={w}: E={G.E}, classes={G.C}; level-1 h1/E = {h1/G.E:.6f}", flush=True)
    # reduce first edges by scalar symmetry when available (prime order): classes up to scalars
    reps = G.reps
    pairs = [(i, j) for i in reps for j in range(G.E) if j != i]
    h = h1
    for rnd in range(rounds):
        with Pool(nproc) as pool:
            res = pool.map(_work, pairs, chunksize=8)
        res.sort(reverse=True)
        print(f"  round {rnd}: max violation {res[0][0]:.5f} at (i,j,e'',t,s,val) = {res[0][1:]}  edges {G.edges[res[0][1]]},{G.edges[res[0][2]]},{G.edges[res[0][3]]}", flush=True)
        if res[0][0] < 1e-7:
            break
        added = 0; seen = set()
        for (v, i, j, e3, t, s, val) in res:
            if v < 1e-7 or added >= 60: break
            row = np.zeros(G.C); row[G.ecls[i]] += t; row[G.ecls[j]] += 1 - t; row[G.ecls[e3]] += s
            key = (tuple(np.round(row, 6)), round(val, 6))
            if key in seen: continue
            seen.add(key); G.rows.append(row); G.rhs.append(val); added += 1
        h = G.solve()
        print(f"  round {rnd}: added {added} depth-2 constraints -> h2/E <= {h/G.E:.6f}  (y = {np.round(G.y,4)})", flush=True)
    print(f"RESULT {name} {mode} w={w}: h1/E = {h1/G.E:.6f}  h2A/E = {h/G.E:.6f}", flush=True)

if __name__ == '__main__':
    main()
