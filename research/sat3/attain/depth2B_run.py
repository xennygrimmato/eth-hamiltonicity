#!/usr/bin/env python3
"""Driver: certified game value with level-1, type-A and type-B rows (attain-notes.md, section 11).

LP (dual, y constant on translation classes of edges, symmetrised over the linear automorphisms of the net that
preserve w):  max sum y  s.t.  y <= raw,  level-1 rows (ratios LP_T),  type-A rows (depth2c: coarse sweep + accurate
check, as in section 10),  type-B rows (this file: filter -> coarse grid -> certified branch and bound).
A type-B row is added only if its CERTIFIED UPPER BOUND hi on val_w(F) is below the priced bits by > 1e-6 per bit;
the row's right-hand side is hi (so the LP value stays an upper bound on the certified value of the class).

Usage: depth2B_run.py GROUP w0,w1,w2 [full|generic] [--typeA] [--stoponly] [--rounds N] [--tag NAME]
"""
import sys, os, math, time, argparse, itertools
import numpy as np

import depth2b
from depth2b import Game
import depth2B_core as B

TG = np.array([0.2, 0.35, 0.5, 0.65, 0.8])
UG = np.array([0.25, 0.5, 1.0])
LP_T = sorted(set([i / 10 for i in range(1, 10)] + [0.35, 0.65]))
TOL = 1e-6


def linear_maps(G, w):
    """node permutations of the linear automorphisms (r,c) -> scalar * (r,c), optionally composed with the swap
    (r,c) -> (c,r) (which exchanges merges 0 and 1; used only if w0 == w1). Prime cyclic groups only."""
    g = G.g
    if 'x' in G.name or any(g % d == 0 for d in range(2, g)):
        return [list(range(len(G.nodes)))]
    idx = {nd: i for i, nd in enumerate(G.nodes)}
    swaps = (0, 1) if abs(w[0] - w[1]) < 1e-12 else (0,)
    maps = []
    for m in range(1, g):
        for sw in swaps:
            perm = []
            for (r, c) in G.nodes:
                r2, c2 = (c, r) if sw else (r, c)
                perm.append(idx[((m * r2) % g, (m * c2) % g)])
            maps.append(perm)
    return maps


def class_perms(G, maps):
    epos = {e: k for k, e in enumerate(G.edges)}
    out = []
    for perm in maps:
        cp = np.zeros(G.C, dtype=int)
        for e, (a, c) in enumerate(G.edges):
            a2, c2 = perm[a], perm[c]
            e2 = epos.get((min(a2, c2), max(a2, c2)))
            if e2 is None:
                return [np.arange(G.C)]
            cp[G.ecls[e]] = G.ecls[e2]
        out.append(cp)
    return out


def pair_reps(G, maps):
    """representatives of unordered pairs of edges under translations x linear maps (full mode on a prime cyclic
    group), else all pairs."""
    E = G.E
    PE = np.array(list(itertools.combinations(range(E), 2)), dtype=np.int64)
    if G.mode != 'full' or len(maps) == 1 and G.g * G.g != len(G.nodes):
        return PE, np.arange(len(PE))
    g = G.g
    idx = {nd: i for i, nd in enumerate(G.nodes)}
    epos = np.full((len(G.nodes), len(G.nodes)), -1, dtype=np.int64)
    for k, (a, c) in enumerate(G.edges):
        epos[a, c] = k; epos[c, a] = k
    best = None
    for perm in maps:
        for tr in range(g):
            for tc in range(g):
                nperm = np.array([idx[((G.nodes[perm[i]][0] + tr) % g, (G.nodes[perm[i]][1] + tc) % g)] for i in range(len(G.nodes))])
                em = epos[nperm[G.ex], nperm[G.ey]]
                x = em[PE[:, 0]]; y = em[PE[:, 1]]
                key = np.minimum(x, y) * E + np.maximum(x, y)
                best = key if best is None else np.minimum(best, key)
    reps = np.unique(best)
    pos = {int(a) * E + int(b): k for k, (a, b) in enumerate(PE)}
    return PE, np.array([pos[int(k)] for k in reps])


class Driver:
    def __init__(self, name, w, mode, log):
        self.log = log
        depth2b.LP_TGRID = LP_T
        self.G = G = Game(name, w, mode)
        G.level1_rows()
        self.h1 = G.solve()
        self.maps = linear_maps(G, w)
        self.cperms = class_perms(G, self.maps)
        self.symmetrise()
        self.LAB = np.ascontiguousarray(G.lab.astype(np.int64))
        self.EA = np.array([a for (a, c) in G.edges], dtype=np.int64)
        self.EB = np.array([c for (a, c) in G.edges], dtype=np.int64)
        self.PE, self.P1 = pair_reps(G, self.maps)
        t0 = time.time()
        self.PC, self.PM, self.PT = B.pair_tables(self.LAB, self.EA, self.EB, self.PE, TG, G.w, G.g)
        self.say(f"net {name} {mode} w={tuple(w)}: E={G.E}, classes={G.C}, linear maps={len(self.maps)}, pairs={len(self.PE)}, "
                 f"P1 reps={len(self.P1)}; level-1 (ratios {len(LP_T)}) h1/E = {self.h1 / G.E:.6f}  [tables {time.time()-t0:.1f}s]")
        self.nB = 0; self.nA = 0; self.best = []

    def say(self, s):
        print(s, flush=True)
        if self.log:
            self.log.write(s + "\n"); self.log.flush()

    def symmetrise(self):
        G = self.G
        if len(self.cperms) > 1:
            G.y = np.mean([G.y[p] for p in self.cperms], axis=0)

    def add_row(self, row, rhs):
        G = self.G
        seen = set()
        for p in self.cperms:
            r2 = np.zeros(G.C); np.add.at(r2, p, row)
            key = tuple(np.round(r2, 9))
            if key in seen: continue
            seen.add(key); G.rows.append(r2); G.rhs.append(rhs)

    def resolve(self):
        h = self.G.solve(); self.symmetrise(); return h

    # -------------------------------------------------- type B
    def split(self, si):
        nT, nU = len(TG), len(UG)
        t1i, rem = divmod(si, nT * nU); t2i, ui = divmod(rem, nU)
        return t1i, t2i, ui

    def strategy(self, i, j, t1i, t2i, ui):
        G, PE = self.G, self.PE
        e1, e1p = PE[i]; e2, e2p = PE[j]
        EA, EB = self.EA, self.EB
        LL = B.labels8(self.LAB, EA[e1], EA[e1p], EB[e1], EB[e1p], EA[e2], EA[e2p], EB[e2], EB[e2p])
        u = UG[ui]; p1 = TG[t1i]; q1 = 1 - p1; p2 = u * TG[t2i]; q2 = u * (1 - TG[t2i])
        C1 = self.PC[i, t1i].copy(); C2 = self.PC[j, t2i] * u
        yE = G.y[G.ecls]
        priced = p1 * yE[e1] + q1 * yE[e1p] + p2 * yE[e2] + q2 * yE[e2p]
        row = np.zeros(G.C)
        for e, b in ((e1, p1), (e1p, q1), (e2, p2), (e2p, q2)):
            row[G.ecls[e]] += b
        return LL, p1, q1, p2, q2, C1, C2, priced, row, u

    def typeB_round(self, stoponly=False, ncoarse=17, max_verify=400):
        G = self.G
        yE = np.ascontiguousarray(G.y[G.ecls])
        t0 = time.time()
        if stoponly:
            # restriction (c): the cover always stops; val = level-1 value of the two pieces
            nT, nU = len(TG), len(UG)
            pr1 = TG[None, :] * yE[self.PE[:, 0]][:, None] + (1 - TG[None, :]) * yE[self.PE[:, 1]][:, None]
            viol = (pr1 - self.PM).max()
            self.say(f"  stop-only type B: max violation of (priced - stop1 - stop2) per bit = {viol:.3e} (level-1 rows => <= 0)")
            return 0
        best = B.filter_sweep(self.LAB, self.EA, self.EB, self.PE, self.P1, self.PC, self.PM, self.PT,
                              TG, UG, G.w, yE, G.g, TOL)
        t1 = time.time()
        cand = np.argwhere(best > TOL)
        self.say(f"  type-B filter: {len(self.P1)} x {len(self.PE)} quadruples x {len(TG)**2*len(UG)} splits in {t1-t0:.0f}s; "
                 f"quadruples passing the filter: {len(cand)} (max filter violation/bit {best.max():.5f})")
        # stage 2: coarse grid (exact th3) for every split of every candidate quadruple
        TH = np.linspace(0, math.pi / 2, ncoarse)
        stage2 = []
        if len(cand):
            QI = np.ascontiguousarray(self.P1[cand[:, 0]]); QJ = np.ascontiguousarray(cand[:, 1].astype(np.int64))
            V = B.stage2(self.LAB, self.EA, self.EB, self.PE, QI, QJ, self.PC, self.PM, self.PT, TG, UG, G.w, yE, G.g, TOL, TH)
            for n, si in np.argwhere(V > TOL):
                t1i, t2i, ui = self.split(int(si))
                stage2.append((float(V[n, si]), int(QI[n]), int(QJ[n]), t1i, t2i, ui))
        stage2.sort(reverse=True)
        t2 = time.time()
        self.say(f"  type-B coarse grid ({ncoarse}x{ncoarse} + level-1 maximisers): {len(stage2)} strategies pass [{t2-t1:.0f}s]"
                 + (f"; largest coarse violation/bit {stage2[0][0]:.5f}" if stage2 else ""))
        # stage 3: certified bracket by branch and bound, then row
        added = 0; nver = 0; worst_gap = 0.0; rows = []
        for (vio, i, j, t1i, t2i, ui) in stage2[:max_verify]:
            LL, p1, q1, p2, q2, C1, C2, priced, row, u = self.strategy(i, j, t1i, t2i, ui)
            lo, hi, a1, a2, nev = B.F_bnb(LL, p1, q1, p2, q2, C1, C2, G.w, G.g, 32, 1e-7, 400000,
                                          self.PT[i, t1i], self.PT[j, t2i])
            nver += 1; worst_gap = max(worst_gap, hi - lo)
            tv = (priced - hi) / (1 + u)
            if tv > TOL:
                rows.append((tv, row, hi, (i, j, t1i, t2i, ui, lo, hi, a1, a2, priced)))
        for (tv, row, hi, info) in rows:
            self.add_row(row, hi); added += 1
            self.best.append((tv, info))
        self.nB += added
        self.say(f"  type-B certification: {nver} bracketed (largest hi-lo {worst_gap:.2e}), verified improving {added} [{time.time()-t2:.0f}s]")
        return added

    def describe(self, info):
        G = self.G
        i, j, t1i, t2i, ui, lo, hi, a1, a2, priced = info
        e = [G.edges[k] for k in (*self.PE[i], *self.PE[j])]
        return (f"P1 = {e[0]}x{e[1]} t1={TG[t1i]}, P2 = {e[2]}x{e[3]} t2={TG[t2i]} u={UG[ui]}: val in [{lo:.6f},{hi:.6f}] "
                f"at th1={a1:.4f} th2={a2:.4f}; priced {priced:.6f}; classes {[int(G.ecls[k]) for k in (*self.PE[i], *self.PE[j])]}")

    # -------------------------------------------------- type A (section 10 code)
    def typeA_round(self, nproc=4, ncand=160):
        import depth2c
        from multiprocessing import Pool
        G = self.G
        depth2c.G = G
        reps, seen = [], set()
        for c in range(G.C):
            orb = frozenset(int(p[c]) for p in self.cperms)
            if orb in seen: continue
            seen.add(orb); reps.append(G.reps[c])
        pairs = [(i, j) for i in reps for j in range(G.E) if j != i]
        t0 = time.time()
        with Pool(nproc) as pool:
            res = [c for lst in pool.map(depth2c.sweep, pairs, chunksize=8) for c in lst]
            res.sort(reverse=True)
            cands = [c for c in res if c[0] > 1e-6][:ncand]
            ver = pool.map(depth2c.verify, cands, chunksize=4) if cands else []
        good = [v for v in ver if v[0] > 1e-6]
        for (v, i, j, e3, t, s, val) in good:
            row = np.zeros(G.C); row[G.ecls[i]] += t; row[G.ecls[j]] += 1 - t; row[G.ecls[e3]] += s
            self.add_row(row, val)
        self.nA += len(good)
        self.say(f"  type-A round: coarse candidates {len([c for c in res if c[0] > 1e-6])}, accurate-checked {len(ver)}, "
                 f"verified {len(good)} [{time.time()-t0:.0f}s]")
        return len(good)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('group'); ap.add_argument('w'); ap.add_argument('mode', nargs='?', default='full')
    ap.add_argument('--typeA', action='store_true'); ap.add_argument('--stoponly', action='store_true')
    ap.add_argument('--exactfilter', action='store_true')
    ap.add_argument('--rounds', type=int, default=4); ap.add_argument('--tag', default=None)
    ap.add_argument('--nproc', type=int, default=4)
    a = ap.parse_args()
    w = tuple(float(x) for x in a.w.split(','))
    tag = a.tag or f"{a.group}_{a.mode}_{a.w}"
    os.makedirs('out4', exist_ok=True)
    log = open(f"out4/B_{tag}.txt", 'w')
    D = Driver(a.group, w, a.mode, log)
    G = D.G
    if a.stoponly:
        D.typeB_round(stoponly=True)
    h = D.h1
    for rnd in range(a.rounds):
        nA = D.typeA_round(a.nproc) if a.typeA else 0
        if nA:
            h = D.resolve(); D.say(f"  round {rnd}: after type A  h/E = {h / G.E:.6f}")
        nB = D.typeB_round()
        if nB:
            h = D.resolve(); D.say(f"  round {rnd}: after type B  h/E = {h / G.E:.6f}")
        if nA == 0 and nB == 0:
            break
    D.best.sort(key=lambda x: -x[0])
    for tv, info in D.best[:8]:
        D.say(f"   B-strategy violation/bit {tv:.6f}: " + D.describe(info))
    D.say(f"RESULT {a.group} {a.mode} w={w}: h1/E = {D.h1 / G.E:.6f}  final h/E = {h / G.E:.6f}  "
          f"(verified type-A rows {D.nA}, verified type-B strategies {D.nB}; y = {np.round(G.y, 5).tolist()})")


if __name__ == '__main__':
    main()
