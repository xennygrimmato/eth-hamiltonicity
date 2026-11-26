#!/usr/bin/env python3
"""Depth-2 certified game (type A) with accurate verification of candidates and constraint generation.
See depth2b.py for the strategy class and depth2acc.py for the accurate evaluation.
A coarse sweep proposes candidates (coarse values are below the true values, so every true violation shows up);
only strategies whose ACCURATE value is below their priced bits are added to the dual LP.
Result: h2A(w) = value of the LP with level-1 rows and the verified depth-2 rows (an upper bound on the certified
value at weights w for this strategy class, and exact for it up to the candidates not examined).
Usage: depth2c.py GROUP w0,w1,w2 [full|generic] [rounds] [nproc] [ncand]"""
import sys, math
import numpy as np
from multiprocessing import Pool
from depth2b import Game, SGRID, TGRID
from depth2acc import acc_val

G = None
def sweep(args):
    i, j = args
    out = []
    for t in TGRID:
        vals = G.strat_vals(i, j, t, 17, 65)
        priced = t * G.y[G.ecls[i]] + (1 - t) * G.y[G.ecls[j]] + np.array(SGRID)[:, None] * G.y[G.ecls][None, :]
        viol = (priced - vals) / (1 + np.array(SGRID)[:, None])
        # keep the best third wire for each s
        for si in range(len(SGRID)):
            e3 = int(np.argmax(viol[si]))
            out.append((float(viol[si, e3]), i, j, e3, t, SGRID[si]))
    out.sort(reverse=True)
    return out[:3]

def verify(c):
    v, i, j, e3, t, s = c
    val = acc_val(G, i, j, t, s, e3, n1=161, zooms=2)
    priced = t * G.y[G.ecls[i]] + (1 - t) * G.y[G.ecls[j]] + s * G.y[G.ecls[e3]]
    return (priced - val, i, j, e3, t, s, val)

def scalar_images(G):
    """class permutations induced by scalar multiplication of the nodes (prime order only)."""
    g = G.g
    if G.name.find('x') >= 0 or any(g % d == 0 for d in range(2, g)): return []
    perms = []
    idx = {nd: k for k, nd in enumerate(G.nodes)}
    epos = {e: k for k, e in enumerate(G.edges)}
    for m in range(2, g - 1):
        perm = np.zeros(G.C, dtype=int)
        for e, (a, c) in enumerate(G.edges):
            a2 = idx[((m * G.nodes[a][0]) % g, (m * G.nodes[a][1]) % g)]; c2 = idx[((m * G.nodes[c][0]) % g, (m * G.nodes[c][1]) % g)]
            e2 = epos.get((min(a2, c2), max(a2, c2)))
            if e2 is None: return []
            perm[G.ecls[e]] = G.ecls[e2]
        perms.append(perm)
    return perms

def main():
    global G
    name = sys.argv[1]; w = tuple(float(x) for x in sys.argv[2].split(','))
    mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
    rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    ncand = int(sys.argv[6]) if len(sys.argv) > 6 else 160
    G = Game(name, w, mode); G.level1_rows(); h1 = G.solve()
    perms = scalar_images(G) if mode == 'full' else []
    def symmetrise():
        if perms:
            ys = [G.y] + [G.y[p] for p in perms]
            G.y = np.mean(ys, axis=0)
    symmetrise()
    # first edges up to translation and scalars
    reps, seen = [], set()
    for c in range(G.C):
        orb = frozenset([c] + [int(p[c]) for p in perms])
        if orb in seen: continue
        seen.add(orb); reps.append(G.reps[c])
    print(f"net {name} {mode} w={w}: E={G.E}, classes={G.C}, first-edge reps={len(reps)}; level-1 h1/E = {h1/G.E:.6f}", flush=True)
    pairs = [(i, j) for i in reps for j in range(G.E) if j != i]
    h = h1; total_added = 0; best_rows = []
    for rnd in range(rounds):
        with Pool(nproc) as pool:
            res = [c for lst in pool.map(sweep, pairs, chunksize=8) for c in lst]
            res.sort(reverse=True)
            cands = [c for c in res if c[0] > 1e-6][:ncand]
            ver = pool.map(verify, cands, chunksize=4) if cands else []
        ver.sort(reverse=True)
        ngood = sum(1 for v in ver if v[0] > 1e-6)
        print(f"  round {rnd}: coarse candidates {len([c for c in res if c[0] > 1e-6])}, verified {len(ver)}, true violations {ngood}"
              + (f", largest {ver[0][0]:.5f} (coarse {cands[0][0]:.5f})" if ver else ""), flush=True)
        if ngood == 0: break
        for (v, i, j, e3, t, s, val) in ver:
            if v <= 1e-6: continue
            row = np.zeros(G.C); row[G.ecls[i]] += t; row[G.ecls[j]] += 1 - t; row[G.ecls[e3]] += s
            G.rows.append(row); G.rhs.append(val); total_added += 1
            for p in perms:
                r2 = np.zeros(G.C); np.add.at(r2, p, row); G.rows.append(r2); G.rhs.append(val)
            best_rows.append((v, G.edges[i], G.edges[j], G.edges[e3], t, s, val))
        h = G.solve(); symmetrise()
        print(f"  round {rnd}: {total_added} verified depth-2 strategies in the LP -> h2A/E = {h/G.E:.6f}", flush=True)
    best_rows.sort(reverse=True)
    for b in best_rows[:6]:
        print("   strategy (violation, e, e', e'', t, s, val):", b, flush=True)
    print(f"RESULT {name} {mode} w={w}: h1/E = {h1/G.E:.6f}  h2A/E = {h/G.E:.6f}  (verified strategies added: {total_added})", flush=True)

if __name__ == '__main__':
    main()
