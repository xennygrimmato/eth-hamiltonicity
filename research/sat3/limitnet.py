#!/usr/bin/env python3
"""Large-g limit of the one-tree problem for 3-nets of vector-space type (nodes (r,c) in G^2, G = F_q^M,
merges r, c, r-c).  A pod labelling of a quotient Q of G: each line (class k, q in Q) gets (arm, radius).
Two generic nodes of the big net project to two independent uniform nodes of Q^2 (equal labels allowed:
different hubs at the same position).

    Phi = E_{n,n'} [ c(n,n')_+^2 ] / Dbar,   Dbar = (1/3) sum_k E_{q,q'} d(pos_k(q), pos_k(q'))^2,
    c(n,n') = max over arms b != b' of  g_n(b) + g_{n'}(b'),   g_n(b) = sum_k (+-) rho_k(n).

Level value per merge per edge bit (lower bound on the floor rho when contracting fails) = sqrt(Phi)/3.
Flat: Phi = 3 (rho = 1/sqrt3).  Cap valid for all prices: Phi <= 4.5 (rho = 1/sqrt2).
Usage: limitnet.py m [restarts] [seed]      (Q = Z_m);   limitnet.py 2x2 ...   (Q = Z_2^2)
"""
import sys, math, itertools
import numpy as np
from scipy.optimize import minimize


def group(name):
    if 'x' in name:
        dims = [int(t) for t in name.split('x')]
        els = list(itertools.product(*[range(d) for d in dims]))
        idx = {e: i for i, e in enumerate(els)}
        sub = lambda a, b: idx[tuple((x - y) % d for x, y, d in zip(els[a], els[b], dims))]
        return len(els), sub
    m = int(name)
    return m, (lambda a, b: (a - b) % m)


def phi(arms, rho, m, sub, detail=False):
    """arms, rho: arrays (3, m)."""
    # Dbar
    D = 0.0
    for k in range(3):
        for a in range(m):
            for b in range(m):
                if a == b: continue
                d = abs(rho[k, a] - rho[k, b]) if arms[k, a] == arms[k, b] else rho[k, a] + rho[k, b]
                D += d * d
    D /= 3.0 * m * m
    if D < 1e-14:
        return 0.0
    # node gains: for each node the list of (value, arm) candidates
    nodes = [(r, c) for r in range(m) for c in range(m)]
    cand = []
    for (r, c) in nodes:
        hubs = [(arms[0, r], rho[0, r]), (arms[1, c], rho[1, c]), (arms[2, sub(r, c)], rho[2, sub(r, c)])]
        tot = sum(h[1] for h in hubs)
        byarm = {}
        for a, x in hubs:
            byarm[a] = byarm.get(a, 0.0) + x
        lst = sorted([(2 * v - tot, a) for a, v in byarm.items()] + [(-tot, -1)], reverse=True)
        cand.append(lst[:3])
    S = 0.0
    for la in cand:
        for lb in cand:
            best = -1e18
            for va, a in la:
                for vb, b in lb:
                    if a == b and a != -1: continue
                    if va + vb > best: best = va + vb
            if best > 0: S += best * best
    S /= len(nodes) ** 2
    return S / D


def search(name, restarts=200, seed=0, maxarms=None, verbose=True):
    m, sub = group(name)
    rng = np.random.default_rng(seed)
    maxarms = maxarms or 6
    best = (0.0, None, None)
    for it in range(restarts):
        arms = rng.integers(0, maxarms, size=(3, m))
        rho = rng.random((3, m)) * (rng.random((3, m)) < 0.6)
        cur = phi(arms, rho, m, sub)
        for sweep in range(8):
            f = lambda x: -phi(arms, np.abs(x.reshape(3, m)), m, sub)
            res = minimize(f, rho.ravel(), method='Powell', options=dict(maxiter=4000, xtol=1e-7, ftol=1e-10))
            if -res.fun > cur:
                rho = np.abs(res.x.reshape(3, m)); cur = -res.fun
            improved = False
            for k in range(3):
                for q in range(m):
                    old = arms[k, q]
                    for a in range(maxarms):
                        if a == old: continue
                        arms[k, q] = a
                        v = phi(arms, rho, m, sub)
                        if v > cur + 1e-9:
                            cur = v; old = a; improved = True
                    arms[k, q] = old
            if not improved: break
        if cur > best[0] + 1e-7:
            best = (cur, arms.copy(), rho.copy())
            if verbose: print(f"restart {it}: Phi >= {cur:.6f}  rho_level >= {math.sqrt(cur)/3:.6f}", flush=True)
    return best


if __name__ == '__main__':
    name = sys.argv[1]
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    v, arms, rho = search(name, restarts, seed)
    print(f"Q={name}: Phi >= {v:.6f}; rho_level >= {math.sqrt(v)/3:.6f}   (flat 0.577350, cap 0.707107)")
    print("arms (rows R,C,D):\n", arms)
    print("radii:\n", np.round(rho / max(rho.max(), 1e-12), 4))
