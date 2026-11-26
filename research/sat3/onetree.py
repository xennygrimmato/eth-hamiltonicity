#!/usr/bin/env python3
"""One-tree reduction.  For a configuration with merge- and edge-transitive symmetry, the supremum of the
far-leg price value over all l2-products of pods equals (1/p) sqrt(E * Gamma), where

    Gamma = sup over ONE pod with hubs of   S / Dbar,
    S    = sum_e ( max over leg arms of sum_k s^k_e )_+^2,
    Dbar = average over merges k and pairs of hubs of merge k of d(o,o')^2.

(Proof: Cauchy-Schwarz over edges and factors; equality by taking the product over the orbit of the pod.)
This script maximises S/Dbar over pods (hub = (arm, radius))."""
import sys, itertools, math
import numpy as np
from scipy.optimize import minimize
from podprod import config


def ratio(arms, rho, p, E, groups, detail=False):
    H = len(arms)
    # Dbar
    D = 0.0
    for k in range(p):
        prs = list(itertools.combinations(groups[k], 2))
        s = 0.0
        for a, b in prs:
            d = abs(rho[a] - rho[b]) if arms[a] == arms[b] else rho[a] + rho[b]
            s += d * d
        D += s / len(prs)
    D /= p
    if D < 1e-14:
        return (0.0, None) if detail else 0.0
    S = 0.0
    cs = []
    for (ha, hb) in E:
        def side(hubs):
            cands = set(int(arms[h]) for h in hubs) | {-1}
            return [(sum((1.0 if arms[h] == b else -1.0) * rho[h] for h in hubs), b) for b in cands]
        best = -1e18
        for va, ba in side(ha):
            for vb, bb in side(hb):
                if ba == bb and ba != -1:
                    continue
                best = max(best, va + vb)
        c = max(best, 0.0)
        cs.append(c)
        S += c * c
    if detail:
        return S / D, dict(S=S, D=D, c=cs)
    return S / D


def search(name, restarts=300, seed=0, maxarms=None, verbose=True):
    p, H, E, groups = config(name)
    rng = np.random.default_rng(seed)
    maxarms = maxarms or H
    best = (0.0, None, None)
    for it in range(restarts):
        arms = rng.integers(0, maxarms, size=H)
        rho = rng.random(H) * (rng.random(H) < 0.6)
        cur = ratio(arms, rho, p, E, groups)
        for sweep in range(8):
            f = lambda x: -ratio(arms, np.abs(x), p, E, groups)
            res = minimize(f, rho, method='Powell', options=dict(maxiter=3000, xtol=1e-7, ftol=1e-10))
            if -res.fun > cur:
                rho = np.abs(res.x); cur = -res.fun
            improved = False
            for h in range(H):
                old = arms[h]
                for a in range(maxarms):
                    if a == old: continue
                    arms[h] = a
                    v = ratio(arms, rho, p, E, groups)
                    if v > cur + 1e-9:
                        cur = v; old = a; improved = True
                arms[h] = old
            if not improved: break
        if cur > best[0] + 1e-7:
            best = (cur, arms.copy(), rho.copy())
            if verbose: print(f"restart {it}: Gamma >= {cur:.6f}", flush=True)
    return best, (p, H, E, groups)


if __name__ == '__main__':
    name = sys.argv[1]
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    (g, arms, rho), (p, H, E, groups) = search(name, restarts, seed)
    nE = len(E)
    print(f"{name}: Gamma >= {g:.6f};  value per merge (1/p)sqrt(E*Gamma) = {math.sqrt(nE*g)/p:.6f};"
          f"  flat E/sqrt(p) = {nE/math.sqrt(p):.6f};  cap E/sqrt2 = {nE/math.sqrt(2):.6f}")
    print("arms", arms); print("rho ", np.round(rho / max(rho.max(), 1e-12), 4))
