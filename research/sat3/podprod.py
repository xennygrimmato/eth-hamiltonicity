#!/usr/bin/env python3
"""Far-leg price-method value in products of pods (stars with infinite arms) and lines.

Space: X = prod_j T_j, T_j a pod with unboundedly many arms, l2 product metric.
A hub o has in factor j a position (arm a_j(o), radius rho_j(o) >= 0).
An edge e has a unit weight vector w_e >= 0 over the factors and, in every factor with
w_{e,j} > 0, two different arms b+ != b- along which its two legs go to infinity.
Far-leg saving of edge e under merge k (hub o for e+, hub o' for e-):
    s^k_e = sum_j w_{e,j} * ( eps(b+, o_j) rho_j(o) + eps(b-, o'_j) rho_j(o') ),
eps = +1 if the hub sits on the leg's arm, -1 otherwise.
delta_k = largest hub-hub distance inside merge k.
b_k = sum_e s^k_e / delta_k.   Objective: (1/p) sum_k b_k  (configuration is merge-transitive)
or min_k b_k.

For fixed hubs the optimal legs are found exactly: per edge and factor the best pair of
different arms; then w_e proportional to the positive part.

Configurations: 'delta3' (9 class-4 edges of AG(2,3), merges rows/cols/diagonals),
'cross' (the rectangle crossing, two merges) for calibration, 'k4' (three matchings).
"""
import sys, itertools, math, random
import numpy as np
from scipy.optimize import minimize


def config(name):
    if name == 'delta3':
        nodes = [(r, c) for r in range(3) for c in range(3)]
        merges = [lambda n: n[0], lambda n: n[1], lambda n: (n[0] - n[1]) % 3]
        edges = [((r, c), ((r + 1) % 3, (c - 1) % 3)) for r in range(3) for c in range(3)]
        ng = [3, 3, 3]
    elif name == 'cross':
        # x=(0,0), y=(0,1), u=(1,0), v=(1,1); wires x-v, y-u
        nodes = [(r, c) for r in range(2) for c in range(2)]
        merges = [lambda n: n[0], lambda n: n[1]]
        edges = [((0, 0), (1, 1)), ((0, 1), (1, 0))]
        ng = [2, 2]
    elif name == 'k4':
        nodes = [(r, c) for r in range(2) for c in range(2)]
        merges = [lambda n: n[0], lambda n: n[1], lambda n: (n[0] + n[1]) % 2]
        edges = [(a, b) for a, b in itertools.combinations(nodes, 2)]
        ng = [2, 2, 2]
    elif name == 'ag3full':
        nodes = [(r, c) for r in range(3) for c in range(3)]
        merges = [lambda n: n[0], lambda n: n[1], lambda n: (n[0] - n[1]) % 3]
        edges = [(a, b) for a, b in itertools.combinations(nodes, 2)]
        ng = [3, 3, 3]
    else:
        raise ValueError(name)
    p = len(merges)
    # hub index: (k, g) -> integer
    hub_id = {}
    for k in range(p):
        for g in range(ng[k]):
            hub_id[(k, g)] = len(hub_id)
    E = []
    for (a, b) in edges:
        ha = [hub_id[(k, merges[k](a))] for k in range(p)]
        hb = [hub_id[(k, merges[k](b))] for k in range(p)]
        E.append((ha, hb))
    groups = [[hub_id[(k, g)] for g in range(ng[k])] for k in range(p)]
    return p, len(hub_id), E, groups


def value(arms, rho, p, E, groups, mode='avg', detail=False):
    """arms: int array (J, H); rho: float array (J, H) >= 0."""
    J, H = arms.shape
    # delta_k
    delta = np.zeros(p)
    for k in range(p):
        best = 0.0
        for a, b in itertools.combinations(groups[k], 2):
            same = arms[:, a] == arms[:, b]
            d = np.where(same, np.abs(rho[:, a] - rho[:, b]), rho[:, a] + rho[:, b])
            best = max(best, math.sqrt(float(np.sum(d * d))))
        delta[k] = best
    if np.min(delta) < 1e-12:
        return (-1e9, None) if detail else -1e9
    lam = 1.0 / delta
    bk = np.zeros(p)
    tot = 0.0
    per_edge = []
    for (ha, hb) in E:
        cvec = np.zeros(J)
        svec = np.zeros((J, p))
        for j in range(J):
            # candidate arms for the + leg: arms of its hubs in factor j, or a fresh arm (-1)
            def side(hubs):
                cands = set(int(arms[j, h]) for h in hubs) | {-1}
                out = []
                for b in cands:
                    contrib = np.array([(1.0 if arms[j, h] == b else -1.0) * rho[j, h] for h in hubs])
                    out.append((float(np.dot(lam, contrib)), b, contrib))
                return out
            bestv = -1e18
            bests = None
            for va, ba, ca in side(ha):
                for vb, bb, cb in side(hb):
                    if ba == bb and ba != -1:
                        continue
                    if va + vb > bestv:
                        bestv = va + vb
                        bests = ca + cb
            cvec[j] = bestv
            svec[j] = bests
        pos = np.maximum(cvec, 0.0)
        nrm = math.sqrt(float(np.sum(pos * pos)))
        tot += nrm
        if nrm > 0:
            w = pos / nrm
            bk += lam * (w @ svec)
        per_edge.append(nrm)
    val = tot / p if mode == 'avg' else float(np.min(bk))
    if detail:
        return val, dict(bk=bk, delta=delta, per_edge=per_edge)
    return val


def optimise(name, J, restarts=200, seed=0, mode='avg', maxarms=None, verbose=True):
    p, H, E, groups = config(name)
    rng = np.random.default_rng(seed)
    best = (-1e9, None, None)
    maxarms = maxarms or H
    for it in range(restarts):
        arms = rng.integers(0, maxarms, size=(J, H))
        rho = rng.random((J, H))
        # some hubs at the centre
        rho *= (rng.random((J, H)) < 0.8)

        def f(x, arms=arms):
            return -value(arms, np.abs(x.reshape(J, H)), p, E, groups, mode)
        cur = -f(rho.ravel())
        for sweep in range(6):
            res = minimize(f, rho.ravel(), method='Powell', options=dict(maxiter=4000, xtol=1e-6, ftol=1e-9))
            rho = np.abs(res.x.reshape(J, H))
            cur = -res.fun
            improved = False
            # discrete moves
            for j in range(J):
                for h in range(H):
                    old = arms[j, h]
                    for a in range(maxarms):
                        if a == old:
                            continue
                        arms[j, h] = a
                        v = value(arms, rho, p, E, groups, mode)
                        if v > cur + 1e-9:
                            cur = v
                            old = a
                            improved = True
                    arms[j, h] = old
            if not improved:
                break
        if cur > best[0] + 1e-9:
            best = (cur, arms.copy(), rho.copy())
            if verbose:
                print(f"restart {it}: {cur:.6f}", flush=True)
    return best, (p, H, E, groups)


if __name__ == '__main__':
    name = sys.argv[1]
    J = int(sys.argv[2])
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    mode = sys.argv[4] if len(sys.argv) > 4 else 'avg'
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    (v, arms, rho), (p, H, E, groups) = optimise(name, J, restarts, seed, mode)
    nE = len(E)
    print(f"{name} J={J} mode={mode}: best value per merge = {v:.6f}  (E={nE}, E/sqrt(p)={nE/math.sqrt(p):.6f}, E/sqrt2={nE/math.sqrt(2):.6f})")
    val, det = value(arms, rho, p, E, groups, mode, detail=True)
    print("b_k:", det['bk'], "delta:", det['delta'])
    print("arms:\n", arms)
    print("rho:\n", np.round(rho, 4))
