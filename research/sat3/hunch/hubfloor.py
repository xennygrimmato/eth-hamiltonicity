#!/usr/bin/env python3
"""hunch/hubfloor.py -- Euclidean (flat) price floors for Delta_3 when the merged network may contain a HUB
(a label shared by the three groups of the merge = a hyperedge of the merged instance).

Configuration: nodes (r,c) in Z_3^2, merges rows / columns / diagonals r-c, edges = the nine edges of the fourth
parallel class (three triangles x+y = const).  Under every merge Delta_3 is the matrix multiplication tensor
<N^3,N^3,N^3> on the three groups.

Price method with hubs [D, notes hunch-triangle.md section 2]: for a price with hub sites o^k_G, a piece A that is a
restriction of a network on the groups of merge k with pair bonds b_{GG'} (bits) and a three-way label of t bits has
        lambda * B_k  <=  sum b_{GG'} d(o_G,o_G') + t * D_k,     B_k = L - H_k   (far legs: B_k = sum_e <u_e, Delta^k_e>),
D_k = common-label rate of the three hubs.  In a Euclidean flat D_k = W_k = half the perimeter of the hub triangle
[K-OA EG Thm 1.1; unrefereed].  Hence, for every family with 2^{o(lambda)} terms, some piece has for all k at once

  mode 'kappa':  (pair bits) + kappa*(hub bits)      >= lambda * B_k / max(delta_k, W_k/kappa)
  mode 'time' :  t + omega(b)  (K = 3 base, exact rectangular matrix multiplication [K-OA])  >= lambda * B_k / W_k

This script maximises min_k of the right-hand sides over Euclidean placements (hubs in R^d, unit leg directions u_e).
Sanity values: kappa >= 3/2 must give 3*sqrt(3) = 5.19615 (hubs useless, b2's value);
equilateral orthogonal hubs give (2 kappa/3) * 3 sqrt 3 for kappa <= 3/2.
Usage: hubfloor.py [restarts] [d]
"""
import sys, itertools, math
import numpy as np
from scipy.optimize import minimize

NODES = [(r, c) for r in range(3) for c in range(3)]
GRP = [lambda n: n[0], lambda n: n[1], lambda n: (n[0] - n[1]) % 3]
EDGES = []
for (r, c) in NODES:
    n2 = ((r + 1) % 3, (c - 1) % 3)
    EDGES.append(((r, c), n2))
assert len(set(frozenset(e) for e in EDGES)) == 9
PAIRS = [(0, 1), (1, 2), (0, 2)]


def unpack(x, d):
    h = x[:27 * 1 * d // 3 * 1].reshape(3, 3, d) if False else x[:9 * d].reshape(3, 3, d)
    u = x[9 * d:18 * d].reshape(9, d)
    t = x[18 * d]
    return h, u, t


def Bk(h, u):
    B = np.zeros(3)
    for k in range(3):
        for i, (a, b) in enumerate(EDGES):
            B[k] += u[i] @ (h[k, GRP[k](b)] - h[k, GRP[k](a)])
    return B


def sides(h, k):
    return np.array([np.linalg.norm(h[k, i] - h[k, j]) for i, j in PAIRS])


def value(h, u, mode, kappa):
    B = Bk(h, u)
    v = []
    for k in range(3):
        s = sides(h, k)
        W = s.sum() / 2
        m = W if mode == 'time' else max(s.max(), W / kappa)
        v.append(B[k] / m)
    return min(v), v


def solve(mode, kappa, d, rng, x0=None):
    nvar = 18 * d + 1
    if x0 is None:
        x0 = np.concatenate([rng.normal(size=9 * d), rng.normal(size=9 * d), [0.5]])
        u = x0[9 * d:18 * d].reshape(9, d)
        u /= np.linalg.norm(u, axis=1, keepdims=True)
    cons = []
    for k in range(3):
        if mode == 'time':
            cons.append(dict(type='ineq', fun=lambda x, k=k: Bk(*unpack(x, d)[:2])[k] - x[-1] * sides(unpack(x, d)[0], k).sum() / 2))
        else:
            cons.append(dict(type='ineq', fun=lambda x, k=k: Bk(*unpack(x, d)[:2])[k] - x[-1] * sides(unpack(x, d)[0], k).sum() / (2 * kappa)))
            for j in range(3):
                cons.append(dict(type='ineq', fun=lambda x, k=k, j=j: Bk(*unpack(x, d)[:2])[k] - x[-1] * sides(unpack(x, d)[0], k)[j]))
    for i in range(9):
        cons.append(dict(type='ineq', fun=lambda x, i=i: 1.0 - np.sum(unpack(x, d)[1][i] ** 2)))
    # pin the scale of the hubs
    cons.append(dict(type='eq', fun=lambda x: np.sum(unpack(x, d)[0] ** 2) - 9.0))
    r = minimize(lambda x: -x[-1], x0, constraints=cons, method='SLSQP', options=dict(maxiter=600, ftol=1e-12))
    h, u, t = unpack(r.x, d)
    nu = np.linalg.norm(u, axis=1, keepdims=True)
    u = u / np.maximum(nu, 1e-12)
    val, per = value(h, u, mode, kappa)
    return val, h, u, per


def describe(h):
    out = []
    for k in range(3):
        s = np.sort(sides(h, k))
        out.append("(%.3f,%.3f,%.3f)" % tuple(s / s.max()))
    return " ".join(out)


def explicit_family():
    """Closed-form candidates, for the record."""
    print("closed forms:")
    for kappa in (1.0, 4 / 3, 1.5):
        print("  kappa=%.4f: equilateral orthogonal hubs: %.5f" % (kappa, min(1, 2 * kappa / 3) * 3 * math.sqrt(3)))
    # isosceles hub triangles with sides (1,1,x), orthogonal across merges; edge i=(i,j) is 'short' in rows iff i=i0,
    # in columns iff j=j0, in diagonals iff i-j=l0 (see notes); non-concurrent choice: 3 edges short twice,
    # 3 short once, 3 never.
    for kappa in (4 / 3,):
        best = (0, None)
        for x in np.linspace(0.0, 1.0, 2001):
            m = max(1.0, (2 + x) / (2 * kappa))
            v = (math.sqrt(1 + 2 * x * x) + math.sqrt(2 + x * x) + math.sqrt(3)) / m   # average over merges
            if v > best[0]:
                best = (v, x)
        print("  kappa=%.4f: isosceles (1,1,x) orthogonal, non-concurrent short sides (upper estimate = merge average): %.5f at x=%.3f" % (kappa, best[0], best[1]))
    best = (0, None)
    for x in np.linspace(0.0, 1.0, 2001):
        W = (2 + x) / 2
        v = (math.sqrt(1 + 2 * x * x) + math.sqrt(2 + x * x) + math.sqrt(3)) / W
        if v > best[0]:
            best = (v, x)
    print("  time mode: isosceles (1,1,x): merge average %.5f at x=%.3f;  x=0 (two hubs coincide): %.5f;  3*sqrt2 = %.5f"
          % (best[0], best[1], (1 + math.sqrt(2) + math.sqrt(3)) / 1.0, 3 * math.sqrt(2)))


if __name__ == "__main__":
    restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    rng = np.random.default_rng(7)
    explicit_family()
    print("numerical maxima (SLSQP, %d restarts, hubs in R^%d); values are per merge, in units of lambda; raw bits: 9" % (restarts, d))
    for mode, kappa in (('kappa', 2.0), ('kappa', 1.5), ('kappa', 4 / 3), ('kappa', 1.2), ('kappa', 1.0), ('time', None)):
        best = (-1, None, None, None)
        vals = []
        for it in range(restarts):
            try:
                val, h, u, per = solve(mode, kappa, d, rng)
            except Exception as ex:
                continue
            vals.append(val)
            if val > best[0]:
                best = (val, h, u, per)
        vals = np.sort(vals)[::-1]
        lab = "kappa=%.4f" % kappa if mode == 'kappa' else "time (label units)"
        print("  %-20s best %.5f  (rho = %.4f of 9)  top5 %s  per-merge %s  hub triangles %s"
              % (lab, best[0], best[0] / 9, np.round(vals[:5], 4), np.round(best[3], 4), describe(best[1])))
