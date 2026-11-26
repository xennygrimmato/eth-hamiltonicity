#!/usr/bin/env python3
"""hunch/hubfloor.py -- Euclidean (flat) price floors for Delta_3 when the merged network may contain a HUB
(a label shared by the three groups of the merge = a hyperedge of the merged instance).

Configuration: nodes (r,c) in Z_3^2, merges rows / columns / diagonals r-c, edges = the nine edges of the fourth
parallel class (three triangles x+y = const).  Under every merge Delta_3 is the matrix multiplication tensor
<N^3,N^3,N^3> on the three groups.

Price method with hubs [D, hunch-triangle.md section 2]: for a price with hub sites o^k_G, a piece A that is a
restriction of a network on the groups of merge k with pair bonds b_{GG'} (bits) and a three-way label of t bits has
        lambda * B_k  <=  sum b_{GG'} d(o_G,o_G') + t * D_k,     B_k = L - H_k   (far legs: B_k = sum_e <u_e, Delta^k_e>),
D_k = common-label rate of the three hubs.  In a Euclidean flat D_k = W_k = half the perimeter of the hub triangle
[K-OA, Euclidean-geometry paper Thm 1.1; unrefereed].  Hence, for every family with 2^{o(lambda)} terms, some piece
has for all k at once

  mode 'kappa':  (pair bits) + kappa*(hub bits)      >= lambda * B_k / max(delta_k, W_k/kappa)
  mode 'time' :  t + omega(b)  (K = 3 base, exact rectangular matrix multiplication [K-OA])  >= lambda * B_k / W_k

This script maximises min_k of the right-hand sides over Euclidean placements (hubs in R^d, unit leg directions u_e).
Every value printed is attained by an explicit placement found by the optimiser, so it is a valid lower bound on
the supremum; optimality is not claimed.
Sanity: kappa >= 3/2 must give 3*sqrt(3) = 5.19615 (hubs useless; b2's value, Prop. 2.2 of notes.md);
equilateral orthogonal hubs give (2 kappa/3) * 3 sqrt 3 for kappa <= 3/2.
Usage: hubfloor.py [restarts] [d]
"""
import sys, math
import numpy as np
from scipy.optimize import minimize

NODES = [(r, c) for r in range(3) for c in range(3)]
GRP = [lambda n: n[0], lambda n: n[1], lambda n: (n[0] - n[1]) % 3]
EDGES = [((r, c), ((r + 1) % 3, (c - 1) % 3)) for (r, c) in NODES]
assert len(set(frozenset(e) for e in EDGES)) == 9
PAIRS = [(0, 1), (1, 2), (0, 2)]
# incidence matrices: (M_k h_k)_e = h_k[g_k(e-)] - h_k[g_k(e+)]
M = np.zeros((3, 9, 3))
for k in range(3):
    for i, (a, b) in enumerate(EDGES):
        M[k, i, GRP[k](b)] += 1
        M[k, i, GRP[k](a)] -= 1
        assert GRP[k](a) != GRP[k](b)


def parts(x, d):
    return x[:9 * d].reshape(3, 3, d), x[9 * d:].reshape(9, d)


def evaluate(x, d, mode, kappa, beta=None):
    """returns (min_k ratio, per-merge ratios, smooth objective, gradient)"""
    h, v = parts(x, d)
    nv = np.linalg.norm(v, axis=1, keepdims=True)
    u = v / nv
    ratios = np.zeros(3)
    gh = np.zeros((3, 3, 3, d))   # d ratio_k / d h   (only block k nonzero)
    gu = np.zeros((3, 9, d))
    for k in range(3):
        Dk = M[k] @ h[k]                       # 9 x d
        B = np.sum(u * Dk)
        dB_h = M[k].T @ u                      # 3 x d
        dB_u = Dk
        s = np.array([np.linalg.norm(h[k, i] - h[k, j]) for i, j in PAIRS])
        ds = np.zeros((3, 3, d))               # d s_p / d h_k
        for p, (i, j) in enumerate(PAIRS):
            g = (h[k, i] - h[k, j]) / max(s[p], 1e-12)
            ds[p, i] += g
            ds[p, j] -= g
        W = s.sum() / 2
        dW = ds.sum(axis=0) / 2
        if mode == 'time':
            m, dm = W, dW
        else:
            p = int(np.argmax(s))
            if s[p] >= W / kappa:
                m, dm = s[p], ds[p]
            else:
                m, dm = W / kappa, dW / kappa
        ratios[k] = B / m
        gh[k, k] = dB_h / m - B * dm / m ** 2
        gu[k] = dB_u / m
    if beta is None:
        return ratios.min(), ratios, None, None
    w = np.exp(-beta * (ratios - ratios.min()))
    w /= w.sum()
    obj = ratios.min() - np.log(np.sum(np.exp(-beta * (ratios - ratios.min())))) / beta
    Gh = np.tensordot(w, gh, axes=1)
    Gu = np.tensordot(w, gu, axes=1)
    # chain rule through the normalisation u = v/|v|
    Gv = (Gu - u * np.sum(Gu * u, axis=1, keepdims=True)) / nv
    return ratios.min(), ratios, obj, np.concatenate([Gh.ravel(), Gv.ravel()])


def solve(mode, kappa, d, rng):
    x = rng.normal(size=18 * d)
    for beta in (2, 8, 32, 128, 512, 2048):
        f = lambda z: tuple(-t for t in evaluate(z, d, mode, kappa, beta)[2:4])
        r = minimize(lambda z: f(z), x, jac=True, method='L-BFGS-B', options=dict(maxiter=3000))
        x = r.x
    val, per, _, _ = evaluate(x, d, mode, kappa)
    return val, per, x


def describe(x, d):
    h, _ = parts(x, d)
    out = []
    for k in range(3):
        s = np.sort([np.linalg.norm(h[k, i] - h[k, j]) for i, j in PAIRS])
        out.append("(%.3f,%.3f,%.3f)" % tuple(s / s.max()))
    return " ".join(out)


def closed_forms():
    print("closed forms:")
    for kappa in (1.0, 4 / 3, 1.5):
        print("  kappa=%.4f: equilateral orthogonal hubs: %.5f" % (kappa, min(1, 2 * kappa / 3) * 3 * math.sqrt(3)))
    print("  time mode: equilateral orthogonal hubs: %.5f;  hubs (1,1,0) orthogonal, merge average: %.5f;  3*sqrt2 = %.5f"
          % (2 * math.sqrt(3), 1 + math.sqrt(2) + math.sqrt(3), 3 * math.sqrt(2)))


if __name__ == "__main__":
    restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    rng = np.random.default_rng(7)
    closed_forms()
    print("numerical maxima (softmin + L-BFGS, %d restarts, hubs in R^%d); per merge, in units of lambda; raw bits: 9" % (restarts, d))
    for mode, kappa in (('kappa', 2.0), ('kappa', 1.5), ('kappa', 1.4), ('kappa', 4 / 3), ('kappa', 1.2), ('kappa', 1.0), ('time', None)):
        res = []
        for it in range(restarts):
            val, per, x = solve(mode, kappa, d, rng)
            res.append((val, per, x))
        res.sort(key=lambda t: -t[0])
        best = res[0]
        lab = "kappa=%.4f" % kappa if mode == 'kappa' else "time (label units)"
        print("  %-20s best %.5f  (rho = %.4f of 9)  top5 %s  hub triangles %s"
              % (lab, best[0], best[0] / 9, np.round([t[0] for t in res[:5]], 4), describe(best[2], d)))
        sys.stdout.flush()
