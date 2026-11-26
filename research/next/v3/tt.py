"""Tripod x tripod (and x tripod, x line): upper bounds on the shared-label rate of the three tips of the first factor.

Forced by rho_2: the tips E1, E3, E5 (cells (0,1), (1,2), (2,0)) and the points 0, I, g (g of order 3, sigma = +1)
have all cross distances 1 and all distances inside each triple sqrt 2.  Every square {s, E_i, s', E_j} is flat with
a common centre m, so the convex hull of the six points is tripod x tripod with arms 1/sqrt 2 (checked below on the
distance table).  Flat sets: sites using at most two legs in each tripod factor.
"""
import sys, math, itertools, numpy as np
sys.path.insert(0, "../v2")
import cone
from cone import RateLP
from hexbook import mean_width, LP3

class TreeProduct:
    """product of tripods (and lines): a point is a tuple of coordinates; a tripod coordinate is (leg, r), a line coordinate a float"""
    def __init__(self, kinds): self.kinds = kinds                    # e.g. "TT", "TTR", "TTT"
    def _d1(self, k, a, b):
        if k == "R": return abs(a - b)
        (l, r), (m, s) = a, b
        return abs(r - s) if (l == m or r == 0 or s == 0) else r + s
    def dist(self, p, q): return math.sqrt(sum(self._d1(k, a, b)**2 for k, a, b in zip(self.kinds, p, q)))
    def geodesic_point(self, p, q, lam):
        out = []
        for k, a, b in zip(self.kinds, p, q):
            if k == "R": out.append((1-lam)*a + lam*b); continue
            (l, r), (m, s) = a, b
            if l == m or r == 0 or s == 0: out.append((l if r > 0 else m, (1-lam)*r + lam*s))
            else:
                x = (1-lam)*r - lam*s
                out.append((l, x) if x >= 0 else (m, -x))
        return tuple(out)
    def flat_coords(self, pts):
        cols = []
        for i, k in enumerate(self.kinds):
            if k == "R": cols.append([p[i] for p in pts]); continue
            legs = sorted({p[i][0] for p in pts if p[i][1] > 0})
            if len(legs) > 2: return None
            cols.append([(p[i][1] if (not legs or p[i][0] == legs[0]) else -p[i][1]) for p in pts])
        return [np.array(v) for v in zip(*cols)]

def run(kinds, pts, tips, label, convex_k=2):
    lp = LP3(TreeProduct(kinds), pts, convex_k=convex_k)
    hi = lp.solve([(lp.mask(tips), 1.0)], -1)
    U = -hi.fun
    print("%-64s sites %2d  max delta(tips) = %.5f   6/U = %.5f" % (label, len(pts), U, 6/U))
    return U

if __name__ == "__main__":
    # distance table of the six forced points against tripod x tripod with arms 1/sqrt 2
    from rank2 import rk, add, cell, Z, I, R2, sig
    g = next(h for h in R2 if sig[h] == (1, 2, 0)); tipsM = [cell[(0, 1)], cell[(1, 2)], cell[(2, 0)]]; S = [Z, I, g]
    r = 1/math.sqrt(2); X = TreeProduct("TT")
    pos = {tipsM[i]: ((i, r), (0, 0.0)) for i in range(3)}; pos.update({S[j]: ((0, 0.0), (j, r)) for j in range(3)})
    ok = all(abs(X.dist(pos[a], pos[b])**2 - rk[add(a, b)]) < 1e-12 for a in pos for b in pos)
    print("tips and {0, I, g} have the distance table of tripod x tripod (arms 1/sqrt 2):", ok, " (g <-> permutation %s)" % (sig[g],))

    o = (0, 0.0)
    tip = lambda i: ((i, 1.0), o)
    print("\nunit arms; book x line reference: 2.82843, book x l_2: 2.73423, target 8/3 = 2.66667")
    for ts in ([0.35], [0.25, 0.5], [0.2, 0.4, 0.8]):
        pts = [tip(i) for i in range(3)] + [(o, o)] + [(o, (j, t)) for t in ts for j in range(3)]
        run("TT", pts, [0, 1, 2], "T x T, second-factor sites at radii %s" % ts)
    pts = [tip(i) for i in range(3)] + [(o, o)] + [(o, (j, 0.35)) for j in range(3)] + [((i, 0.5), o) for i in range(3)]
    run("TT", pts, [0, 1, 2], "T x T, + midpoints of the arms", convex_k=3)
    pts = [tip(i) for i in range(3)] + [(o, o)] + [(o, (j, 0.35)) for j in range(3)] + [((i, 0.5), (j, 0.35)) for i in range(3) for j in range(2)]
    run("TT", pts, [0, 1, 2], "T x T, + six off-axis sites")
    o3 = (o, o, 0.0)
    for t, z in ((0.3, 0.3), (0.25, 0.35), (0.35, 0.25)):
        pts = [((i, 1.0), o, 0.0) for i in range(3)] + [o3] + [(o, (j, t), 0.0) for j in range(3)] + [(o, o, z), (o, o, -z)]
        run("TTR", pts, [0, 1, 2], "T x T x R, second-factor radius %.2f, line sites +-%.2f" % (t, z))
    for t in (0.25, 0.35):
        pts = [((i, 1.0), o, o) for i in range(3)] + [(o, o, o)] + [(o, (j, t), o) for j in range(3)] + [(o, o, (j, t)) for j in range(3)]
        run("TTT", pts, [0, 1, 2], "T x T x T, radius %.2f in factors 2 and 3" % t)
