"""Tripod x line ("book with three pages"): do the elementary price axioms obstruct it?

Point: (leg, t, z), t >= 0 distance from the spine, z the coordinate along the spine.  Any two pages form a flat plane,
which is convex in the book, so the flat law fixes delta on every set of sites inside two pages.
Axioms as in ../v2/cone.py (pair, monotone, submodular on intersecting sets, flat law, midpoint convexity), plus
optionally  perimeter <= omega * delta(triple)  with omega = 9/4 (OpenAI's claimed value; conditional).
"""
import sys, math, itertools, numpy as np
sys.path.insert(0, "../v2")
from cone import RateLP, half_perimeter

class Book:
    def dist(self, p, q):
        (a, t, z), (b, s, w) = p, q
        if a == b or t == 0 or s == 0: return math.hypot(t - s, z - w)
        return math.hypot(t + s, z - w)
    def geodesic_point(self, p, q, lam):
        (a, t, z), (b, s, w) = p, q
        if a == b or t == 0 or s == 0:
            leg = a if t > 0 else b
            return (leg, (1-lam)*t + lam*s, (1-lam)*z + lam*w)
        x = (1-lam)*t - lam*s                               # signed coordinate: page a positive, page b negative
        return (a, x, (1-lam)*z + lam*w) if x >= 0 else (b, -x, (1-lam)*z + lam*w)
    def flat_coords(self, pts):
        legs = sorted({a for a, t, z in pts if t > 0})
        if len(legs) > 2: return None
        return [np.array([(t if (not legs or a == legs[0]) else -t), z]) for a, t, z in pts]

def run(pts, names, omega=None, convex_k=2, label=""):
    lp = RateLP(Book(), pts, names, convex_k=convex_k)
    if omega:
        for tri in itertools.combinations(range(len(pts)), 3):
            per = lp.D[tri[0], tri[1]] + lp.D[tri[0], tri[2]] + lp.D[tri[1], tri[2]]
            lp._add([(lp.mask(tri), -omega)], -per, "omega")
    tips = lp.mask([names.index(x) for x in ("p", "q", "r")])
    rg = lp.range_of(tips)
    print("%-52s sites %2d, forced %4d, ineq %6d: delta(tips) in %s" % (label, len(pts), lp.nflat, len(lp.rhs),
          "INFEASIBLE" if rg is None else "[%.4f, %.4f]" % rg))
    return lp

if __name__ == "__main__":
    t0 = 1/math.sqrt(8)
    tips = [(0, 1.0, 0.0), (1, 1.0, 0.0), (2, 1.0, 0.0)]
    print("one-step bound 3 sqrt(1+t^2) - t at t = 1/sqrt 8: %.4f;  8/3 = %.4f;  ball lemma in T x l_2: 2.7342" % (3*math.sqrt(1+t0*t0) - t0, 8/3))
    run(tips + [(0, 0.0, 0.0)], ["p", "q", "r", "o"], label="tips + centre")
    run(tips + [(0, 0.0, 0.0), (0, 0.0, t0), (0, 0.0, -t0)], ["p", "q", "r", "o", "u", "d"], label="+ spine points at +-1/sqrt8")
    run(tips + [(0, 0.0, 0.0), (0, 0.0, t0), (0, 0.0, -t0)], ["p", "q", "r", "o", "u", "d"], omega=2.25, label="  same, with omega = 9/4")
    sp = [(0, 0.0, z) for z in (-1.0, -t0, 0.0, t0, 1.0)]
    run(tips + sp, ["p", "q", "r"] + ["s%d" % i for i in range(5)], omega=2.25, label="+ five spine points, omega")
    half = [(a, 0.5, z) for a in range(3) for z in (-t0/2, t0/2)]
    run(tips + sp[1:4] + half, ["p", "q", "r", "u", "o", "d"] + ["h%d" % i for i in range(6)], omega=2.25, convex_k=3, label="+ six midpoints tip-spine, omega, 3-leg convexity")
    # X_4(pi/2) with its natural companions
    a = math.pi/4; c, s = math.cos(a), math.sin(a)
    X = [(0, c, s), (1, c, -s), (2, c, -s), (0, 0.0, 0.0), (1, c, s), (2, c, s), (0, c, -s), (0, 0.0, s), (0, 0.0, -s)]
    nm = ["p", "q", "r", "m", "q'", "r'", "p'", "u", "d"]
    run(X, nm, omega=2.25, convex_k=3, label="X_4(pi/2) + mirror images + spine, omega")
