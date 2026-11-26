#!/usr/bin/env python3
"""Guards for the k2 encoding (not part of the proof):
  * K2Spec.G at points agrees with a plain float implementation of Br' written verbatim from the spec
    (notes §5.4: N by the linear test, |Q|, X) and with the trigonometric definition of §5.2
    (N_i = cos((kappa_i - |mu_i|)_+), sin kappa_i = lam cos delta_i), on random points of each piece;
  * the piece test (misses) never discards a point of the piece, and discards points outside it;
  * the hand-written gradient agrees with sympy;
  * k2near(a, t) agrees with k2far at sigma = (a + s t^2, s t^2 - a);
  * if the ivcert example binary is present: the ivcert encoding agrees with this one at the same points.
"""
import itertools, math, os, random, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from flint import arb
import problems as P
from ivarb import Iv

random.seed(3)
JOBS = {"s910": ("9/10", "6/5", 0.9, 1.2), "cl0": ("12/13", "15/13", 12 / 13, 15 / 13)}


def br_float(s, lam, eta):
    tau = math.sqrt(1 - lam * lam)
    c = [math.sqrt(max(0.0, 1 - v * v)) for v in s]
    N = []
    for p, q in P.VERTS:
        Q = s[p] + s[q]
        W = (c[p] + c[q]) ** 2 + Q * Q
        C = 0.5 * math.sqrt(tau * tau * (c[p] + c[q]) ** 2 + (s[p] - s[q]) ** 2) + lam / 2 * abs(Q)
        N.append(1.0 if 2 * abs(Q) >= lam * W else C)
    E = sum(abs(s[p] + s[q]) for p, q in P.PAIRS)
    X = sum(abs(s[p] + s[q]) for p, q in P.VERTS) - E
    return sum(N) - lam / 2 * X - eta


def br_trig(s, lam, eta):
    psi = [math.asin(v) for v in s]
    tot = 0.0
    for p, q in P.VERTS:
        mu = (psi[p] + psi[q]) / 2
        d = (psi[p] - psi[q]) / 2
        k = math.asin(lam * math.cos(d))
        tot += math.cos(max(k - abs(mu), 0.0))
    E = sum(abs(s[p] + s[q]) for p, q in P.PAIRS)
    X = sum(abs(s[p] + s[q]) for p, q in P.VERTS) - E
    return tot - lam / 2 * X - eta


def piece_float(s, lam, case, sg):
    c = [math.sqrt(max(0.0, 1 - v * v)) for v in s]
    Q = [s[p] + s[q] for p, q in P.VERTS]
    W = [(c[p] + c[q]) ** 2 + Q[i] ** 2 for i, (p, q) in enumerate(P.VERTS)]
    ok = Q[0] <= 0 <= Q[1] and Q[2] >= 0 and 2 * abs(Q[0]) <= lam * W[0] and 2 * Q[1] <= lam * W[1]
    ok &= (2 * Q[2] <= lam * W[2]) if case == "c" else (2 * Q[2] >= lam * W[2])
    eps = [s[p] + s[q] for p, q in P.PAIRS]
    return ok and all(sg[k] * eps[k] >= 0 for k in range(3))


def mid(iv):
    return float(((iv.lo + iv.hi) / 2).mid())


def test_points(npts=3000):
    worst = 0.0
    for job, (ls, es, lam, eta) in JOBS.items():
        pts = []
        while len(pts) < npts:
            s = [random.uniform(-1, 1) for _ in range(6)]
            if piece_float(s, lam, "c", [1, 1, 1]) or any(
                    piece_float(s, lam, cs, sg) for cs in "cl" for sg in itertools.product((1, -1), repeat=3)):
                pts.append(s)
        hits = 0
        for s in pts:
            b = br_float(s, lam, eta)
            assert abs(b - br_trig(s, lam, eta)) < 1e-12
            for cs in "cl":
                for sg in itertools.product((1, -1), repeat=3):
                    name = "k2far:lam=%s:eta=%s:case=%s:s=%s" % (ls, es, cs, "".join("+" if x > 0 else "-" for x in sg))
                    spec = P.K2Spec(name)
                    box = tuple((v, v) for v in s)
                    inside = piece_float(s, lam, cs, sg)
                    assert spec.misses(box) == (not inside) or inside, "piece test discards a point inside"
                    if not inside:
                        assert spec.misses(box), "point outside not discarded %r" % (s,)
                        continue
                    hits += 1
                    g = spec.G(spec.sigma(spec.coords(box)))   # verbatim form
                    worst = max(worst, abs(mid(g) - spec.M * b))
                    worst = max(worst, abs(mid(spec.nat(box)) - spec.M * b))   # collected form
                    assert float(g.lo.mid()) <= spec.M * b + 1e-12
        print("points", job, len(pts), "piece hits", hits)
    print("max |G - M Br'| at piece points:", worst)
    assert worst < 1e-11


def sympy_G(case, sg, lam):
    x = sp.symbols("x0:6", real=True)
    lam = sp.Rational(lam)
    t2 = 1 - lam ** 2
    c = [sp.sqrt(1 - v ** 2) for v in x]
    V = [sp.sqrt(t2 * (c[p] + c[q]) ** 2 + (x[p] - x[q]) ** 2) / 2 for p, q in P.VERTS]
    Q = [x[p] + x[q] for p, q in P.VERTS]
    N3 = V[2] + lam / 2 * Q[2] if case == "c" else 1
    E = sum(sg[k] * (x[p] + x[q]) for k, (p, q) in enumerate(P.PAIRS))
    X = -Q[0] + Q[1] + Q[2] - E
    return x, V[0] - lam / 2 * Q[0] + V[1] + lam / 2 * Q[1] + N3 - lam / 2 * X


def test_gradients():
    worst = 0.0
    for ls in ("9/10", "12/13"):
        for case in "cl":
            for sg in ((1, -1, 1), (-1, -1, 1)):
                x, G = sympy_G(case, sg, ls)
                dG = [sp.lambdify(x, sp.diff(G, xi)) for xi in x]
                spec = P.K2Spec("k2far:lam=%s:eta=1/1:case=%s:s=%s" % (ls, case, "".join("+" if v > 0 else "-" for v in sg)))
                for _ in range(200):
                    s = [random.uniform(-0.95, 0.95) for _ in range(6)]
                    g = spec.gradG_sigma([Iv(v) for v in s])
                    for i in range(6):
                        worst = max(worst, abs(mid(g[i]) - dG[i](*s)))
    print("max gradient discrepancy vs sympy:", worst)
    assert worst < 1e-10


def test_near():
    worst = 0.0
    for sg in itertools.product((1, -1), repeat=3):
        st = "".join("+" if v > 0 else "-" for v in sg)
        near = P.K2Spec("k2near:lam=12/13:eta=15/13:case=c:s=%s:t=0.70703125" % st)
        far = P.K2Spec("k2far:lam=12/13:eta=15/13:case=c:s=%s" % st)
        for _ in range(300):
            a = [random.uniform(-0.49, 0.49) for _ in range(3)]
            t = [random.uniform(0, 0.7) for _ in range(3)]
            e = [sg[k] * t[k] ** 2 for k in range(3)]
            s = [a[0] + e[0], a[1] + e[1], e[0] - a[0], a[2] + e[2], e[1] - a[1], e[2] - a[2]]
            gn = near.nat(tuple((v, v) for v in a + t))
            gf = far.nat(tuple((v, v) for v in s))
            worst = max(worst, abs(mid(gn) - mid(gf)))
    print("max |near - far|:", worst)
    assert worst < 1e-12


def test_enclosures(nbox=300, npt=20):
    """nat and mvf enclosures over random boxes contain the point values at random points of the box."""
    names = ["k2far:lam=9/10:eta=6/5:case=c:s=+-+", "k2far:lam=9/10:eta=6/5:case=l:s=++-",
             "k2near:lam=12/13:eta=15/13:case=c:s=-+-:t=0.70703125"]
    bad = 0
    for name in names:
        spec = P.K2Spec(name)
        for _ in range(nbox):
            w = random.choice((0.3, 0.05, 0.005))
            if spec.near:
                lo = [random.uniform(-0.49, 0.49 - w) for _ in range(3)] + [random.uniform(0, 0.7 - w) for _ in range(3)]
            else:
                lo = [random.uniform(-0.99, 0.99 - w) for _ in range(6)]
            box = tuple((l, l + w) for l in lo)
            encs = [spec.nat(box), spec.mvf(box)]
            for _ in range(npt):
                x = tuple((v, v) for v in (random.uniform(l, h) for l, h in box))
                fx = spec.nat(x)
                for e in encs:
                    if e is not None and not (e.lo <= fx.hi and fx.lo <= e.hi):
                        bad += 1
    print("enclosure containment failures:", bad)
    assert bad == 0


def test_vs_ivcert():
    exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../ivcert/target/release/examples/k2_points")
    if not os.path.exists(exe):
        print("ivcert example binary not built; skipping the cross-encoding comparison")
        return
    worst = 0.0
    n = 0
    for job, (ls, es, lam, eta) in JOBS.items():
        for cs in "cl":
            for sg in itertools.product((1, -1), repeat=3):
                st = "".join("+" if v > 0 else "-" for v in sg)
                names = ["k2far:lam=%s:eta=%s:case=%s:s=%s" % (ls, es, cs, st)]
                if cs == "c" and job == "cl0":
                    names.append("k2near:lam=%s:eta=%s:case=c:s=%s:t=0.70703125" % (ls, es, st))
                for name in names:
                    spec = P.K2Spec(name)
                    if spec.near:
                        pts = [[random.uniform(-0.49, 0.49) for _ in range(3)] + [random.uniform(0, 0.7) for _ in range(3)]
                               for _ in range(300)]
                    else:
                        pts = [[random.uniform(-1, 1) for _ in range(6)] for _ in range(300)]
                    out = subprocess.run([exe, name], input="\n".join(" ".join(repr(v) for v in p) for p in pts),
                                         capture_output=True, text=True, check=True).stdout.split("\n")
                    for p, ln in zip(pts, out):
                        lo, hi, ex = ln.split()[:3]
                        box = tuple((v, v) for v in p)
                        mine = spec.nat(box)
                        worst = max(worst, abs(mid(mine) - float(lo)))
                        # ivcert's exclusion of a point must be confirmed here too (and conversely)
                        assert bool(int(ex)) == spec.misses(box) or not spec.near and spec.rho > 0
                        n += 1
    print("ivcert vs ivcheck2 encodings: %d points, max |difference| %.3g" % (n, worst))
    assert worst < 1e-11


if __name__ == "__main__":
    test_points()
    test_gradients()
    test_near()
    test_enclosures()
    test_vs_ivcert()
    print("selftest_k2 OK")
