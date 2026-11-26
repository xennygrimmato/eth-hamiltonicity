#!/usr/bin/env python3
"""Consistency tests of the checker's function code (not part of the proof, a guard against typos):
  * point enclosures agree with plain floating-point evaluation of the formulas and contain it;
  * interval enclosures on random boxes contain sampled values;
  * the hand-written gradients agree with sympy derivatives of the formula;
  * clnear evaluation equals clstar evaluation at sigma = (a+e, e-a);
  * the trigonometric identity behind the sine coordinates (symbolic, sympy).
"""
import math, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from flint import arb
import problems as P
from ivarb import Iv

random.seed(1)


def phi_float(s):
    c = [math.sqrt(1 - v * v) for v in s]
    r = -3.0
    for p, q in P.VERTS:
        r += 0.5 * math.sqrt((c[p] + c[q]) ** 2 + 10 * (s[p] - s[q]) ** 2)
    for p, q in P.PAIRS:
        r += 1.5 * abs(s[p] + s[q])
    return r


def F_float(t):
    return sum(math.cos((t[i] - t[j]) / 2) * math.sqrt(1 + 9 * math.sin((t[i] + t[j]) / 2) ** 2)
               for i, j in P.H3PAIRS) - 3


def contains(iv, v, tol=1e-12):
    return float(iv.lo.mid()) - tol <= v <= float(iv.hi.mid()) + tol


def test_points():
    for _ in range(2000):
        s = [random.uniform(-1, 1) for _ in range(6)]
        v = phi_float(s)
        e = P.clstar_nat([(x, x) for x in s])
        assert contains(e, v), (s, v, e)
        assert float(e.hi.mid()) - float(e.lo.mid()) < 1e-12
        t = [random.uniform(-math.pi / 2, math.pi / 2) for _ in range(3)]
        assert contains(P.hull3_nat([(x, x) for x in t]), F_float(t))
        y = [random.uniform(-0.5, 0.5) for _ in range(6)]
        sig = [None] * 6
        for k, (ij, ji) in enumerate(P.CLNEAR_IDX):
            sig[ij] = y[k] + y[3 + k]
            sig[ji] = y[3 + k] - y[k]
        assert contains(P.clnear_nat([(x, x) for x in y]), phi_float(sig))
    # equality points
    assert abs(phi_float([0] * 6)) == 0
    for (j, k), i_coords in (((0, 1), None),):
        pass
    print("points ok")


def corners():
    """Equality corners of Phi: for the pair {jk} and sign s, sigma_jk = sigma_kj = s,
    sigma_ji = sigma_ki = s, sigma_ij = sigma_ik = -s (i the third vertex)."""
    names = ["12", "13", "21", "23", "31", "32"]
    idx = {n: q for q, n in enumerate(names)}
    out = []
    for (j, k, i) in (("1", "2", "3"), ("1", "3", "2"), ("2", "3", "1")):
        for s in (1, -1):
            x = [0] * 6
            x[idx[j + k]] = x[idx[k + j]] = s
            x[idx[j + i]] = x[idx[k + i]] = s
            x[idx[i + j]] = x[idx[i + k]] = -s
            out.append((j + k, s, x, phi_float(x)))
    return out


def test_intervals():
    for _ in range(300):
        box = []
        for _ in range(6):
            a, b = sorted(random.uniform(-1, 1) for _ in range(2))
            box.append((a, b))
        e = P.clstar_nat(box)
        m = P.clstar_mvf(box)
        for _ in range(20):
            s = [random.uniform(a, b) for a, b in box]
            v = phi_float(s)
            assert contains(e, v)
            if m is not None:
                assert contains(m, v)
        tb = []
        for _ in range(3):
            a, b = sorted(random.uniform(-1.57, 1.57) for _ in range(2))
            tb.append((a, b))
        e = P.hull3_nat(tb); m = P.hull3_mvf(tb)
        for _ in range(20):
            t = [random.uniform(a, b) for a, b in tb]
            assert contains(e, F_float(t)) and (m is None or contains(m, F_float(t)))
    print("interval containment ok")


def test_gradients():
    x = sp.symbols("x0:6", real=True)
    c = lambda u: sp.sqrt(1 - u ** 2)
    V = sum(sp.sqrt((c(x[p]) + c(x[q])) ** 2 + 10 * (x[p] - x[q]) ** 2) / 2 for p, q in P.VERTS)
    dV = [sp.lambdify(x, sp.diff(V, xi)) for xi in x]
    t = sp.symbols("t0:3", real=True)
    F = sum(sp.cos((t[i] - t[j]) / 2) * sp.sqrt(1 + 9 * sp.sin((t[i] + t[j]) / 2) ** 2) for i, j in P.H3PAIRS)
    dF = [sp.lambdify(t, sp.diff(F, ti)) for ti in t]
    for _ in range(300):
        s = [random.uniform(-0.99, 0.99) for _ in range(6)]
        g = P.vsum_grad([Iv(v) for v in s])
        for i in range(6):
            assert contains(g[i], dV[i](*s), 1e-9), (i, s)
        th = [random.uniform(-1.57, 1.57) for _ in range(3)]
        gb = P.hull3_grad_balls([(v, v) for v in th])
        for i in range(3):
            assert abs(float(gb[i].mid()) - dF[i](*th)) < 1e-9
    print("gradients ok")


def test_identity():
    """cos(mu) sqrt(1 + 9 sin^2 delta) = 1/2 sqrt((cos p1 + cos p2)^2 + 10 (sin p1 - sin p2)^2)
    with mu = (p1 + p2)/2 (half-sum), delta = (p1 - p2)/2 (half-difference), p1, p2 in [-pi/2, pi/2]."""
    mu, de = sp.symbols("mu delta", real=True)
    p1, p2 = mu + de, mu - de
    lhs2 = (sp.cos(mu) ** 2) * (1 + 9 * sp.sin(de) ** 2)
    rhs2 = ((sp.cos(p1) + sp.cos(p2)) ** 2 + 10 * (sp.sin(p1) - sp.sin(p2)) ** 2) / 4
    d = sp.simplify(sp.expand_trig(sp.expand(rhs2 - lhs2)))
    assert d == 0, d
    # squares agree; both sides are >= 0 because |mu| <= pi/2 gives cos(mu) >= 0. With the roles
    # of mu and delta swapped the identity is false:
    swapped = (sp.cos(de) ** 2) * (1 + 9 * sp.sin(mu) ** 2)
    val = sp.N((rhs2 - swapped).subs({mu: 0.3, de: 0.1}))
    assert abs(val) > 1e-3
    print("identity ok: squares agree symbolically (difference simplifies to 0); swapped roles differ by", val)


if __name__ == "__main__":
    test_points()
    test_intervals()
    test_gradients()
    test_identity()
    for pair, s, x, v in corners():
        print("corner pair %s s=%+d sigma=%s Phi=%r" % (pair, s, x, v))
        assert v == 0
    # the variant 'other four coordinates = -s' is not an equality point:
    x = [1, -1, 1, -1, -1, -1]  # sigma12 = sigma21 = 1, rest -1
    print("variant sigma12=sigma21=1, other four -1: Phi =", phi_float(x))
    print("selftest passed")
