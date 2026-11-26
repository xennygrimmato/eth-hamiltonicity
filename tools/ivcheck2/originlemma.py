"""Rigorous treatment of the equality point 0 (own argument, independent of the prover's tests).

hull3 (F >= 3 near t = 0).  On C = [-r, r]^3:
  * F(0) = 3 exactly (each term cos 0 * sqrt(1 + 0) = 1);
  * F is even (cos and sin^2 are even), and smooth, so grad F(0) = 0;
  * the Hessian of F is positive definite at every point of C: C is cut into n^3 sub-boxes and on
    each one the Arb ball enclosures of the Hessian entries (symbolic second derivatives from
    sympy) have leading principal minors whose enclosures are > 0 (Sylvester's criterion applied
    to every symmetric matrix whose entries lie in the balls).
  Hence F is convex on C with a critical point at 0, so F >= F(0) = 3 on C.

clnear (Phi >= 0 near (a, e) = 0).  Write Phi(a, e) = V(a, e) - 3 + 3 (|e12| + |e13| + |e23|),
V = sum of the three vertex terms.  On G = A x E with A = [-r, r]^3 (a) and E = [-r, r]^3 (e):
  * g(a) = V(a, 0) has g(0) = 3 exactly (c = 1, Q = 4 at every vertex), is even in a (the global
    flip sigma -> -sigma maps (a, 0) to (-a, 0) and leaves V invariant), hence grad g(0) = 0;
  * Hessian of g positive definite on A (same sub-box/Sylvester method), so g >= 3 on A;
  * L_k := sup over G of |dV/de_k| < 3 (Arb enclosures of the symbolic derivative on sub-boxes of
    G), so by the mean value theorem along the segment (a, 0) -> (a, e), which lies in G,
    V(a, e) >= V(a, 0) - sum_k L_k |e_k|.
  Hence Phi(a, e) >= (g(a) - 3) + sum_k (3 - L_k) |e_k| >= 0 on G, which contains the part of
  every orthant box within distance r (sup norm) of the origin.
"""
import itertools
import sympy as sp
from sympy.printing.pycode import PythonCodePrinter
from flint import arb


class _ArbPrinter(PythonCodePrinter):
    def _print_Rational(self, e):
        return "(arb(%d)/arb(%d))" % (e.p, e.q)

    def _print_Integer(self, e):
        return "arb(%d)" % e.p

    def _print_Half(self, e):
        return "(arb(1)/arb(2))"

    def _print_Function(self, e):
        return PythonCodePrinter._print_Function(self, e)

    def _print_Pow(self, e, rational=False):
        b, x = e.as_base_exp()
        if x == sp.Rational(1, 2):
            return "(%s).sqrt()" % self._print(b)
        if x == -sp.Rational(1, 2):
            return "(arb(1)/(%s).sqrt())" % self._print(b)
        if x.is_Integer and x > 0:
            return "(" + "*".join(["(%s)" % self._print(b)] * int(x)) + ")"
        if x.is_Integer and x < 0:
            return "(arb(1)/(" + "*".join(["(%s)" % self._print(b)] * int(-x)) + "))"
        if x.is_Rational and x.q == 2:
            # b^(p/2) = sqrt(b)^p
            p = int(x.p)
            s = "(%s).sqrt()" % self._print(b)
            if p > 0:
                return "(" + "*".join([s] * p) + ")"
            return "(arb(1)/(" + "*".join([s] * (-p)) + "))"
        raise NotImplementedError(str(e))


def to_arb_func(args, expr):
    """Compile a sympy expression into a Python function on Arb balls.  Every constant is an exact
    Arb rational, sqrt/cos/sin are Arb's rigorous ball functions."""
    pr = _ArbPrinter()
    body = pr.doprint(expr)
    body = body.replace("math.sqrt", "_sqrt").replace("math.cos", "_cos").replace("math.sin", "_sin")
    src = "def _f(%s):\n    return %s\n" % (", ".join(str(a) for a in args), body)
    ns = {"arb": arb, "_sqrt": lambda b: b.sqrt(), "_cos": lambda b: b.cos(), "_sin": lambda b: b.sin()}
    exec(src, ns)
    return ns["_f"], src


def sylvester_pd(H):
    """H: 3x3 list of Arb balls (H[i][j] encloses the (i,j) entry; symmetric in reality).
    True if every symmetric matrix with entries in the balls is positive definite."""
    m1 = H[0][0]
    m2 = H[0][0] * H[1][1] - H[0][1] * H[1][0]
    m3 = (H[0][0] * (H[1][1] * H[2][2] - H[1][2] * H[2][1])
          - H[0][1] * (H[1][0] * H[2][2] - H[1][2] * H[2][0])
          + H[0][2] * (H[1][0] * H[2][1] - H[1][1] * H[2][0]))
    return bool(m1 > 0 and m2 > 0 and m3 > 0), (m1, m2, m3)


def _subboxes(r, n, dim):
    r = arb(r)
    edges = [(-r + 2 * r * arb(i) / n, -r + 2 * r * arb(i + 1) / n) for i in range(n)]
    for combo in itertools.product(range(n), repeat=dim):
        yield [edges[i][0].union(edges[i][1]) for i in combo]


# ----------------------------------------------------------------- symbolic setup -------
def hull3_symbolic():
    t = sp.symbols("t0 t1 t2", real=True)
    F = 0
    for i, j in ((0, 1), (0, 2), (1, 2)):
        F += sp.cos((t[i] - t[j]) / 2) * sp.sqrt(1 + 9 * sp.sin((t[i] + t[j]) / 2) ** 2)
    return t, F


def clnear_symbolic():
    a = sp.symbols("a12 a13 a23", real=True)
    e = sp.symbols("e12 e13 e23", real=True)
    s12, s21 = a[0] + e[0], e[0] - a[0]
    s13, s31 = a[1] + e[1], e[1] - a[1]
    s23, s32 = a[2] + e[2], e[2] - a[2]
    c = lambda u: sp.sqrt(1 - u ** 2)
    V = lambda u, v: sp.sqrt((c(u) + c(v)) ** 2 + 10 * (u - v) ** 2) / 2
    Vs = V(s12, s13) + V(s21, s23) + V(s31, s32)
    return a, e, Vs


def prove_hull3(r, n):
    t, F = hull3_symbolic()
    assert sp.simplify(F.subs({ti: 0 for ti in t}) - 3) == 0
    # evenness: F(-t) = F(t) symbolically
    assert sp.simplify(F.subs({ti: -ti for ti in t}, simultaneous=True) - F) == 0
    Hf = [[to_arb_func(t, sp.diff(F, t[i], t[j]))[0] for j in range(3)] for i in range(3)]
    worst = None
    count = 0
    for b in _subboxes(r, n, 3):
        H = [[Hf[i][j](*b) for j in range(3)] for i in range(3)]
        ok, mins = sylvester_pd(H)
        count += 1
        if not ok:
            return False, {"r": r, "n": n, "failed_box": [str(x) for x in b], "minors": [str(x) for x in mins]}
        lo = min(m.lower() for m in mins)
        worst = lo if worst is None or lo < worst else worst
    return True, {"r": r, "n": n, "subboxes": count, "min_minor_lower": str(worst)}


def prove_clnear(r, nH, nL):
    a, e, Vs = clnear_symbolic()
    zero = {x: 0 for x in list(a) + list(e)}
    assert sp.simplify(Vs.subs(zero) - 3) == 0
    g = Vs.subs({x: 0 for x in e})
    assert sp.simplify(g.subs({x: -x for x in a}, simultaneous=True) - g) == 0  # g even
    Hf = [[to_arb_func(a, sp.diff(g, a[i], a[j]))[0] for j in range(3)] for i in range(3)]
    worst = None
    cH = 0
    for b in _subboxes(r, nH, 3):
        H = [[Hf[i][j](*b) for j in range(3)] for i in range(3)]
        ok, mins = sylvester_pd(H)
        cH += 1
        if not ok:
            return False, {"stage": "hessian", "failed_box": [str(x) for x in b]}
        lo = min(m.lower() for m in mins)
        worst = lo if worst is None or lo < worst else worst
    args = list(a) + list(e)
    dVf = [to_arb_func(args, sp.diff(Vs, e[k]))[0] for k in range(3)]
    L = [arb(0)] * 3
    cL = 0
    for b in _subboxes(r, nL, 6):
        for k in range(3):
            v = dVf[k](*b)
            if not v.is_finite():
                return False, {"stage": "L", "failed_box": [str(x) for x in b]}
            u = abs(v).upper()
            if u > L[k]:
                L[k] = u
        cL += 1
    ok = all(Lk < 3 for Lk in L)
    return ok, {"r": r, "nH": nH, "hessian_subboxes": cH, "min_minor_lower": str(worst),
                "nL": nL, "L_subboxes": cL, "L": [str(x) for x in L]}


if __name__ == "__main__":
    import sys, json, time
    t0 = time.time()
    print("hull3", prove_hull3(float(sys.argv[1]) if len(sys.argv) > 1 else 0.125, 4), time.time() - t0)
    t0 = time.time()
    print("clnear", prove_clnear(float(sys.argv[2]) if len(sys.argv) > 2 else 0.125, 4, 3), time.time() - t0)
