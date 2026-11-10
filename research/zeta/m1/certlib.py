"""Generic rigorous 1D sign certification by Taylor models with ball arithmetic."""
from flint import arb, acb

def ball(a, b):
    """arb ball containing [a,b] (a,b arb or float)."""
    a = arb(a); b = arb(b)
    return (a + b) / 2 + arb(0, ((b - a) / 2).upper()) if True else None

def lower_on(fun0, fun1, fun2box, a, b):
    """certified lower bound of f on [a,b]: f(c) - |f'(c)| h - sup|f''| h^2/2, c midpoint, h half-width.
    fun0, fun1 evaluate f, f' at a point (arb), fun2box evaluates f'' on a ball."""
    a = arb(a); b = arb(b)
    c = (a + b) / 2; h = (b - a) / 2
    B = c + arb(0, h.upper())
    f0 = fun0(c); f1 = fun1(c); f2 = fun2box(B)
    return f0 - abs(f1) * h - abs(f2) * h * h / 2

def certify_positive(fun0, fun1, fun2box, a, b, thresh=0, maxdepth=40, minw=1e-12):
    """prove f > thresh on [a,b] by adaptive bisection. Returns (ok, n_boxes, min_lower_bound)."""
    stack = [(arb(a), arb(b), 0)]
    n = 0; mn = None
    while stack:
        lo, hi, d = stack.pop()
        n += 1
        L = lower_on(fun0, fun1, fun2box, lo, hi)
        if L > thresh:
            v = L.lower()
            mn = v if mn is None or v < mn else mn
            continue
        if d >= maxdepth or float((hi - lo).mid()) < minw:
            return False, n, (float(lo.mid()), float(hi.mid()))
        m = (lo + hi) / 2
        stack.append((lo, m, d + 1)); stack.append((m, hi, d + 1))
    return True, n, mn
