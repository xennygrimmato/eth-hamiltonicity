"""The functions to be bounded, written from the mathematical statement (not from ivcert).

All evaluations take a box as a list of Iv (or degenerate Iv for points) and return Iv
enclosures.  Gradients are hand-derived (and cross-checked against sympy in selftest.py).

clstar  : x = (s12, s13, s21, s23, s31, s32) in [-1,1]^6
          Phi = 1/2 sum_i sqrt((c_ij + c_ik)^2 + 10 (s_ij - s_ik)^2) - 3
                + 3/2 (|s12+s21| + |s13+s31| + |s23+s32|),   c = sqrt(1 - s^2)
          vertex 1 -> (x0, x1), vertex 2 -> (x2, x3), vertex 3 -> (x4, x5)
          pair {12} -> (x0, x2), {13} -> (x1, x4), {23} -> (x3, x5)
clnear  : y = (a12, a13, a23, e12, e13, e23); s_ij = a + e, s_ji = e - a for (ij) in 12,13,23,
          so |s_ij + s_ji| = 2|e|; Phi as above.
hull3   : F(t) = sum_{i<j} cos((t_i - t_j)/2) sqrt(1 + 9 sin^2((t_i + t_j)/2)) - 3.
"""
from flint import arb
from ivarb import Iv, ONE

VERTS = ((0, 1), (2, 3), (4, 5))
PAIRS = ((0, 2), (1, 4), (3, 5))
# clnear: pair k uses a_k = y[k], e_k = y[3+k]; s_ij index, s_ji index in the clstar vector
CLNEAR_IDX = ((0, 2), (1, 4), (3, 5))  # (ij, ji) positions: 12->(s12,s21), 13->(s13,s31), 23->(s23,s32)


def cfun(u):
    """c = sqrt(1 - u^2), valid for u within [-1, 1]."""
    return (ONE - u.sqr()).sqrt()


def vertex(u, v):
    cu = cfun(u)
    cv = cfun(v)
    S = cu + cv
    D = u - v
    Q = S.sqr() + D.sqr().scale(10)
    return Q.sqrt().scale(0.5)


def vsum(x):
    return vertex(x[0], x[1]) + vertex(x[2], x[3]) + vertex(x[4], x[5])


def vsum_grad(x):
    """Enclosure of grad of sum_i V_i over the box x, or None when some c may vanish."""
    g = [None] * 6
    for (p, q) in VERTS:
        u, v = x[p], x[q]
        cu = cfun(u)
        cv = cfun(v)
        if not (cu.lo > 0 and cv.lo > 0):
            return None
        S = cu + cv
        D = u - v
        Q = S.sqr() + D.sqr().scale(10)
        if not (Q.lo > 0):
            return None
        inv = Q.sqrt().scale(2).recip_pos()  # 1/(2 sqrt Q)
        D10 = D.scale(10)
        # d c_u / d u = -u / c_u
        g[p] = (S * (-u / cu) + D10) * inv
        g[q] = (S * (-v / cv) - D10) * inv
    return g


def sigma_to_x(box):
    return [Iv(lo, hi) for lo, hi in box]


def clstar_nat(box):
    x = sigma_to_x(box)
    r = vsum(x) - 3
    for (p, q) in PAIRS:
        r = r + (x[p] + x[q]).abs().scale(1.5)
    return r


def _point(box):
    m = [lo + 0.5 * (hi - lo) for lo, hi in box]
    for (lo, hi), mi in zip(box, m):
        assert lo <= mi <= hi
    return m


def clstar_mvf(box):
    """Mean-value form: Phi(x) in Phi(m) + sum_i G_i (x_i - m_i).  The vertex part uses the
    interval gradient over the box; each |eps_k| (eps_k = s_ij + s_ji) uses the exact
    identity |u| - |w| = t (u - w) with t in [-1, 1] (t = sign when the sign of eps_k is
    fixed on the box)."""
    x = sigma_to_x(box)
    g = vsum_grad(x)
    if g is None:
        return None
    m = _point(box)
    xm = [Iv(mi) for mi in m]
    val = vsum(xm) - 3
    coef = list(g)
    for (p, q) in PAIRS:
        em = xm[p] + xm[q]
        val = val + em.abs().scale(1.5)
        eb = x[p] + x[q]
        if eb.lo >= 0:
            t = Iv(1.5)
        elif eb.hi <= 0:
            t = Iv(-1.5)
        else:
            t = Iv(-1.5, 1.5)
        coef[p] = coef[p] + t
        coef[q] = coef[q] + t
    for i in range(6):
        dx = Iv(arb(box[i][0]) - arb(m[i]), arb(box[i][1]) - arb(m[i]))
        val = val + coef[i] * dx
    return val


# ---------------------------------------------------------------- clnear ----------
def clnear_sigma(y):
    s = [None] * 6
    for k, (ij, ji) in enumerate(CLNEAR_IDX):
        a, e = y[k], y[3 + k]
        s[ij] = a + e
        s[ji] = e - a
    return s


def clnear_nat(box):
    y = sigma_to_x(box)
    r = vsum(clnear_sigma(y)) - 3
    for k in range(3):
        r = r + y[3 + k].abs().scale(3)
    return r


def clnear_mvf(box):
    y = sigma_to_x(box)
    gs = vsum_grad(clnear_sigma(y))
    if gs is None:
        return None
    m = _point(box)
    ym = [Iv(mi) for mi in m]
    val = vsum(clnear_sigma(ym)) - 3
    coef = [None] * 6
    for k, (ij, ji) in enumerate(CLNEAR_IDX):
        coef[k] = gs[ij] - gs[ji]
        e = y[3 + k]
        val = val + ym[3 + k].abs().scale(3)
        if e.lo >= 0:
            t = Iv(3)
        elif e.hi <= 0:
            t = Iv(-3)
        else:
            t = Iv(-3, 3)
        coef[3 + k] = gs[ij] + gs[ji] + t
    for i in range(6):
        dx = Iv(arb(box[i][0]) - arb(m[i]), arb(box[i][1]) - arb(m[i]))
        val = val + coef[i] * dx
    return val


# ---------------------------------------------------------------- hull3 -----------
H3PAIRS = ((0, 1), (0, 2), (1, 2))


def hull3_nat(box):
    t = sigma_to_x(box)
    r = Iv(-3)
    for i, j in H3PAIRS:
        h = (t[i] - t[j]).scale(0.5)
        g = (t[i] + t[j]).scale(0.5)
        C = h.cos_halfpi()
        W = (ONE + g.sin2().scale(9)).sqrt()
        r = r + C * W
    return r


def _ball(lo, hi):
    return arb(lo).union(arb(hi))


def hull3_grad_balls(box):
    t = [_ball(lo, hi) for lo, hi in box]
    g = [arb(0)] * 3
    for i, j in H3PAIRS:
        h = (t[i] - t[j]) / 2
        gg = (t[i] + t[j]) / 2
        sh, ch = h.sin_cos()
        sg, cg = gg.sin_cos()
        W = (1 + 9 * sg * sg).sqrt()
        common = ch * 9 * sg * cg / (2 * W)
        g[i] = g[i] + (-sh * W / 2 + common)
        g[j] = g[j] + (sh * W / 2 + common)
    return g


def hull3_mvf(box):
    gb = hull3_grad_balls(box)
    if not all(b.is_finite() for b in gb):
        return None
    m = _point(box)
    val = hull3_nat([(mi, mi) for mi in m])
    for i in range(3):
        G = Iv(gb[i].lower(), gb[i].upper())
        dx = Iv(arb(box[i][0]) - arb(m[i]), arb(box[i][1]) - arb(m[i]))
        val = val + G * dx
    return val
