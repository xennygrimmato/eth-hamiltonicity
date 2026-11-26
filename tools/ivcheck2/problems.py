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


# ---------------------------------------------------------------- k2 (K_{2,3} refined bracket) ------
# Written from research/ports/k2m/notes.md §5.2/§5.4 ("Certificate spec"), not from ivcert.
#   vertex (u, v): Q = u + v, W = (c_u + c_v)^2 + Q^2,
#     C(u, v) = 1/2 sqrt(tau^2 (c_u + c_v)^2 + (u - v)^2) + (lam/2)|Q|,
#     N(u, v) = 1 if 2|Q| >= lam W, C(u, v) otherwise  (C <= N everywhere)
#   E = sum_{i<j} |s_ij + s_ji|,  X = |Q1| + |Q2| + |Q3| - E,  Br' = N1 + N2 + N3 - (lam/2) X - eta.
#   F'_1 = {Q1 <= 0, Q2 >= 0, Q3 >= 0, 2|Q1| <= lam W1, 2 Q2 <= lam W2}.
# A certificate `k2far|k2near:lam=P/Q:eta=P/Q:case=c|l:s=...` claims Br' >= bound on the piece
#   F'_1 ∩ {2 Q3 <= lam W3 (case c) | 2 Q3 >= lam W3 (case l)} ∩ {s_k eps_k >= 0 (k = 12, 13, 23)}.
# On the piece the signs of Q1, Q2, Q3, eps_k are fixed, N1 = C1 and N2 = C2 (vertices 1, 2 curved;
# on the boundary 2|Q| = lam W both formulas give 1), and N3 >= C3 (case c) / N3 = 1 (case l).
# So on the piece Br' >= G(sigma) with
#   G = C1' + C2' + N3' - (lam/2)(-Q1 + Q2 + Q3 - sum_k s_k eps_k) - eta,
#   C1' = V1 - (lam/2) Q1, C2' = V2 + (lam/2) Q2, N3' = V3 + (lam/2) Q3 (case c) or 1 (case l),
#   V_i = 1/2 sqrt(tau^2 (c+c')^2 + (u - v)^2).
# G is smooth where every c > 0; it is evaluated as written (no algebraic cancellation).
# (Only N >= C is used for N1, N2, N3 in case c; this holds everywhere since N = C or N = 1 >= C.)
# Scaling and coordinates (the meaning of the certificate, see ivcert-notes.md): the certified claim is
#   M * Br' >= bound,  M = lcm(den lam, den eta);
# k2far boxes are sigma boxes in [-1,1]^6; k2near boxes are (a12, a13, a23, t12, t13, t23) boxes with
#   e_k = s_k t_k^2, sigma_ij = a_k + e_k, sigma_ji = e_k - a_k, a in [-R,R]^3, t in [0,T]^3, R = T^2.
# Here every box is mapped to an (a, e) box (resp. kept as a sigma box) and G is bounded on that box.
K2VERTS = VERTS   # 1 -> (s12, s13), 2 -> (s21, s23), 3 -> (s31, s32)
K2PAIRS = PAIRS   # eps12 = s12 + s21, eps13 = s13 + s31, eps23 = s23 + s32


def _rat(txt):
    p, q = txt.split("/")
    return int(p), int(q)


class K2Spec:
    def __init__(self, name):
        parts = name.split(":")
        self.base = parts[0]
        assert self.base in ("k2far", "k2near")
        kv = dict(p.split("=", 1) for p in parts[1:])
        self.lam_pq = _rat(kv["lam"])
        self.eta_pq = _rat(kv["eta"])
        lp, lq = self.lam_pq
        ep, eq = self.eta_pq
        self.lam = Iv(arb(lp) / arb(lq))   # Iv of a ball: outward endpoints
        self.tau2 = Iv(arb(lq * lq - lp * lp) / arb(lq * lq))
        self.eta = Iv(arb(ep) / arb(eq))
        self.hl = Iv(arb(lp) / arb(2 * lq))  # lam / 2
        self.case = kv["case"]
        assert self.case in ("c", "l")
        self.s = [1 if ch == "+" else -1 for ch in kv["s"]]
        assert len(self.s) == 3
        self.near = self.base == "k2near"
        if self.near:
            self.T = float(kv["t"])
            self.rho = self.T * self.T
            assert arb(self.T) * arb(self.T) == arb(self.rho) and self.rho <= 0.5
        else:
            self.rho = float(kv.get("rho", "0"))
        from math import gcd
        self.M = lq * eq // gcd(lq, eq)
        self.bound = float(kv.get("c", "0"))
        self.shift = 0.0  # mutation tests only: prove G - shift >= bound

    def sigma(self, y):
        if not self.near:
            return list(y)
        return clnear_sigma(y)  # same (a, e) convention: s_ij = a + e, s_ji = e - a

    def constraints(self, s):
        """Enclosures of the defining quantities g >= 0 of the piece."""
        c = [cfun(u) for u in s]
        Q = [s[p] + s[q] for p, q in K2VERTS]
        W = [(c[p] + c[q]).sqr() + Q[i].sqr() for i, (p, q) in enumerate(K2VERTS)]
        g = [-Q[0], Q[1], Q[2], self.lam * W[0] - Q[0].abs().scale(2), self.lam * W[1] - Q[1].scale(2)]
        g3 = self.lam * W[2] - Q[2].scale(2)
        g.append(g3 if self.case == "c" else -g3)
        for k, (p, q) in enumerate(K2PAIRS):
            g.append((s[p] + s[q]).scale(self.s[k]))
        return g

    def coords(self, box):
        """Iv box in the coordinates G is written in: sigma (k2far) or (a, e) (k2near)."""
        y = sigma_to_x(box)
        if self.near:
            for k in range(3):
                assert box[3 + k][0] >= 0
                y[3 + k] = y[3 + k].sqr().scale(self.s[k])
        return y

    def misses(self, box):
        """True if the box certainly misses the piece (some g < 0 on the whole box)."""
        g = self.constraints(self.sigma(self.coords(box)))
        return any(x.hi < 0 for x in g)

    def G(self, s):
        c = [cfun(u) for u in s]
        V = [((c[p] + c[q]).sqr() * self.tau2 + (s[p] - s[q]).sqr()).sqrt().scale(0.5) for p, q in K2VERTS]
        Q = [s[p] + s[q] for p, q in K2VERTS]
        C1 = V[0] - self.hl * Q[0]
        C2 = V[1] + self.hl * Q[1]
        N3 = V[2] + self.hl * Q[2] if self.case == "c" else Iv(1)
        E = Iv(0)
        for k, (p, q) in enumerate(K2PAIRS):
            E = E + (s[p] + s[q]).scale(self.s[k])
        X = -Q[0] + Q[1] + Q[2] - E
        return (C1 + C2 + N3 - self.hl * X - self.eta - self.shift).scale(self.M) - self.bound

    def _linear_part(self):
        """Exact rational coefficients of the linear terms of G (collected from the formula of G term by
        term) and its constant; the V terms are kept.  G_fast below is G with these terms collected,
        which avoids the dependency loss of evaluating +-(lam/2)Q twice; selftest_k2 checks
        G_fast = G = M Br' at points."""
        if hasattr(self, "_lin"):
            return self._lin
        from fractions import Fraction as Fr
        hl = Fr(self.lam_pq[0], 2 * self.lam_pq[1])
        coef = [Fr(0)] * 6
        def addQ(i, w):
            for idx in K2VERTS[i]:
                coef[idx] += w
        addQ(0, -hl)                    # C1' = V1 - (lam/2) Q1
        addQ(1, hl)                     # C2' = V2 + (lam/2) Q2
        if self.case == "c":
            addQ(2, hl)                 # N3' = V3 + (lam/2) Q3
        const = Fr(-self.eta_pq[0], self.eta_pq[1]) + (1 if self.case == "l" else 0)
        # -(lam/2) X, X = -Q1 + Q2 + Q3 - sum_k s_k eps_k
        addQ(0, hl)
        addQ(1, -hl)
        addQ(2, -hl)
        for k, (p, q) in enumerate(K2PAIRS):
            coef[p] += hl * self.s[k]
            coef[q] += hl * self.s[k]
        self._lin = ([Iv(arb(c.numerator) / arb(c.denominator)) for c in coef],
                     Iv(arb(const.numerator) / arb(const.denominator)))
        return self._lin

    def G_fast(self, s):
        coef, const = self._linear_part()
        c = [cfun(u) for u in s]
        r = const - self.shift
        for i, (p, q) in enumerate(K2VERTS):
            if i == 2 and self.case == "l":
                continue
            r = r + ((c[p] + c[q]).sqr() * self.tau2 + (s[p] - s[q]).sqr()).sqrt().scale(0.5)
        for i in range(6):
            if coef[i].lo != 0 or coef[i].hi != 0:
                r = r + coef[i] * s[i]
        return r.scale(self.M) - self.bound

    def gradG_sigma(self, s):
        """Interval gradient of G in sigma over the box, or None if some c or root may vanish."""
        g = [Iv(0)] * 6
        for i, (p, q) in enumerate(K2VERTS):
            if i == 2 and self.case == "l":
                continue  # N3' = 1
            u, v = s[p], s[q]
            cu, cv = cfun(u), cfun(v)
            if not (cu.lo > 0 and cv.lo > 0):
                return None
            S = cu + cv
            R = S.sqr() * self.tau2 + (u - v).sqr()
            if not (R.lo > 0):
                return None
            inv = R.sqrt().scale(2).recip_pos()
            D = u - v
            g[p] = g[p] + (S * self.tau2 * (-u / cu) + D) * inv
            g[q] = g[q] + (S * self.tau2 * (-v / cv) - D) * inv
        # linear parts: C1' -(lam/2)Q1, C2' +(lam/2)Q2, N3' +(lam/2)Q3 (case c);
        # -(lam/2)X = (lam/2)Q1 - (lam/2)Q2 - (lam/2)Q3 + (lam/2) sum s_k eps_k
        lin = [Iv(0)] * 6
        hl = self.hl
        for idx in K2VERTS[0]:
            lin[idx] = lin[idx] - hl + hl
        for idx in K2VERTS[1]:
            lin[idx] = lin[idx] + hl - hl
        for idx in K2VERTS[2]:
            lin[idx] = lin[idx] + (hl if self.case == "c" else Iv(0)) - hl
        for k, (p, q) in enumerate(K2PAIRS):
            lin[p] = lin[p] + hl.scale(self.s[k])
            lin[q] = lin[q] + hl.scale(self.s[k])
        return [g[i] + lin[i] for i in range(6)]

    def grad(self, y):
        """Gradient in the certificate's coordinates."""
        gs = self.gradG_sigma(self.sigma(y))
        if gs is None or not self.near:
            return gs
        out = [None] * 6
        for k, (ij, ji) in enumerate(CLNEAR_IDX):
            out[k] = gs[ij] - gs[ji]          # d/da_k
            out[3 + k] = gs[ij] + gs[ji]      # d/de_k
        return out

    def nat(self, box):
        return self.G_fast(self.sigma(self.coords(box)))

    def mvf(self, box):
        y = self.coords(box)
        g = self.grad(y)
        if g is None:
            return None
        m = []
        for yi in y:   # a point of the box: the midpoint if Arb computes it exactly, else the lower end
            mi = (yi.lo + yi.hi) / 2
            m.append(mi if (mi.rad() == 0 and yi.lo <= mi <= yi.hi) else yi.lo)
        val = self.G_fast(self.sigma([Iv(mi) for mi in m]))
        for i in range(6):   # G_fast is M * (...), the gradient is that of (...): scale it by M
            val = val + g[i].scale(self.M) * Iv(y[i].lo - m[i], y[i].hi - m[i])
        return val

    def ae_box_in(self, box, r):
        y = self.coords(box)
        return all(yi.lo >= -r and yi.hi <= r for yi in y)
