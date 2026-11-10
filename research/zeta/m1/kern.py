"""Certified closed-form kernel (h3's explicit 5-term kernel) in ball arithmetic (python-flint / Arb).

f(u) = 2/3 + a1 cos(mu1 u) + a2 cos(mu2 u) + b1 sin(mu1 u) + b2 sin(mu2 u) on [-3/4,3/4], mu_n = 4 pi n/3,
b1 = 0.347412, b2 = -0.178443 (exact decimals), a1 = 2/3 + a2 (so that f(+-3/4) = 0 exactly), and
a2 = the root near -0.13622 of r(1) = 0 (r(1) is an exact quadratic in a2).  [h3's kernel had a1 = 0.53044, f(3/4) = -1.1e-6,
which makes r > 0 on (3/2 - 1e-6, 3/2): see single_pair.md Sec. 1.]
r = f (autocorrelation) f, K = r^ = |f^|^2, r1 = r 1_[-1,1], K1 = r1^.
Closed form (derivation in single_pair.md, Lemma 1):  for 0 <= alpha <= 3/2
   r(alpha) = sum_{k=-2..2} (P_k + Q_k alpha) e^{i mu_k alpha}.
All integrals int_0^L alpha^n e^{w alpha} d alpha are evaluated through E_n(w) = int_0^1 t^n e^{wt} dt (series + rigorous tail
for |w|<2, exact recurrence otherwise).
"""
from flint import arb, acb, ctx, fmpq
ctx.prec = 160

PI = arb.pi()
I = acb(0, 1)

def MU(n):
    return 4 * PI * n / 3

B1 = arb(fmpq(347412, 1000000)); B2 = arb(fmpq(-178443, 1000000)); C0 = arb(fmpq(2, 3))

# ---------------- E_n(w) ----------------
def E_all(w, nmax):
    """[E_0(w),...,E_nmax(w)], E_n(w)=int_0^1 t^n e^{wt} dt, w an acb (ball). Rigorous."""
    w = acb(w)
    aw = w.abs_upper()
    if aw < 2:
        out = []
        J = 40
        # tail bound: sum_{j>=J} |w|^j/j! /(j+n+1) <= |w|^J/J! * 1/(1-|w|/(J+1)) /(J+n+1)
        termJ = arb(aw) ** J / arb.fac_ui(J) / (1 - arb(aw) / (J + 1))
        for n in range(nmax + 1):
            s = acb(0); t = acb(1)
            for j in range(J):
                s += t / (j + n + 1)
                t = t * w / (j + 1)
            rad = termJ / (J + n + 1)
            s += acb(arb(0, rad.upper()), arb(0, rad.upper()))
            out.append(s)
        return out
    ew = w.exp()
    out = [(ew - 1) / w]
    for n in range(1, nmax + 1):
        out.append((ew - n * out[-1]) / w)
    return out

# ---------------- coefficients ----------------
def fourier_coeffs(a2):
    """c_n for n=-2..2 as dict."""
    a2 = arb(a2)
    A1 = C0 + a2
    return {0: acb(C0), 1: acb(A1, -B1) / 2, -1: acb(A1, B1) / 2, 2: acb(a2, -B2) / 2, -2: acb(a2, B2) / 2}

def r_coeffs(a2):
    """returns dict k -> (P_k, Q_k), r(alpha)=sum (P_k+Q_k alpha) e^{i mu_k alpha} on [0,3/2]."""
    c = fourier_coeffs(a2)
    P = {k: acb(0) for k in range(-2, 3)}; Q = {k: acb(0) for k in range(-2, 3)}
    for n in range(-2, 3):
        for m in range(-2, 3):
            j = n + m
            if j == 0:
                # c_n c_m e^{i mu_m alpha} (3/2 - alpha), m = -n
                P[m] += c[n] * c[m] * arb(1.5)
                Q[m] += -c[n] * c[m]
            else:
                coef = c[n] * c[m] * (-1) ** (j % 2) / (I * MU(j))
                # (e^{-i mu_n alpha} - e^{i mu_m alpha})
                P[-n] += coef
                P[m] += -coef
    return P, Q

def r_val(a2, alpha, deriv=0, PQ=None):
    P, Q = PQ if PQ is not None else r_coeffs(a2)
    alpha = acb(alpha)
    s = acb(0)
    for k in range(-2, 3):
        lam = I * MU(k)
        e = (lam * alpha).exp()
        # d^d/dalpha^d [(P+Q a) e^{lam a}] = (P+Q a) lam^d e + d Q lam^{d-1} e
        term = (P[k] + Q[k] * alpha) * lam ** deriv
        if deriv >= 1:
            term += deriv * Q[k] * lam ** (deriv - 1)
        s += term * e
    return s.real

def solve_a2():
    """a2 = root near -0.13623 of r(1)=0 (r(1) is a quadratic polynomial in a2; exact interpolation at -1,0,1)."""
    v = {t: r_val(arb(t), arb(1)) for t in (-1, 0, 1)}
    C = v[0]; A = (v[1] + v[-1]) / 2 - C; B = (v[1] - v[-1]) / 2
    disc = B * B - 4 * A * C
    roots = [(-B + disc.sqrt()) / (2 * A), (-B - disc.sqrt()) / (2 * A)]
    rt = [x for x in roots if abs(float(x.mid()) + 0.13622) < 1e-3]
    assert len(rt) == 1, roots
    return rt[0], (A, B, C)

A2, QUAD = solve_a2()
PQ = r_coeffs(A2)

def r(alpha, d=0):
    return r_val(A2, alpha, d, PQ)

# ---------------- generic integral ----------------
def mom(Lr, w, nmax):
    """[int_0^L a^n e^{w a} da]_{n<=nmax} for L = Lr (arb), w acb."""
    Es = E_all(w * Lr, nmax)
    return [Lr ** (n + 1) * Es[n] for n in range(nmax + 1)]

def int_r_poly_exp(L, s, polyc):
    """int_0^L r(alpha) * (sum_j polyc[j] alpha^j) * e^{s alpha} d alpha, s acb."""
    P, Q = PQ
    nmax = len(polyc)
    tot = acb(0)
    for k in range(-2, 3):
        M = mom(arb(L), I * MU(k) + s, nmax)
        for j, cj in enumerate(polyc):
            if cj == 0:
                continue
            tot += cj * (P[k] * M[j] + Q[k] * M[j + 1])
    return tot

TWO_PI = 2 * PI

def Kd(x, n=0):
    """K^{(n)}(x), x real (arb ball): 2 Re int_0^{3/2} r (2 pi i a)^n e^{2 pi i a x}."""
    poly = [acb(0)] * n + [(TWO_PI * I) ** n]
    return 2 * int_r_poly_exp(arb(1.5), TWO_PI * I * acb(x), poly).real

def Pd(x, y, a=0, b=0):
    """d_x^a d_y^b Re K1(x+iy) = Re int_0^1 r [ (2pi i al)^a (2pi al)^b e^{2pi al(ix+y)} + (2pi i al)^a(-2pi al)^b e^{2pi al(ix-y)} ]."""
    n = a + b
    cpl = (TWO_PI * I) ** a * TWO_PI ** b
    cmi = (TWO_PI * I) ** a * (-TWO_PI) ** b
    s1 = TWO_PI * (I * acb(x) + acb(y))
    s2 = TWO_PI * (I * acb(x) - acb(y))
    p1 = [acb(0)] * n + [cpl]
    p2 = [acb(0)] * n + [cmi]
    return (int_r_poly_exp(arb(1), s1, p1) + int_r_poly_exp(arb(1), s2, p2)).real

def G(x, y, a=0, b=0):
    """d_x^a d_y^b G(x,y), G = K(x) + Re K1(x+iy) - K1(x)."""
    if b == 0:
        return Kd(x, a) + Pd(x, y, a, 0) - Pd(x, arb(0), a, 0)
    return Pd(x, y, a, b)

def Delta(y):
    """K1(2iy)-K1(0)."""
    return Pd(arb(0), 2 * arb(y)) - Pd(arb(0), arb(0))

# ---------------- efficient jets ----------------
def moments_r(L, s, nmax):
    """for each k: (P_k M_j + Q_k M_{j+1})_{j<=nmax} = int_0^L r_k(a) a^j e^{s a}, summed over k -> list over j."""
    P, Q = PQ
    out = [acb(0)] * (nmax + 1)
    for k in range(-2, 3):
        M = mom(arb(L), I * MU(k) + s, nmax + 1)
        for j in range(nmax + 1):
            out[j] += P[k] * M[j] + Q[k] * M[j + 1]
    return out   # out[j] = int_0^L r(a) a^j e^{s a} da

def Gjet(x, y):
    """returns dict with G, Gx, Gy, Gxx, Gxy, Gyy at (x,y) (balls allowed). Uses 4 moment sets."""
    x = acb(x); y = acb(y)
    tp = TWO_PI
    mK = moments_r(1.5, tp * I * x, 2)
    m0 = moments_r(1, tp * I * x, 2)
    mp_ = moments_r(1, tp * (I * x + y), 2)
    mm = moments_r(1, tp * (I * x - y), 2)
    iw = tp * I
    # K^{(a)} = 2 Re (2 pi i)^a mK[a];  P_{a,b}(x,y) = Re[(2pi i)^a (2pi)^b (mp[a+b] + (-1)^b mm[a+b])]
    Kd_ = [2 * (iw ** a * mK[a]).real for a in range(3)]
    def Pab(a, b):
        return (iw ** a * tp ** b * (mp_[a + b] + (-1) ** b * mm[a + b])).real
    def P0(a):
        return (iw ** a * 2 * m0[a]).real
    return dict(G=Kd_[0] + Pab(0, 0) - P0(0), Gx=Kd_[1] + Pab(1, 0) - P0(1), Gy=Pab(0, 1),
                Gxx=Kd_[2] + Pab(2, 0) - P0(2), Gxy=Pab(1, 1), Gyy=Pab(0, 2), K=Kd_[0], K1=P0(0), K1xx=P0(2))

def Kjet(x, n=4):
    """[K^{(j)}(x)]_{j<=n}, [K1^{(j)}(x)]_{j<=n} for real x (ball allowed)."""
    x = acb(x)
    s = TWO_PI * I * x
    mK = moments_r(1.5, s, n)
    m0 = moments_r(1, s, n)
    iw = TWO_PI * I
    return [2 * (iw ** a * mK[a]).real for a in range(n + 1)], [2 * (iw ** a * m0[a]).real for a in range(n + 1)]

def ballx(lo, hi):
    lo = arb(lo); hi = arb(hi)
    return (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())

# ---------------- high-order Taylor data ----------------
from math import comb, factorial
def Gderivs(x, y, n):
    """D[(a,b)] = d_x^a d_y^b G(x,y) for a+b<=n, at a point (x,y) (balls allowed)."""
    x = acb(x); y = acb(y); tp = TWO_PI; iw = tp * I
    mK = moments_r(1.5, iw * x, n)
    m0 = moments_r(1, iw * x, n)
    mp_ = moments_r(1, tp * (I * x + y), n)
    mm = moments_r(1, tp * (I * x - y), n)
    D = {}
    for a in range(n + 1):
        Kterm = 2 * (iw ** a * (mK[a] - m0[a])).real
        for b in range(n + 1 - a):
            v = (iw ** a * tp ** b * (mp_[a + b] + (-1) ** b * mm[a + b])).real
            D[(a, b)] = v + (Kterm if b == 0 else 0)
    return D

MOM1 = moments_r(1, acb(0), 40)      # int_0^1 r a^n
MOM15 = moments_r(1.5, acb(0), 40)   # int_0^{3/2} r a^n
def absmom_K(n):
    """int_{-3/2}^{3/2} |r| |a|^n  (r>=0 on [0,1], r<=0 on [1,3/2])."""
    return 2 * (2 * MOM1[n].real - MOM15[n].real)
def coshmom(n, y):
    """int_{-1}^{1} r |a|^n cosh(2 pi a y)  (r1>=0)."""
    y = arb(y)
    mp1 = moments_r(1, acb(TWO_PI * y), n); mm1 = moments_r(1, acb(-TWO_PI * y), n)
    return (mp1[n] + mm1[n]).real
def crudeG(a, b, ymax):
    """upper bound for sup_{x real, 0<=y<=ymax} |d_x^a d_y^b G(x,y)|."""
    tp = TWO_PI
    m = a + b
    c = coshmom(m, ymax)
    if b == 0:
        return tp ** m * (absmom_K(m) + c + 2 * MOM1[m].real)
    return tp ** m * c
