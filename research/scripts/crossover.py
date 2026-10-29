#!/usr/bin/env python3
"""crossover.py -- where do the ETH-refutation #SAT algorithms (Anthropic, OpenAI) and our exact #HC
algorithm first beat brute force?  Run:  python3 -I crossover.py  (writes crossover.out beside it).

All quantities are PROVEN upper bounds on log2(time) as written in the sources (paths in crossover.md),
evaluated with mpmath (60 digits) in the log domain; K_l = 2^(L_l) is never materialised as an integer.
Rate := log2(T_alg)/n.  Brute force: 2^n for #3-SAT, n^2 2^n for #HC (Held-Karp).  Crossover n* = least n
with T_alg < T_brute.  We report t* = log2 n* (and log2 t*).

Tiers:  A = as written (Lean / paper parameters);  B = same proven lemmas, free parameters re-optimised;
        C = justified constant changes outside the proofs (labelled heuristic where they rest on our notes).
Existential constants (C0, C1, C2, the TM polynomial degree q, OpenAI's poly degrees) are parameters;
setting them to 0 (q to 1) gives the explicit-part lower bound on n*.
"""
import sys, os, math
import mpmath as mp
from mpmath import mpf

mp.mp.dps = 60
TWO = mpf(2)
LN2 = mp.log(2)
RHO = 1 / mp.sqrt(2)
OUT = []

def P(*a):
    s = ' '.join(str(x) for x in a)
    OUT.append(s); print(s)

def lg(x): return mp.log(x, 2)
def size(x):                      # Lean Nat.size of floor(x): bit length
    x = mp.floor(x)
    return mpf(0) if x < 1 else mp.floor(lg(x)) + 1
def clog2(x):                     # Nat.clog 2 (ceil x)
    x = mp.ceil(x)
    return mpf(0) if x <= 1 else mp.ceil(lg(x) - mpf(10) ** -40)
def H2(x):
    if x <= 0 or x >= 1: return mpf(0)
    return -x * lg(x) - (1 - x) * lg(1 - x)
def f(x, d=4): return mp.nstr(x, d)

# ----------------------------------------------------------------------------------------------------
# 1. Anthropic schedule  (proof/statements/LevelsStatement.lean, Levels.Gen.K/g/zeta/e)
# ----------------------------------------------------------------------------------------------------
class Sched:
    """L[l] = log2 K_l (exact ints), a[l] = log2(g_l/K_l), e[l] = e_l, zeta[l]."""
    def __init__(self, x0=18, e0=mpf(1) / 2, zeta=None, gk='lean', nlev=48, name='lean'):
        self.name, self.x0 = name, x0
        zeta = zeta or (lambda l: TWO ** (-(l + 5)))
        L, e, a, z = [x0], [mpf(e0)], [], []
        for l in range(nlev):
            zl = zeta(l); z.append(zl)
            if gk == 'lean':
                al = 3 * l + x0
            else:                       # least a with case_ii:  K ln(2gK) <= 2 zeta^2 g,  g = 2^a K
                al = 1
                while (1 + al + 2 * L[-1]) * LN2 > 2 * zl ** 2 * TWO ** al: al += 1
            a.append(al)
            e.append((RHO + 3 * zl) * e[-1] + 3 * TWO ** (-L[-1]))
            L.append(2 * (L[-1] + al))
        self.L, self.e, self.a, self.zeta = L, e, a, z

LEAN = Sched()
for l in range(40):                 # PartA.logK closed form and PartA.case_ii, checked
    assert LEAN.L[l] == (3 * 18 + 6) * 2 ** l - 6 * l - 2 * 18 - 6
    assert (1 + LEAN.a[l] + 2 * LEAN.L[l]) * LN2 <= 2 * LEAN.zeta[l] ** 2 * TWO ** LEAN.a[l]

def frac_half(l):                   # rates/GeneralPieces/Num/Between.lean: num/den, the e' of CountedRoute
    return mpf(5 + 2 * (l % 2)) / (5 * TWO ** ((l + 1) // 2))

# ----------------------------------------------------------------------------------------------------
# 2. Anthropic m-route: rates/ClauseBound/Alg/Top.lean (PtopK, lamTopK, needTop) with the solver exponent
#    CountedRoute: needOf = ceil(e' K^2 lam) + C0 K^2 size(K(lam+B+1)) + 2 (rates/CountedToPadded/Defs.lean)
#    pieces route: Seq.rate  e K^2 lam + C0 K^2 log2(K(lam+B))      (rates/ClauseBound/Alg/Interfaces.lean)
# ----------------------------------------------------------------------------------------------------
def anth_m_terms(L, e, k, m, C0=0, route='counted', no_search=False):
    K = TWO ** L; g = 3 * K ** 8
    Pt = max(mpf(1), 2 * k * mp.ceil(m / g))
    lam = mp.floor((K ** 3 + K * (2 * k * m) + g * Pt) / K ** 3)
    tg = 6 * K ** 7                                   # (2g)/K, exact since K = 2^L
    B = Pt * tg
    t_search = mpf(0) if no_search else 3 * K ** 8 * (L + 1)   # 3K^8 * size K  (K^g grouping search)
    t_P = Pt * (tg + 1)
    t_tab = (K - 1) * lam
    if route == 'counted':
        t_S = mp.ceil(e * K ** 2 * lam) + C0 * K ** 2 * size(K * (lam + B + 1)) + 2
    else:
        t_S = e * K ** 2 * lam + C0 * K ** 2 * lg(K * (lam + B))
    return {'search': t_search, 'P(2g/K+1)': t_P, '(K-1)lam': t_tab, 'solver': t_S}

def anth_m_rate(t, alpha, sch, l, k=3, C0=0, route='counted', ekind='half', no_search=False):
    n = TWO ** t; m = alpha * n
    e = frac_half(l) if ekind == 'half' else sch.e[l]
    T = anth_m_terms(sch.L[l], e, k, m, C0, route, no_search)
    return max(T.values()) / n, T

def level_root(sch, logx, d):        # largest l with K_l^d <= x  (root9 / root17 / K^30 <= n); l = 0 if none
    l = 0
    while l + 1 < len(sch.L) and d * sch.L[l + 1] <= logx: l += 1
    return l

def bisect_t(fun, lo, hi, it=120):   # least t in [lo,hi] with fun(t) True, fun monotone False->True
    lo, hi = mpf(lo), mpf(hi)
    if not fun(hi): return None
    if fun(lo): return lo
    for _ in range(it):
        mid = (lo + hi) / 2
        if fun(mid): hi = mid
        else: lo = mid
        if hi - lo < mpf(10) ** -6 * max(1, abs(hi)): break
    return hi

def banded_cross(rate_at, band_start, nl, thr):
    """rate_at(t) uses the as-written level rule; bands [band_start(l), band_start(l+1)).
    Within a band the rate decreases in t; returns least t with rate < thr."""
    for l in range(nl - 1):
        a, b = band_start(l), band_start(l + 1)
        if b <= a: continue
        end = b - mpf(10) ** -30 * max(1, abs(b))
        if rate_at(end) < thr:
            r = bisect_t(lambda t: rate_at(t) < thr, a, end)
            return r, l
    return None, None

def free_cross(rate_l, Ls, thr, span):
    """Tier B/C: any level; returns (t*, l*) minimising the least t with rate_l(l, t) < thr.
    A level whose rate at the current best t is already >= thr cannot cross earlier (rate decreases in t)."""
    best = (None, None)
    for l, L in enumerate(Ls):
        if best[0] is not None and not (rate_l(l, best[0]) < thr): continue
        hi = span * L + 600
        r = bisect_t(lambda t: rate_l(l, t) < thr, 1, hi)
        if r is not None and (best[0] is None or r < best[0]): best = (r, l)
    return best

def best_over(scheds, fn):
    """fn(sched) -> (t, l); returns (t, l, name) with least t."""
    best = (None, None, None)
    for nm, s in scheds:
        t, l = fn(s)
        if t is not None and (best[0] is None or t < best[0]): best = (t, l, nm)
    return best

# ----------------------------------------------------------------------------------------------------
# 3. Anthropic n-route: variables/RecursionToBound/Defs.lean (needAt, needOutputs, needWalk, root17),
#    variables/VariableBound/Net/Defs.lean (UbD, PbD, BbD, nPrMax), rates/ClauseBound/Alg/TopNet.lean
#    (lamS, bitsS, needNet), sparsification/SparsificationLemma/Cal/Defs.lean (alphaC, betaC, thetaC).
# ----------------------------------------------------------------------------------------------------
def anth_n_terms(L, enum, eps, n, C0=0, k=3):
    K = TWO ** L; g = 3 * K ** 8
    xC = 32 * (k - 1) ** 2 / eps
    logC = clog2(mp.ceil(xC))
    alpha = mp.ceil(2 * (k - 1) ** 2 / eps * logC)
    beta = [mpf(0), mpf(2)]
    for c in range(2, k):
        beta.append(sum(4 * alpha * beta[c - h] * beta[h] for h in range(1, c)))
    theta = [mpf(2)] + [alpha * beta[c] for c in range(1, k)]
    occ = 2 * sum(theta) + 2
    Dl = min(occ, n + 1)
    LD = clog2(2 * Dl)
    Ub = 6 * k * (n + LD) + 28 * k * n * clog2(96 * Dl * LD) + 2 * g ** 2
    tb = clog2(Dl * n) + 33 * LD + 1
    sb = 32 * Dl * LD
    P0 = mp.ceil(n / g) * (1 + Dl * (tb + 3)) + mp.ceil(10 * n / g) * sb
    Pb = mp.ceil(2 * P0)
    Bb = (k + 1) * 14 * n + 1
    lamS = mp.floor((K ** 3 + K * Ub + g * Pb) / K ** 3)
    tg = 6 * K ** 7
    bitsS = Pb * tg + Bb * (tg + tg ** 2) * K
    needS = mp.ceil(enum * K ** 2 * lamS) + C0 * K ** 2 * size(K * (lamS + bitsS + 1)) + 2
    objMax = 10 * n * sb + Dl * n
    s_npr = mp.floor(2 * g ** 2 * lg(objMax + 1)) + 1
    extra = size(8 * (10 * n + 1) * (sb + 1) * (size(Dl * n) + 2) + 8)
    tau_sp = 32 * alpha
    inl = (k * 2 ** k + 1) * (n + 2) ** (k + 1)
    stack = (tau_sp ** (2 * k) * n + 1) * (2 ** k * inl * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n + 16
    walk = mp.ceil(eps * n) + 2 + size(stack)
    T = {'search': 3 * K ** 8 * (L + 1), 'P(2g/K+1)': Pb * (tg + 1), '(K-1)lam': (K - 1) * lamS,
         'solver': needS, 'profiles+checks': s_npr + extra, 'walk(eps n)': walk}
    expo = max(T['search'], T['P(2g/K+1)'], T['(K-1)lam'], T['solver']) + s_npr + extra + walk
    return expo, T, dict(Delta=Dl, U_over_n=Ub / n, alpha=alpha)

def anth_n_rate(t, sch, l, C0=0, ekind='half', epsmul=None, nummul=1):
    n = TWO ** t
    e = frac_half(l) if ekind == 'half' else sch.e[l]
    num = min(e * nummul, mpf(1))
    eps = num if epsmul is None else min(e * epsmul, mpf(1))
    expo, T, aux = anth_n_terms(sch.L[l], num, eps, n, C0)
    return expo / n, T, aux

# ----------------------------------------------------------------------------------------------------
# 4. #HC: research/exact-hc-theorem.md (6.1)-(6.2) and research/hc-degree-theorem.md Prop. 3.2 / §4.1
# ----------------------------------------------------------------------------------------------------
def hc_terms(L, e, n, Dlt, C0=0, C1=0, C2=0, net='hc'):
    K = TWO ** L; g = 3 * K ** 8; m = Dlt * n / 2; ln = lg(n)
    if net == 'hc':
        gP = mpf('2.33') * (2 * m + n) + 3 * g ** 3; Pn = gP / g
        U = mpf('4.65') * m + g ** 3
        B = 2 * (2 * m + n) / g + 5
        ltau = mpf('1.5') * (2 * m + n) / g + 3 + C2 * ln
        Lc = gP + 1; Bp = 2 * gP + 1 + g ** 2 * B
        Theta = max(mpf(2), mp.ceil(n / g))
        extra = 4 * m / Theta * ln                     # log2 #branches, Lemma 6.1
    else:
        lamD = lg(2 * mp.e * Dlt)
        U = 2 * n * lg(2 * mp.e * Dlt) + g ** 3        # d-bar = Delta for Delta-regular
        Lam = (2 * n / g + 2) * lamD
        gP = 2 * (n + g) * lamD + 3 * g ** 3; Pn = gP / g
        B = Lam + 2
        ltau = Lam + C2 * ln
        Lc = U + gP + 1; Bp = 2 * gP / K + 1 + g ** 2 * B
        nu = n / g + 1
        extra = g * (g - 1) / 2 * lg(2 * nu + 1)       # log2 #profiles, Lemma 3.3
    inner = e * (U + gP / K + K ** 2) + C0 * K ** 2 * lg(K * (Lc + Bp)) + 2 * gP / K + ltau
    X = 1 + max(g * L, inner) + C1 * lg(g * (Pn + B)) + C2 * ln + extra
    T = {'gL(search)': g * L, 'eU': e * U, 'e gP/K + 2gP/K': (e + 2) * gP / K, 'log tau': ltau,
         'C0 K^2 log': C0 * K ** 2 * lg(K * (Lc + Bp)), 'branches/profiles': extra}
    return X, T

def hc_excess(t, sch, l, Dlt, net='hc', C0=0, C1=0, C2=0):
    n = TWO ** t
    X, T = hc_terms(sch.L[l], sch.e[l], n, Dlt, C0, C1, C2, net)
    return (X - 2 * lg(n)) / n, T                       # < 1  <=>  beats n^2 2^n

# ----------------------------------------------------------------------------------------------------
# 5. OpenAI Engine I (interpolation route, prop:interpolation-bound) -- main_full_version.tex
# ----------------------------------------------------------------------------------------------------
def sparsify_params(s, k=3):        # app:sparsify "The size of the tree": M, C, Gamma, B
    Gam = 2 * (3 ** (k - 1) - 1)
    M = 1
    while M < Gam: M *= 2
    while True:
        C = 4 * sum((3 * M) ** j for j in range(k - 1))
        h = math.ceil(math.log2(4 * C * M))
        if Gam * h * s <= M: break
        M *= 2
    B = 2 * sum(M ** j for j in range(k))
    return M, C, B

def taylor_log2(q, n):               # log2 C_q,  C_q = sum_{s<=q} 2^s C(n,s)  (rigorous upper bound)
    if q <= 0: return mpf(0)
    if q >= 2 * n / 3: return n * lg(3)
    x = q / n
    return q + n * H2(x) + lg(q + 1)

def oai_engineI(lam, k=3, mtest=None, tier='A', r=None, Q=None, R=None, ssp=None, tfac=None, verbose=False):
    """log2(time)/n for Engine I on n = 2^lam variables; returns (rate, terms, ok, why)."""
    lam = int(lam); n = TWO ** lam
    nu = math.ceil(math.log2(lam)) if lam > 1 else 1
    s = math.isqrt(lam // nu ** 4) if nu ** 4 <= lam else 0
    while (s + 1) ** 2 * nu ** 4 <= lam: s += 1
    while s > 0 and s * s * nu ** 4 > lam: s -= 1
    if ssp is None: ssp = s
    if ssp < 2: return mpf(1), {}, False, 's<2: exhaustive search'
    Msp, Csp, Bocc = sparsify_params(ssp, k)
    terms = {}
    terms['leaves 1/s'] = (2 * lg(Csp * n + 1) + n / ssp) / n
    mleaf = Bocc * n
    mu = mp.floor(lg(mleaf)) + 1
    Ph = 20000 * mpf(Bocc) ** 2 * mu ** 2
    D0 = 320000 * mpf(Bocc) ** 2 * mu ** 3
    calls = lg(3 * n) + Ph * lg(2 * mleaf) + 1
    dG = min(mleaf, D0); cG = mp.ceil(dG / (8 * Bocc)); qG = 2 * mleaf / dG
    tanner = dG * lg(qG) + cG * dG + lg(dG) * 10
    terms['polylog (Tanner, calls)'] = (calls + tanner) / n
    sq = math.isqrt(lam); sq = sq if sq * sq == lam else sq + 1          # ceil sqrt(lam)
    if tfac is None: tfac = sq
    Minc = 18 * D0 + 1
    b = Minc * tfac; w = 3 * D0
    terms['branches 1/t'] = (n / tfac) / n
    nprime = n * (1 - mpf(1) / tfac)
    lamp = lam
    nup = nu
    if mtest is None: mtest = 6 * n
    if tier == 'A':
        beta = max(1, int(mp.ceil(lg(b) / lg(lamp) - mpf(10) ** -30)), int(mp.ceil(lg(w) / lg(lamp) - mpf(10) ** -30)))
        r = s if True else None
        r = math.isqrt(lamp // nup ** 4) if nup ** 4 <= lamp else 0
        while (r + 1) ** 2 * nup ** 4 <= lamp: r += 1
        while r > 0 and r * r * nup ** 4 > lamp: r -= 1
        Q = lamp // (128 * nup)
        R = (beta + 3) * sq
        tau = mpf(1) / (r * lamp)
        if r < 2 or Q <= R: return mpf(1), terms, False, 'r<2 or Q<=R: exhaustive search'
        why = []
        if R < 32: why.append('R<32')
        if 6 * R > Q: why.append('6R>Q')
        log2D = 2 * Q * lg(r)
        if lg(2 * (b + w)) + 2 * log2D > lg(nprime): why.append('2(b+w)D^2>M')
        if lg(2 * Q * r * r) > lg(nprime): why.append('2Qr^2>n')
        if 2 * mp.exp(-mpf(R) ** 2 / (8 * Q)) > 1 / (b * r * r * lamp): why.append('tail')
        if why: return mpf(1), terms, False, ','.join(why) + ': exhaustive search'
        extra = dict(beta=beta, r=r, Q=Q, R=R)
    else:
        log2D = 2 * Q * lg(r)
        tail = binom_tail_kl(Q, (r - 1) / (2 * r), R)
        tau = r * b * tail
        why = []
        if not (r >= 2 and 1 <= R < Q and tau <= mpf(1) / 2): why.append('ranges')
        if lg(2 * (b + w)) + 2 * log2D > lg(nprime): why.append('2(b+w)D^2>M')
        if lg(2 * Q * r * r) > lg(nprime): why.append('2Qr^2>n')
        if why: return mpf(1), terms, False, ','.join(why)
        extra = dict(r=r, Q=Q, R=R, ssp=ssp, t=tfac, tau=tau)
    dH = k * R * (mtest + 2 * n)
    q = mp.floor(dH / Q)
    terms['Taylor log2 C_q'] = taylor_log2(q, n) / n
    terms['measurements'] = 2 * tau * n * lg(2 * TWO ** log2D + 1) / n
    terms['group 2/r'] = (2 * n / r) / n
    terms['2Qr, interp.'] = lg(2 * Q * r) / n
    rate = sum(terms.values())
    extra['q/n'] = q / n
    return rate, terms, True, extra

def binom_tail_kl(Q, p, R):          # Chernoff-KL upper bound on Pr[W not in centered window of R ints]
    Q = mpf(Q); mu_ = Q * p
    A0 = mp.floor(mu_ - (mpf(R) - 1) / 2)
    lo, hi = A0 - 1, A0 + R                          # W <= lo  or  W >= hi
    def kl(a): return a * mp.log(a / p) + (1 - a) * mp.log((1 - a) / (1 - p))
    t = mpf(0)
    if lo >= 0: t += mp.exp(-Q * kl(lo / Q)) if lo / Q < p else 1
    if hi <= Q: t += mp.exp(-Q * kl(hi / Q)) if hi / Q > p else 1
    return min(t, mpf(1))

# fast float model for the tier B/C optimiser (verified afterwards with oai_engineI in mpmath)
def _H2f(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)
def _klf(a, p): return a * math.log(a / p) + (1 - a) * math.log((1 - a) / (1 - p))
def _oai_inner(lam, ssp, lt, ri, mfac, k=3):
    """float model: best R for given (s, t = 2^lt, r); Q at its maximum. Returns (rate, Q, R)."""
    Msp, Csp, Bocc = sparsify_params(ssp, k)
    mu = lam + math.log2(Bocc) + 1
    lD0 = math.log2(320000) + 2 * math.log2(Bocc) + 3 * math.log2(mu)
    lw = math.log2(3) + lD0
    lb = math.log2(18) + lD0 + lt
    lbw = 1 + max(lb, lw) + 1
    lr = math.log2(ri)
    Q = int((lam - 1 - lbw) / (4 * lr))           # 2(b+w) r^(4Q) <= n/2 <= M'
    if Q < 8: return 9.0, Q, None
    p = (ri - 1) / (2 * ri)
    def cost(R):
        a0 = math.floor(Q * p - (R - 1) / 2)
        lo, hi = (a0 - 1) / Q, (a0 + R) / Q
        if lo < 0 or hi > 1: return 9.0
        l1 = -Q * _klf(lo, p) if 0 < lo < p else (0.0 if lo >= p else -1e300)
        l2 = -Q * _klf(hi, p) if p < hi < 1 else (0.0 if hi <= p else -1e300)
        ltail = max(l1, l2) + math.log(2)
        ltau = math.log(ri) + lb * math.log(2) + ltail
        if ltau > math.log(0.5): return 9.0
        meas = 2 * math.exp(ltau) * (2 * Q * lr + 1)
        x = k * R * (mfac + 2) / Q
        tay = math.log2(3) if x >= 2 / 3 else x + _H2f(x)
        return tay + meas
    sig = math.sqrt(Q * p * (1 - p))
    lo_, hi_ = max(1, int(sig)), min(Q - 1, int(2 * sig * math.sqrt(2 * (lb + 60) * math.log(2)) * 1.5) + 8)
    while hi_ - lo_ > 3:
        m1 = lo_ + (hi_ - lo_) // 3; m2 = hi_ - (hi_ - lo_) // 3
        if cost(m1) <= cost(m2): hi_ = m2
        else: lo_ = m1
    c, R = min((cost(R), R) for R in range(lo_, hi_ + 1))
    return 1.0 / ssp + 2.0 ** -lt + c + 2.0 / ri, Q, R

def oai_opt(lam, mfac=6.0, k=3):
    """min over (s, t, r, Q, R; tau minimal) of the Engine I rate (float model, coordinate descent)."""
    lam = int(lam)
    S = [2 ** i for i in range(1, 41) if 2 ** i <= lam]
    T = list(range(0, int(2 * math.log2(lam)) + 2))
    rgrid = sorted(set(int(1.07 ** i) for i in range(10, 260) if 2 <= int(1.07 ** i) <= lam))
    def ev(c): return _oai_inner(lam, c['ssp'], c['lt'], c['r'], mfac, k)[0]
    starts = [dict(ssp=S[min(len(S) - 1, i)], lt=min(T[-1], j), r=rr) for i in (3, 6, 9) for j in (6, 10, 14) for rr in (8, 64)]
    best, cur = min(((ev(c), c) for c in starts), key=lambda z: z[0])
    for _ in range(4):
        for key, grid in (('r', rgrid), ('ssp', S), ('lt', T)):
            for v in grid:
                c2 = dict(cur); c2[key] = v
                val = ev(c2)
                if val < best: best, cur = val, c2
        for v in range(max(2, cur['r'] - 40), cur['r'] + 41):     # fine integer r
            c2 = dict(cur); c2['r'] = v
            val = ev(c2)
            if val < best: best, cur = val, c2
    rate, Q, R = _oai_inner(lam, cur['ssp'], cur['lt'], cur['r'], mfac, k)
    return rate, dict(ssp=cur['ssp'], t=2 ** cur['lt'], r=cur['r'], Q=Q, R=R)

# ----------------------------------------------------------------------------------------------------
# drivers
# ----------------------------------------------------------------------------------------------------
def tt(x):   # format t* = log2 n*
    if x is None: return 'none'
    return '%s (log2 t = %s)' % (mp.nstr(x, 6), mp.nstr(lg(x), 4))

def section(s): P('\n' + '=' * 100 + '\n' + s + '\n' + '=' * 100)

def main():
    section('0. Schedules (Levels.Gen): L_l = log2 K_l, e_l, e\'_l = fractionHalf(l)')
    P('%3s %14s %10s %10s %10s %8s' % ('l', 'log2 K_l', 'e_l', "e'_l", 'e_l/rho^l', 'zeta_l'))
    for l in range(0, 14):
        P('%3d %14d %10s %10s %10s %8s' % (l, LEAN.L[l], f(LEAN.e[l]), f(frac_half(l)), f(LEAN.e[l] / RHO ** l), f(LEAN.zeta[l], 3)))
    P('limit e_l/rho^l = %s (= 0.5 * prod(1+3 zeta_j/rho)); +3/K_l contributes < 2^-17 at l=0 and is negligible after' % f(LEAN.e[30] / RHO ** 30, 6))

    # ---------------- Anthropic decision machine (PaddedDescent) ----------------
    section('1. Anthropic 3-SAT decision machine (rates/PaddedDescent): explicit floor, TM degree q')
    P('sOf n = floor(3(floor(log2 floor(log2 n)) - 911)/19);  exhaustive while s < s0K 3 = 128;  pad 2^{2^131 (n/2^s + 1)}')
    for q in [1, 2, 10, 1000]:
        smin = 132 + math.ceil(math.log2(q))     # q * 2^131 / 2^s < 1
        x = 911 + math.ceil(19 * smin / 3)
        while 3 * (x - 911) // 19 < smin: x += 1
        P('  q = %5d : rate q*2^(131-s) < 1 needs s >= %d  <=>  floor(log2 log2 n) >= %d  i.e. n >= 2^(2^%d)' % (q, smin, x, x))
    P('  (exhaustive search for all n < 2^(2^1722); ThreeSatRateStatement.lean says 2^(2^518), a weaker, true bound)')

    # ---------------- Anthropic m-route ----------------
    section('2. Anthropic #3-SAT, m-route (Theorem 1 in m), k = 3, m = alpha*n')
    P('rate = needTop/n, needTop = max(search 3K^8 size K, P(2g/K+1), (K-1)lam, solver); T <= q(|x|+2^needTop+1)^q')
    P('\n2a. table: tier A (CountedRoute, e\' = fractionHalf, level root9), alpha = 4.26, C0 = 0, at n = 2^(2^j)')
    P('%4s %12s %4s %12s %12s  %s' % ('j', 'log2 n', 'l', 'rate', 'solver/n', 'dominant'))
    for j in range(4, 31, 2):
        t = TWO ** j; m_ = lg(mpf('4.26')) + t
        l = level_root(LEAN, m_, 9)
        r, T = anth_m_rate(t, mpf('4.26'), LEAN, l)
        dom = max(T, key=lambda kk: T[kk])
        P('%4d %12s %4d %12s %12s  %s' % (j, f(t, 6), l, f(r), f(T['solver'] / TWO ** t), dom))
    res = {}
    P('\n2b. crossover t* = log2 n*  (q = TM degree; q = 1, C0 = 0 is the explicit-part lower bound)')
    P('%-58s %6s %4s %4s  %s' % ('variant', 'alpha', 'q', 'l*', 't* = log2 n*'))
    for alpha in [mpf(1), mpf(3), mpf('4.26')]:
        for q in [1, 2, 3, 5, 10]:
            for C0 in ([0, 1, 10] if q == 1 else [0]):
                thr = mpf(1) / q
                ra = lambda t: anth_m_rate(t, alpha, LEAN, level_root(LEAN, lg(alpha) + t, 9), C0=C0)[0]
                tA, lA = banded_cross(ra, lambda l: 9 * mpf(LEAN.L[l]) - lg(alpha), 40, thr)
                P('%-58s %6s %4d %4s  %s' % ('A  CountedRoute, root9, e\'=fractionHalf, C0=%d' % C0, f(alpha, 3), q, lA, tt(tA)))
                res[('mA', float(alpha), q, C0)] = (tA, lA)
            thr = mpf(1) / q
            tB, lB = free_cross(lambda l, t: anth_m_rate(t, alpha, LEAN, l, ekind='e')[0], LEAN.L[:40], thr, 9)
            P('%-58s %6s %4d %4s  %s' % ('B  same lemmas, num = e_l, level free', f(alpha, 3), q, lB, tt(tB)))
            res[('mB', float(alpha), q)] = (tB, lB)
            for nm, fam in TIERC:
                tC, lC, zn = best_over(fam, lambda sch: free_cross(lambda l, t: anth_m_rate(t, alpha, sch, l, ekind='e')[0], sch.L[:40], thr, 9))
                P('%-58s %6s %4d %4s  %s  [%s]' % (nm, f(alpha, 3), q, lC, tt(tC), zn))
                res[('mC', nm, float(alpha), q)] = (tC, lC)
            tC, lC, zn = best_over(TIERC[1][1], lambda sch: free_cross(lambda l, t: anth_m_rate(t, alpha, sch, l, ekind='e', no_search=True)[0], sch.L[:40], thr, 9))
            P('%-58s %6s %4d %4s  %s  [%s]' % ('C5 C2 + no K^g grouping search [H]', f(alpha, 3), q, lC, tt(tC), zn))
            res[('mCns', float(alpha), q)] = (tC, lC)
    # term breakdown at tier-A crossover, alpha=4.26, q=1
    tA, lA = res[('mA', 4.26, 1, 0)]
    r, T = anth_m_rate((tA + mpf(10) ** -9), mpf('4.26'), LEAN, lA)
    P('\n2c. terms / n at tier-A n* (alpha=4.26, q=1, l=%d): ' % lA + ', '.join('%s=%s' % (kk, f(v / TWO ** (tA + mpf(10) ** -9), 5)) for kk, v in T.items()))
    K = TWO ** LEAN.L[lA]; n = TWO ** (tA + mpf(10) ** -9)
    c0max = (1 - r) / (K ** 2 * size(K * 1e6 * n) / n)
    P('    C0 would have to exceed 2^%s to move n* (C0 enters only as C0 K^2 size(...)/n)' % f(lg(c0max), 6))

    # ---------------- Anthropic n-route ----------------
    section('3. Anthropic #3-SAT, n-route (Theorem D(b): any m), k = 3')
    P('expo = needOutputs (Delta = min(occBound, n+1)) + needWalk;  level root17 (K_l^17 <= n)')
    P('%4s %12s %4s %12s %12s %12s %10s' % ('j', 'log2 n', 'l', 'rate', 'solver/n', 'walk/n', 'U/n'))
    for j in range(4, 41, 3):
        t = TWO ** j; l = level_root(LEAN, t, 17)
        r, T, aux = anth_n_rate(t, LEAN, l)
        n = TWO ** t
        P('%4d %12s %4d %12s %12s %12s %10s' % (j, f(t, 6), l, f(r), f(T['solver'] / n), f(T['walk(eps n)'] / n), f(aux['U_over_n'], 6)))
    P('\ncrossover t* = log2 n*:')
    for q in [1, 2, 5, 10]:
        thr = mpf(1) / q
        ra = lambda t: anth_n_rate(t, LEAN, level_root(LEAN, t, 17))[0]
        tA, lA = banded_cross(ra, lambda l: 17 * mpf(LEAN.L[l]), 44, thr)
        P('  A  CountedRoute (e\'=fractionHalf=eps), root17, q=%-3d  l*=%s  t* = %s' % (q, lA, tt(tA)))
        res[('nA', q)] = (tA, lA)
        bestB = (None, None, None)
        for nm in [1, mpf('1.25'), mpf('1.5'), 2]:
            tB, lB = free_cross(lambda l, t: anth_n_rate(t, LEAN, l, ekind='e', nummul=nm)[0], LEAN.L[:44], thr, 17)
            if tB is not None and (bestB[0] is None or tB < bestB[0]): bestB = (tB, lB, nm)
        P('  B  num = eps in [e_l, 2e_l] free (best num/e=%s), level free, q=%-3d  l*=%s  t* = %s' % (f(bestB[2], 3), q, bestB[1], tt(bestB[0])))
        res[('nB', q)] = bestB[:2]
        for nm, fam in TIERC[:2]:
            bestC = (None, None, None)
            for em in [1, 16, 32, 64, 128, 256, 512]:
                tC, lC, zn = best_over(fam[:5], lambda sch: free_cross(lambda l, t: anth_n_rate(t, sch, l, ekind='e', epsmul=em)[0], sch.L[:44], thr, 17))
                if tC is not None and (bestC[0] is None or tC < bestC[0]): bestC = (tC, lC, '%s, eps/e=%s' % (zn, em))
            P('  %s, eps decoupled, q=%-3d  l*=%s  t* = %s  [%s]' % (nm, q, bestC[1], tt(bestC[0]), bestC[2]))
            res[('nC', nm, q)] = bestC[:2]
    tA, lA = res[('nA', 1)]
    r, T, aux = anth_n_rate((tA + mpf(10) ** -9), LEAN, lA)
    n = TWO ** (tA + mpf(10) ** -9)
    P('  terms / n at tier-A n* (q=1, l=%d, Delta=%s, U/n=%s): ' % (lA, f(aux['Delta'], 5), f(aux['U_over_n'], 6)) +
      ', '.join('%s=%s' % (kk, f(v / n, 5)) for kk, v in T.items()))
    P('  (the n-route also has an existential threshold n_1 >= n_0 below which it searches exhaustively; t* is a lower bound for it)')

    # ---------------- HC ----------------
    section('4. #HC (our theorem, conditional on Anthropic Thm A(b) + Lemma 8): vs n^2 2^n')
    P('X = 1 + max{g log K, e(U + gP/K + K^2) + C0 K^2 log(K(L+B\')) + 2gP/K + log tau} + C1 log(g(P+B)) + C2 log n + log#branches/profiles')
    P('%-6s %-5s %-44s %4s  %s' % ('net', 'Delta', 'tier', 'l*', 't* = log2 n*'))
    for net in ['hc', 'deg']:
        for Dlt in [3, 4, 8]:
            for (C0, C1, C2) in [(0, 0, 0), (10, 10, 10)]:
                ra = lambda t: hc_excess(t, LEAN, level_root(LEAN, t, 30), Dlt, net, C0, C1, C2)[0]
                tA, lA = banded_cross(ra, lambda l: 30 * mpf(LEAN.L[l]), 40, mpf(1))
                P('%-6s %-5d %-44s %4s  %s' % (net, Dlt, 'A  K^30<=n, Lean schedule, C0=C1=C2=%d' % C0, lA, tt(tA)))
                res[('hA', net, Dlt, C0)] = (tA, lA)
            tB, lB = free_cross(lambda l, t: hc_excess(t, LEAN, l, Dlt, net)[0], LEAN.L[:40], mpf(1), 30)
            P('%-6s %-5d %-44s %4s  %s' % (net, Dlt, 'B  level free', lB, tt(tB)))
            res[('hB', net, Dlt)] = (tB, lB)
            for nm, fam in TIERC:
                tC, lC, zn = best_over(fam, lambda sch: free_cross(lambda l, t: hc_excess(t, sch, l, Dlt, net)[0], sch.L[:40], mpf(1), 30))
                P('%-6s %-5d %-44s %4s  %s  [%s]' % (net, Dlt, nm, lC, tt(tC), zn))
                res[('hC', net, Dlt, nm)] = (tC, lC)
    tA, lA = res[('hA', 'hc', 3, 0)]
    X, T = hc_terms(LEAN.L[lA], LEAN.e[lA], TWO ** ((tA + mpf(10) ** -9)), 3)
    P('terms / n at tier-A n* (hc, Delta=3, l=%d): ' % lA + ', '.join('%s=%s' % (kk, f(v / TWO ** (tA + mpf(10) ** -9), 5)) for kk, v in T.items()))
    tt_ = (tA + mpf(10) ** -9); n = TWO ** tt_
    ex0 = hc_excess(tt_, LEAN, lA, 3)[0]
    Xc, Tc = hc_terms(LEAN.L[lA], LEAN.e[lA], n, 3, C0=1)
    d0 = Tc['C0 K^2 log'] / n                       # per unit C0, computed directly (no cancellation)
    K = TWO ** LEAN.L[lA]; g = 3 * K ** 8
    d1 = lg(g * n) / n                               # C1 log(g(P+B))/n, P+B <= n for these n
    d2 = 2 * lg(n) / n
    P('    break-even (n* moves only above): C0 > 2^%s, C1 > 2^%s, C2 > 2^%s' % (f(lg((1 - ex0) / d0), 6), f(lg((1 - ex0) / d1), 6), f(lg((1 - ex0) / d2), 6)))

    # ---------------- OpenAI ----------------
    section('5. OpenAI #3-SAT, Engine I (prop:interpolation-bound), n = 2^lam')
    P('rate = leaves 1/s + branches 1/t + Taylor log2 C_q/n + measurements + group 2/r + polylog terms')
    P('\n5a. tier A (paper parameters, lem:incidence-parameters; checks of the proof of thm:overview-sparse-polynomials)')
    P('%4s %16s %10s  %s' % ('j', 'lam=log2 n', 'rate', 'status / terms'))
    for j in range(4, 52, 2):
        lam = 2 ** j
        rate, T, ok, ex = oai_engineI(lam)
        if ok:
            P('%4d %16d %10s  beta=%d r=%d Q=%d R=%d q/n=%s | %s' % (j, lam, f(rate), ex['beta'], ex['r'], ex['Q'], ex['R'], f(ex['q/n'], 3),
              ' '.join('%s=%s' % (kk.split()[0], f(v, 3)) for kk, v in T.items())))
        else:
            P('%4d %16d %10s  %s' % (j, lam, 'brute', ex))
    # crossover tier A: least lam with ok and rate < 1
    lo, hi = 2 ** 20, 2 ** 60
    def okA(lam):
        rate, T, ok, ex = oai_engineI(lam); return ok and rate < 1
    while not okA(hi): hi *= 2
    # find first feasible-and-below-1 by bisection (rate decreasing in lam once feasible)
    a, b = lo, hi
    while b - a > max(1, a // 10 ** 7):
        mid = (a + b) // 2
        if okA(mid): b = mid
        else: a = mid
    earlier = [x for x in range(b // 2, b, max(1, b // 400)) if okA(x)]
    if earlier: b = min(earlier)                  # guard against non-monotone checks (beta jumps)
    rate, T, ok, ex = oai_engineI(b)
    P('\n  A  crossover: lam* = log2 n* ~ %s (log2 lam* = %s); at lam*: rate=%s, %s' % (f(mpf(b), 6), f(lg(b), 5), f(rate, 5), ex))
    P('     terms: ' + ', '.join('%s=%s' % (kk, f(v, 4)) for kk, v in T.items()))
    res['oA'] = b
    P('     a hidden polynomial factor (n+m)^c moves n* only if c > 2^%s' % f(lg((1 - rate) * TWO ** b / (b + 10)), 6))
    # first lam where all numerical checks pass (rate may still exceed 1)
    def feasA(lam): return oai_engineI(lam)[2]
    a, b2 = 2 ** 10, 2 ** 50
    while b2 - a > max(1, a // 10 ** 7):
        mid = (a + b2) // 2
        if feasA(mid): b2 = mid
        else: a = mid
    P('     (all checks of the proof first pass at lam ~ %s; there the rate is %s)' % (f(mpf(b2), 6), f(oai_engineI(b2)[0], 4)))
    res['oAfeas'] = b2
    P('\n5b/5c. tiers B and C: optimise (s, t, r, Q, R; tau minimal) under lem:layout; C adds m_test <= n + n/log2(4/3) + 2')
    for tier, mfac in [('B', 6.0), ('C', 1 + 1 / math.log2(4 / 3))]:
        P('  tier %s, m_test/n = %.4f:  lam -> best rate' % (tier, mfac))
        for j in range(16, 41, 2):
            lam = 2 ** j
            rt, par = oai_opt(lam, mfac)
            P('    j=%2d lam=%14d rate=%.4f %s' % (j, lam, rt, par))
        a, b = 2 ** 10, 2 ** 44
        while oai_opt(b, mfac)[0] >= 1: b *= 2
        while b - a > max(1, a // 2000):
            mid = (a + b) // 2
            if oai_opt(mid, mfac)[0] < 1: b = mid
            else: a = mid
        rt, par = oai_opt(b, mfac)
        mtest = mpf(mfac) * TWO ** b
        rate, T, ok, ex = oai_engineI(b, mtest=mtest, tier='B', r=par['r'], Q=par['Q'], R=par['R'], ssp=par['ssp'], tfac=par['t'])
        P('  %s crossover: lam* ~ %s (log2 lam* = %s); float rate %.5f, mpmath-verified rate %s ok=%s' % (tier, f(mpf(b), 6), f(lg(b), 5), rt, f(rate, 6), ok))
        P('     params %s; terms: %s' % (par, ', '.join('%s=%s' % (kk, f(v, 4)) for kk, v in T.items())))
        res['o' + tier] = b
    section('6. OpenAI Engine II (thm:tensor-contraction): explicit parameter threshold only')
    eps = mpf(1) / 131072
    P('u_d = floor(eps*lam/2^d), eps = 2^-17, depth d < (log2 C + log2 lam / 2)/3; bound lam^(4/5) <= u_d at the deepest')
    P('active call needs eps*lam^(5/6)/C^(1/3) >= lam^(4/5)  <=>  lam >= 2^510 * C^10 (C = wire density constant, >= 1).')
    P('At d = 0 alone: lam >= eps^-5 = 2^85.  So Engine II as written applies only for log2(wires) >= 2^85 (d=0) / 2^510 (all depths).')
    P('Its rate also has the explicit leaf term H/n = wires/(n*floor(sqrt(lam))) >= 1/sqrt(lam); all other constants are O_C(.).')
    return res

def _family(e0, x0):
    out = []
    for z in range(4, 10):
        out.append(('zeta=2^-(l+%d)' % z, Sched(x0=x0, e0=e0, zeta=(lambda zz: (lambda l: TWO ** (-(l + zz))))(z), gk='min')))
    for z in (10, 14):
        out.append(('zeta=2^-%d' % z, Sched(x0=x0, e0=e0, zeta=(lambda zz: (lambda l: TWO ** (-zz)))(z), gk='min')))
    return out

TIERC = [   # (label, schedules); every schedule uses the least g/K allowed by case_ii of Lemma 8
    ('C1 schedule re-tuned (zeta, g/K), e0=1/2', _family(mpf(1) / 2, 18)),
    ('C2 + FMM base e0=5/18 [H]', _family(mpf(5) / 18, 18)),
    ('C3 + e0=omega/9=0.2635 [H]', _family(mpf('2.371552') / 9, 18)),
    ('C4 + e0=5/18, x0=10 [H]', _family(mpf(5) / 18, 10)),
]

if __name__ == '__main__':
    res = main()
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'crossover.out'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
