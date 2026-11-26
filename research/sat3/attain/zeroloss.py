#!/usr/bin/env python3
"""Zero-loss lemma for the certified crossing bonds (attain-notes.md, Lemma 5.2').

Notation: p(m) partitions; P(E) = sum_{m <= E/2} p(m) = #symbols of energy <= E; f(E) = log2((E+1) P(E));
kappa = pi/sqrt3, kappa' = kappa/ln 2.  Classes of energies e_i = 2 m_i have log2-size <= log2 p(m_i);
Theta = 2(e1+e2) = 4(m1+m2).

(A) (Z'):  (E+1) P(E) >= exp(kappa sqrt(E + 1/2))  -- find the last failure E_fail, verify E_fail < E < 2*MPROOF exactly
    (integers against a 60-digit evaluation), and check the constants of the analytic proof for M >= MPROOF.
(B) sanity check of the quoted two-sided bound (Lehmer / Bessenrodt-Ono) for 1 <= n <= NCHK.
(C) threshold m0: smallest m with 2 d0(m) sqrt(2m) >= kappa'(E0 + 1/2) for all larger m.
(D) exhaustive exact check of the zero-loss criterion for all 1 <= m1 <= m2 <= MEX with p, q = log2 p(m_i)
    (an upper bound for every class of these energies; the criterion is monotone in (p,q) at fixed Theta):
       for every (r, r') with r^2 + r'^2 = 2(p^2+q^2), |p-q| <= r' <= p+q  there is N with f(N) >= r', f(Theta-N) >= r.
    Equivalent finite form: with N(r') = min{N : f(N) >= r'}, for every N in the range, f(Theta-N)^2 >= 2(p^2+q^2) - max(f(N-1), |p-q|)^2
    (for N = 0: f(Theta) >= p+q), where f(Theta - N) may be replaced by min(f, p+q).
"""
import sys
from mpmath import mp, mpf, log, exp, sqrt, pi, floor
mp.dps = 60
MEX = int(sys.argv[1]) if len(sys.argv) > 1 else 120
MPROOF = 400
NMAX = max(4 * MEX + 10, 2 * MPROOF + 10, 20010)

pn = [0] * (NMAX + 1); pn[0] = 1
for k in range(1, NMAX + 1):
    for n in range(k, NMAX + 1):
        pn[n] += pn[n - k]
cum = []; s = 0
for n in range(NMAX + 1):
    s += pn[n]; cum.append(s)
P = lambda E: cum[E // 2]
kappa = pi / sqrt(3); kp = kappa / log(2)
LOG2 = log(2)
_f = {}
def f(E):
    if E not in _f: _f[E] = log((E + 1) * P(E)) / LOG2
    return _f[E]

# (A)
fails = [E for E in range(0, 2 * MPROOF) if (E + 1) * P(E) < exp(kappa * sqrt(E + mpf(1) / 2))]
E_fail = max(fails)
print("(A) (Z') fails exactly for E in", fails[:5], "...", fails[-5:], " last failure E =", E_fail, " -> E0 =", E_fail + 1)
ratmin = min(((E + 1) * P(E)) / exp(kappa * sqrt(E + mpf(1) / 2)) for E in range(E_fail + 1, 2 * MPROOF))
print("    min ratio (E+1)P(E)/exp(kappa sqrt(E+1/2)) on E0 <= E < %d: %s" % (2 * MPROOF, mp.nstr(ratmin, 8)))
# analytic part, M >= MPROOF: ln(0.27386 sqrt M) - 1.368 > 0
M = MPROOF
c1 = 2 * (1 - 1 / sqrt(M - sqrt(M))) / (4 * sqrt(3))
c2 = (pi / sqrt(6)) * (1 + (mpf(19) / 36) * 3 / (2 * sqrt(M))) / sqrt(1 - 1 / sqrt(M) - mpf(1) / (24 * M))
print("    analytic constants at M = %d: c1 = %s (first term >= ln(c1 sqrt M) = %s), c2 = %s" % (M, mp.nstr(c1, 6), mp.nstr(log(c1 * sqrt(M)), 6), mp.nstr(c2, 6)))
# direct check of (Z') further out, as a cross-check of the analytic part
bad = [E for E in range(2 * MPROOF, 20000) if (E + 1) * P(E) < exp(kappa * sqrt(E + mpf(1) / 2))]
print("    cross-check (Z') for %d <= E < 20000: failures %d" % (2 * MPROOF, len(bad)))

# (B)
mu = lambda n: pi / 6 * sqrt(24 * n - 1)
NCHK = 10000
okl = all(pn[n] > sqrt(3) / (12 * n) * (1 - 1 / sqrt(n)) * exp(mu(n)) for n in range(1, NCHK + 1))
oku = all(pn[n] < sqrt(3) / (12 * n) * (1 + 1 / sqrt(n)) * exp(mu(n)) for n in range(1, NCHK + 1))
print("(B) quoted bounds sqrt3/(12n)(1 -+ 1/sqrt n) e^mu(n) hold for 1 <= n <= %d: lower %s, upper %s" % (NCHK, okl, oku))

# (C)
E0 = E_fail + 1
d0 = lambda m: log(4 * sqrt(3) * m / (1 + 1 / sqrt(m))) / LOG2
need = kp * (E0 + mpf(1) / 2)
ok = [m for m in range(1, 2000) if 2 * d0(m) * sqrt(2 * m) >= need]
m0 = min(m for m in ok if all(mm in set(ok) for mm in range(m, 2000)))
print("(C) kappa' = %s; need 2 d0(m) sqrt(2m) >= kappa'(E0+1/2) = %s: holds for all m >= m0 = %d (and Theta >= 2 E0 needs m1+m2 >= %d)" % (mp.nstr(kp, 8), mp.nstr(need, 8), m0, (2 * E0 + 3) // 4))

# (D)
def check(m1, m2):
    p = log(pn[m1]) / LOG2; q = log(pn[m2]) / LOG2
    Th = 4 * (m1 + m2); R2 = 2 * (p * p + q * q); cap = p + q; lo = abs(p - q)
    worst = mpf(10) ** 9
    # N = 0 is used only for r' <= f(0) = 0, i.e. p = q and r' = 0, r = p+q
    if lo == 0:
        worst = min(worst, f(Th) - cap)
    N = 1
    while True:
        # N serves r' in (f(N-1), f(N)] intersected with [lo, cap]
        a = max(f(N - 1), lo); b = min(f(N), cap)
        if b >= a and f(N) >= lo:
            # if f(Theta-N) >= p+q the condition holds identically ((p+q)^2 >= R^2 - a^2 since a >= |p-q|); skip the tie
            if f(Th - N) < cap:
                fc = f(Th - N)
                # worst r' in the interval is its infimum a (largest r); margin in squares
                worst = min(worst, fc * fc - (R2 - a * a))
        if f(N) >= cap or N >= Th:
            break
        N += 1
    if f(Th) < cap: worst = min(worst, mpf(-1))
    return worst
wm = (mpf(10) ** 9, None); nb = 0; cnt = 0
for m1 in range(1, MEX + 1):
    for m2 in range(m1, MEX + 1):
        w = check(m1, m2); cnt += 1
        if w < 0: nb += 1
        if w < wm[0]: wm = (w, (m1, m2))
print("(D) pairs 1 <= m1 <= m2 <= %d: %d; failures: %d; smallest margin (in squared bits) %s at %s" % (MEX, cnt, nb, mp.nstr(wm[0], 8), wm[1]))
