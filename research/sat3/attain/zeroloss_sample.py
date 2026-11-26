#!/usr/bin/env python3
"""Cross-check of Lemma 5.3 (zero loss) on a sample of large pairs with p, q = log2 p(m_i) (exact criterion,
60 digits); complements Step 2 of the proof.  Usage: zeroloss_sample.py"""
from mpmath import mp, mpf, log
mp.dps = 60
MS = [1, 2, 5, 13, 30, 31, 32, 50, 77, 100, 150, 233, 400, 800, 1500]
NMAX = 2 * (2 * max(MS)) + 10
pn = [0] * (NMAX + 1); pn[0] = 1
for k in range(1, NMAX + 1):
    for n in range(k, NMAX + 1):
        pn[n] += pn[n - k]
cum = []; s = 0
for n in range(NMAX + 1):
    s += pn[n]; cum.append(s)
LOG2 = log(2); _f = {}
def f(E):
    if E not in _f: _f[E] = log((E + 1) * cum[E // 2]) / LOG2
    return _f[E]
def check(m1, m2):
    p = log(pn[m1]) / LOG2; q = log(pn[m2]) / LOG2
    Th = 4 * (m1 + m2); R2 = 2 * (p * p + q * q); cap = p + q; lo = abs(p - q)
    worst = mpf(10) ** 9
    if f(Th) < cap: return mpf(-1)
    N = 1
    while True:
        a = max(f(N - 1), lo); b = min(f(N), cap)
        if b >= a and f(N) >= lo and f(Th - N) < cap:
            worst = min(worst, f(Th - N) ** 2 - (R2 - a * a))
        if f(N) >= cap or N >= Th: break
        N += 1
    return worst
bad = 0; wm = (mpf(10) ** 9, None)
for i, m1 in enumerate(MS):
    for m2 in MS[i:]:
        w = check(m1, m2)
        if w < 0: bad += 1
        if w < wm[0]: wm = (w, (m1, m2))
print("pairs", len(MS) * (len(MS) + 1) // 2, "failures", bad, "smallest margin (squared bits)", mp.nstr(wm[0], 8), "at", wm[1])
