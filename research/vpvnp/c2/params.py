#!/usr/bin/env python3
"""Parameter checks for c2/notebook.md (corollaries of the VP != VNP bound).

All logarithms base 2.  Hardness (Thm 1.1/1.4 of the paper):
    L(HC_m) > 2^{c (log m)^{4/3}}  for m >= m0 (m0 ineffective),
with explicit c = 1600^{-4/3} from Theorem E.11 (flat case; the contracting
case gives a larger bound for large m, so c works in both cases eventually).

We work in log-space:  lam = log2 s,  mu = log2 m.
Size of the reconstructed circuit for HC_m (Lemma 2 + Lemma 3 of the notebook):
    L_P = s + n (a+2) 2^a,               a = ceil(log n / log q), q ~ m^2
    L_Q = (d'+1) L_P + 3 (d'+1)^2,       d' = deg_x bound (d, or p-1)
    L_f = 2 (m+1)^2 (m (L_Q+3) + 1) + 2 m^2
Hitting set size |H| = (d m + 1)^t,  t = q^2 <= 4 m^4.
"""
from mpmath import mp, mpf, log, ceil, power

mp.dps = 50
C_EXPL = power(mpf(1600), mpf(-4) / 3)


def log2(x):
    return log(x, 2)


def log2_sum(a, b):  # log2(2^a + 2^b)
    hi, lo = max(a, b), min(a, b)
    return hi + log2(1 + power(2, lo - hi))


def log2_Lf(lam, mu, ln=None, ld=None):
    """log2 of L_f for s=2^lam, n=2^ln, d=2^ld (defaults n=d=s), m=2^mu."""
    ln = lam if ln is None else ln
    ld = lam if ld is None else ld
    logq = 2 * mu
    a = ceil(ln / logq)
    lP = log2_sum(lam, ln + log2(a + 2) + a)
    ld1 = log2_sum(ld, 0)  # log2(d+1)
    lQ = log2_sum(ld1 + lP, log2(3) + 2 * ld1)
    lm1 = log2_sum(mu, 0)
    inner = log2_sum(mu + log2_sum(lQ, log2(3)), 0)
    return log2_sum(1 + 2 * lm1 + inner, 1 + 2 * mu)


def min_mu(lam, c=C_EXPL, **kw):
    """least mu (bisection, real) with log2 L_f < c mu^{4/3}."""
    lo, hi = mpf(1), mpf(1)
    while log2_Lf(lam, hi, **kw) >= c * hi ** (mpf(4) / 3):
        hi *= 2
    for _ in range(200):
        mid = (lo + hi) / 2
        if log2_Lf(lam, mid, **kw) < c * mid ** (mpf(4) / 3):
            hi = mid
        else:
            lo = mid
    return hi


def loglog_H(lam, mu, ld=None):
    ld = lam if ld is None else ld
    return 2 + 4 * mu + log2(log2_sum(ld + mu, 0))


def main():
    c = C_EXPL
    print("c =", mp.nstr(c, 8))
    print("\n[PIT] n = d = s = 2^lam.  mu = log m needed;  loglog|H|;  "
          "predicted 4*(2 lam/c)^{3/4};  ratio")
    for lam in [10 ** k for k in range(6, 32, 2)]:
        lam = mpf(lam)
        mu = min_mu(lam, c)
        llH = loglog_H(lam, mu)
        pred = 4 * (2 * lam / c) ** (mpf(3) / 4)
        triv = lam + log2(lam)  # loglog of (s+1)^s
        print(f"lam=1e{int(mp.log10(lam))}: mu={mp.nstr(mu,8)}  "
              f"loglog|H|={mp.nstr(llH,8)}  pred={mp.nstr(pred,8)}  "
              f"ratio={mp.nstr(llH/pred,6)}  beats trivial: {llH < triv}")
    # threshold where |H| < (s+1)^s
    lo, hi = mpf(10) ** 6, mpf(10) ** 22
    for _ in range(200):
        mid = (lo + hi) / 2
        if loglog_H(mid, min_mu(mid, c)) < mid + log2(mid):
            hi = mid
        else:
            lo = mid
    print("H beats trivial (s+1)^s once log2 s >", mp.nstr(hi, 6))
    print("  rough prediction (4^4*(2/c)^3):",
          mp.nstr(4 ** 4 * (2 / c) ** 3, 6))

    # generic c: constant K(c) in loglog|H| ~ K (log s)^{3/4}
    print("\nK(c) = 4*(2/c)^{3/4}: c=1 ->", mp.nstr(4 * mpf(2) ** 0.75, 6),
          "; c=1600^{-4/3} ->", mp.nstr(4 * (2 / c) ** 0.75, 8))

    # determinantal complexity
    print("\n[dc] dc >= m^{(c/e)(log m)^{1/3}}; exceeds m^k once log m > (k e/c)^3")
    for e, name in [(mpf("2.697263"), "Kaltofen-Villard"), (mpf(4), "Berkowitz")]:
        for k in (2, 3):
            print(f"  e={e} ({name}), beats m^{k} once log2 m > "
                  f"{mp.nstr((k*e/c)**3, 6)}")

    # depth
    print("\n[depth] depth >= c (log m)^{4/3} - 1 exceeds 2 log m once log m >",
          mp.nstr((2 / c) ** 3, 6))


if __name__ == "__main__":
    main()
