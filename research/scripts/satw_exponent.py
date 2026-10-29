"""satw_exponent.py -- research/sat-width.md, Sections 1, 3 and 5 (the exponent and its k-range).

Run: python3 -I satw_exponent.py

X1  Lean's occBound k r = 2*(theta_0+...+theta_{k-1})+2 (RecursionToBound/Defs.lean l.115, thresholds
    from Cal/Defs.lean: alphaC, betaC, thetaC) is <= 2(8k/eps)^{3k}+2 (OccBoundIsThePrinted) for
    k = 3..12 and eps in {1/2,...,1/10^5}; prints log2 occBound / ((k-1) log2(k/eps)) (about 2-3:
    log Delta = Theta(k log(k/eps)), the second factor k).
X2  OpenAI's sparsification (main_full_version.tex App. A, 'The size of the tree'): M = least power of
    two >= Gamma with Gamma*ceil(log2(4CM)) <= sigma*M, B = 2*sum_{j<k} M^j. Prints log2 B; checks that
    log2 B grows like k^2 (log2 B / k^2 -> >= log2(3) - o(1)), i.e. worse k-dependence than Calabro's.
X3  The paper's remark (end of App. D): for k = 3, with Delta = 2(2+4a(32a)^{k-2})+2,
    a = 2(k-1)^2 eps^-1 log2(32(k-1)^2/eps), eps = 2e: Delta >= 4096 e^-2 log2(64/e)^2, and
    84 e log2(96 Delta log2(2 Delta)) < 1 forces e < 2.1e-4, hence l >= 23 and log2 n > 8.5e9.
X4  The same threshold if outputs had density d = (k/eps)^3 (hypothetical poly(k/eps) sparsification).
X5  k-range. Leading exponent per variable, per (68) and Step 5:
        cur(k,e) = e*28k*log2(96 D log2 2D) + 2e,   D = occBound(k, eps=e)      (now: k^2 e log(k/e))
        hyp(k,e) = e*28k*log2(96 d log2 2d) + 2e,   d = (k/e)^3                  (one k removed)
        mid(k,e) = same with d = 2^k (k/e)^3                                     (2^{O(k)} poly(1/eps))
    with e = 1/sqrt(L), L = log2 n (shape only: the true e_l has a constant and the level rounding).
    k_max(L) = largest k with exponent/n < 1. Checks the growth exponents d log k_max / d log L:
    about 1/4 (cur, up to loglog), about 1/2 (hyp), about 1/4 (mid).
"""
from fractions import Fraction
from math import ceil, log2, sqrt, floor

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def clog2(x):  # Nat.clog 2 of a positive integer
    c = 0
    while (1 << c) < x:
        c += 1
    return c


def alphaC(k, eps):
    xC = Fraction(32 * (k - 1) ** 2) / eps
    logC = clog2(ceil(xC))
    return ceil(Fraction(2 * (k - 1) ** 2) / eps * logC)


def betaC(a, c, memo):
    if c in memo:
        return memo[c]
    if c == 0:
        v = 0
    elif c == 1:
        v = 2
    else:
        v = sum(4 * a * betaC(a, c - h, memo) * betaC(a, h, memo) for h in range(1, c))
    memo[c] = v
    return v


def occBound(k, eps):
    a = alphaC(k, eps)
    memo = {}
    th = [2] + [a * betaC(a, c, memo) for c in range(1, k)]
    return 2 * sum(th) + 2


def lg(x):
    return log2(x)


def lgbig(x):  # log2 of a big integer
    b = x.bit_length()
    if b > 1000:
        return b - 1000 + log2(x >> (b - 1000))
    return log2(x)


print("X1  log2 occBound / ((k-1) log2(k/eps))   [rows k, columns eps]")
epss = [Fraction(1, 2), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000), Fraction(1, 10 ** 5)]
print("      k " + "".join(f"{str(e):>10}" for e in epss))
for k in range(3, 13):
    row = []
    for eps in epss:
        ob = occBound(k, eps)
        printed_lg = log2(2) + 3 * k * log2(8 * k / float(eps))
        check(lgbig(ob) <= printed_lg + 1e-9 or ob <= 2 * (8 * k / eps) ** (3 * k) + 2, f"X1 k={k} eps={eps}")
        row.append(lgbig(ob) / ((k - 1) * log2(k / float(eps))))
    print(f"    {k:3d} " + "".join(f"{x:10.2f}" for x in row))


def openai_B(k, sigma):
    Gamma = 2 * (3 ** (k - 1) - 1)
    M = 1
    while M < Gamma:
        M *= 2
    while True:
        C = 4 * sum((3 * M) ** j for j in range(k - 1))
        h = clog2(4 * C * M)
        if Gamma * h <= sigma * M:
            break
        M *= 2
    return 2 * sum(M ** j for j in range(k)), M


print("X2  OpenAI App. A: log2 B vs Calabro/Lean log2 occBound, sigma = eps = 1/100")
for k in range(3, 13):
    B, M = openai_B(k, Fraction(1, 100))
    ob = occBound(k, Fraction(1, 100))
    print(f"    k={k:2d}: log2 M={lgbig(M):6.1f}  log2 B={lgbig(B):7.1f}  (log2 B)/k^2={lgbig(B)/k**2:5.2f}"
          f"   log2 occBound={lgbig(ob):7.1f}")
B, M = openai_B(40, Fraction(1, 100))
check(lgbig(B) / 40 ** 2 > log2(3) * 0.9, "X2 OpenAI log2 B ~ k^2 log2 3")
check(lgbig(B) > lgbig(occBound(40, Fraction(1, 100))), "X2 OpenAI B > Calabro occBound at k=40")

# X3
def delta_paper(k, e):
    eps = 2 * e
    a = 2 * (k - 1) ** 2 / eps * log2(32 * (k - 1) ** 2 / eps)
    return 2 * (2 + 4 * a * (32 * a) ** (k - 2)) + 2


def cond(e, D):
    return 84 * e * lg(96 * D * lg(2 * D))


def thresh(f):
    lo, hi = 1e-12, 1.0
    for _ in range(200):
        mid = sqrt(lo * hi)
        if f(mid) < 1:
            lo = mid
        else:
            hi = mid
    return lo


for e in [1e-2, 1e-3, 1e-4, 1e-5]:
    check(delta_paper(3, e) >= 4096 / e ** 2 * log2(64 / e) ** 2, f"X3 Delta lower bound e={e}")
estar = thresh(lambda e: cond(e, delta_paper(3, e)))
check(2.0e-4 < estar < 2.2e-4, f"X3 e* = {estar}")
ell = next(l for l in range(100) if 0.5 * 2 ** (-l / 2) < estar)
logK = 60 * 2 ** ell - 6 * ell - 42
check(ell == 23 and 17 * logK > 8.5e9, f"X3 l={ell} log n > {17*logK}")
print(f"X3  k=3: e* = {estar:.3e} (paper: 2.1e-4), l >= {ell}, log2 n > 17 log K_l = {17*logK:.3e}"
      f" (paper: 8.5e9), i.e. n > 10^{17*logK*log2(2)/log2(10):.2e}")

# X4
estar_h = thresh(lambda e: cond(e, (3 / (2 * e)) ** 3))
print(f"X4  same threshold with density d=(k/eps)^3: e* = {estar_h:.3e}  (vs {estar:.3e})")
check(estar_h > estar, "X4")


# X5
def lg_occ_approx(k, e):
    # log2 occBound via StBetaCat: theta_{k-1} = alpha * 2 (8 alpha)^{k-2} Cat_{k-2} dominates the sum;
    # occBound <= 2*k*theta_{k-1}+2 and >= 2*theta_{k-1}; we take log2(2*k*theta_{k-1}) (an upper bound)
    from math import lgamma, log
    a = 2 * (k - 1) ** 2 / e * ceil(log2(32 * (k - 1) ** 2 / e))
    c = k - 2
    lcat = (lgamma(2 * c + 1) - lgamma(c + 2) - lgamma(c + 1)) / log(2)
    return log2(2 * k) + log2(a) + 1 + c * log2(8 * a) + lcat


def expo(kind, k, e):
    if kind == "cur":
        if k <= 40:
            LD = lgbig(occBound(k, Fraction(1, round(1 / e))))
        else:
            LD = lg_occ_approx(k, e)
        return e * 28 * k * (log2(96) + LD + log2(LD + 1)) + 2 * e
    if kind == "hyp":
        Ld = 3 * log2(k / e)
    else:
        Ld = k + 3 * log2(k / e)
    return e * 28 * k * (log2(96) + Ld + log2(Ld + 1)) + 2 * e


def kmax(kind, L):
    e = 1 / sqrt(L)
    k = 3
    if expo(kind, 3, e) >= 1:
        return 0
    lo, hi = 3, 4
    while expo(kind, hi, e) < 1:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if expo(kind, mid, e) < 1:
            lo = mid
        else:
            hi = mid
    return lo


for k in [10, 20, 40]:
    for e in [1e-2, 1e-4]:
        ex = lgbig(occBound(k, Fraction(1, round(1 / e))))
        ap = lg_occ_approx(k, e)
        check(ex <= ap + 1e-6 and ap - ex < log2(2 * k) + 2, f"approx occBound k={k} e={e}: {ex} vs {ap}")
print("X5  k_max(L), L = log2 n, e = 1/sqrt(L)  (cur uses exact occBound for k <= 40, StBetaCat bound above)")
Ls = [10 ** 8, 10 ** 12, 10 ** 16, 10 ** 24, 10 ** 32]
res = {}
for kind in ["cur", "mid", "hyp"]:
    res[kind] = [kmax(kind, L) for L in Ls]
    print(f"    {kind}: " + "  ".join(f"L=1e{int(round(log2(L)/log2(10)))}:{km}" for L, km in zip(Ls, res[kind])))
for kind, target in [("cur", 0.25), ("mid", 0.25), ("hyp", 0.5)]:
    a, b = res[kind][-2], res[kind][-1]
    slope = (log2(b) - log2(a)) / (log2(Ls[-1]) - log2(Ls[-2]))
    print(f"    growth exponent of k_max ({kind}) between L=1e24 and 1e32: {slope:.3f} (asymptotically {target}, up to loglog)")
    check(abs(slope - target) < 0.08, f"X5 slope {kind} {slope}")
check(all(h >= 10 * c for h, c in zip(res["hyp"][2:], res["cur"][2:])), "X5 hyp range >> cur range")
print("PASS" if FAILS == 0 else f"FAIL ({FAILS})")
