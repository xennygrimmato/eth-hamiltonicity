#!/usr/bin/env python3
"""Rate of Ryser's formula through OpenAI's replacement-form engine (ETH paper, eq. (2.6)
"three costs"), with exact binomial tails and the paper's constraints, versus Ryser (rate 1)
and versus Anthropic's engine on the bounded-degree profile network (permanent-attack.md §4).

Model (log2 of time divided by n), Ryser on an n x n matrix with <= Delta nonzeros per row/col:
  Taylor data   : q = 2nR/Q coefficients  ->  (2R/Q) * log2(e*Q/R)
  measurements  : rows <= 2 r eps M, M <= n(Delta+1), values in [-D, D]
                  ->  2 r eps (Delta+1) * log2(2D+1)
  one group     : 2^{2n/r}  ->  2/r
  constraints   : D = r^{2Q};  2(b+w) D^2 <= M with b = w = Delta+1  ->  D^2 <= n/4;
                  2 Q r^2 <= n;  R < Q;  eps = Pr[Bin(Q,(r-1)/2r) notin best window of R ints].
Anthropic comparator: e_K * 2 lg(e Delta) with e_K <= 0.85 sqrt((3x0+6)/lg K), x0 = 18,
  K = n^{1/9}  (rate.md §1.1; permanent-attack.md §4) -- an upper bound on that engine's guarantee.
All numbers are heuristic in the sense that lower-order terms (poly factors, rounding) are dropped.
"""
import math

def log_binom_pmf(Q, p):
    return [math.lgamma(Q + 1) - math.lgamma(k + 1) - math.lgamma(Q - k + 1) + k * math.log(p) + (Q - k) * math.log(1 - p) for k in range(Q + 1)]

def logsumexp(xs):
    if not xs: return -float('inf')
    m = max(xs); return m + math.log(sum(math.exp(x - m) for x in xs))

def best_rate(lam, log2Delta):
    best = (float('inf'), None)
    lnDelta1 = math.log(2.0) * log2Delta + math.log1p(2.0 ** (-log2Delta))
    for r in [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 256, 512, 1024]:
        Qmax = int((lam - 2) / (4 * math.log2(r)))
        if Qmax < 4 or 2 * Qmax * r * r > 2 ** min(lam, 60): continue
        Q = Qmax
        lp = log_binom_pmf(Q, (r - 1) / (2 * r))
        NEG = -float('inf')
        def lae(x, y):
            if x == NEG: return y
            if y == NEG: return x
            m = max(x, y); return m + math.log(math.exp(x - m) + math.exp(y - m))
        lcdf = [NEG] * (Q + 2)   # lcdf[k] = log P[W < k]
        for k in range(Q + 1): lcdf[k + 1] = lae(lcdf[k], lp[k])
        lsf = [NEG] * (Q + 2)    # lsf[k] = log P[W >= k]
        for k in range(Q, -1, -1): lsf[k] = lae(lsf[k + 1], lp[k])
        mean = Q * (r - 1) / (2 * r)
        log2D = 2 * Q * math.log2(r)
        for R in range(1, Q):
            st0 = int(round(mean - R / 2))
            lneps = min(lae(lcdf[min(Q + 1, max(0, s))], lsf[min(Q + 1, max(0, s) + R)]) for s in range(st0 - 2, st0 + 3))
            eps = math.exp(lneps) if lneps > -700 else 0.0
            taylor = (2 * R / Q) * math.log2(math.e * Q / R)
            lnmeas = math.log(2 * r) + lneps + lnDelta1 + math.log(log2D + 1)
            meas = math.exp(lnmeas) if lnmeas < 50 else float('inf')
            group = 2.0 / r
            tot = taylor + meas + group
            if tot < best[0]: best = (tot, dict(r=r, Q=Q, R=R, lneps=round(lneps,1), taylor=round(taylor, 4), meas=round(meas, 4), group=round(group, 4)))
            if taylor > best[0]: break
    return best

def anthropic_rate(lam, log2Delta):
    lgK = lam / 9.0
    e = 0.85 * math.sqrt((3 * 18 + 6) / lgK)
    return e * 2 * (log2Delta + math.log2(math.e))

if __name__ == '__main__':
    print('rate = log2(time)/n ; Ryser = 1')
    print('%8s %10s %10s %12s   %s' % ('log2 n', 'log2 Delta', 'OpenAI+Ryser', 'Anthropic', 'OpenAI parameters'))
    for lam in [64, 256, 1024, 4096, 16384, 65536, 262144]:
        for tag, ld in [('O(1)', 1.6), ('lam^1/4', lam ** 0.25), ('lam^1/2', lam ** 0.5), ('lam^3/4', lam ** 0.75), ('lam/8', lam / 8)]:
            rate, par = best_rate(lam, ld)
            print('%8d %10s %12.4f %12.4f   %s' % (lam, tag, rate, anthropic_rate(lam, ld), par))
    # asymptotic shape check: rate * sqrt(lam / (log2Delta * log2 lam)) / log2 lam should stay bounded
    print('\nshape check at log2 Delta = lam^(1/2):  rate / (sqrt(log2Delta*log2 lam/lam) * log2 lam)')
    for lam in [1024, 4096, 16384, 65536, 262144, 1048576]:
        ld = lam ** 0.5
        rate, _ = best_rate(lam, ld)
        print('%8d  %.4f' % (lam, rate / (math.sqrt(ld * math.log2(lam) / lam) * math.log2(lam))))
