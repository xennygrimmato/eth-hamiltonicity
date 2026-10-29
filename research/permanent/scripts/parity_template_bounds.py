#!/usr/bin/env python3
"""Template (M0) bounds for the parity barrier, full label space B = ([r]x[r])^Q.

Lower bound (Theorem 1 / Cor 1.1 of parity-barrier.md), valid for EVERY M0 with the
support condition:      eps >= LB(Q,R) = Pr[Bin(2Q,1/2) >= Q+R]       (r even)
Upper bounds (commutative swap algebra, M0 = V0 g(Pi)):
  * window (OpenAI):   eps <= min_window Pr[Bin(Q,p) not in window of R consecutive], p=(r-1)/2r
  * best symmetric g:  eps_sym(R) = 1 - max{ Pr[j in J] : (-1)^j|_J interpolable, deg <= R-1 }
                        (exhaustive over all level sets J, exact rational arithmetic)
  * best general multilinear g of degree <= R-1 (non-symmetric), exhaustive over agreement
    sets S of the p-biased cube, Q <= 4.
All probabilities exact (fractions / big integers); printed as floats.
"""
from fractions import Fraction as F
from math import comb, log, sqrt
from itertools import combinations
import sys

def binom_pmf(Q, p):
    return [F(comb(Q, j)) * p**j * (1 - p)**(Q - j) for j in range(Q + 1)]

def LB(Q, R):
    """Pr[Bin(2Q,1/2) >= Q+R]"""
    return F(sum(comb(2 * Q, k) for k in range(Q + R, 2 * Q + 1)), 4**Q)

def window_eps(Q, R, p):
    pm = binom_pmf(Q, p)
    if R > Q:
        return F(0)
    best = max(sum(pm[a:a + R]) for a in range(0, Q - R + 2))
    return 1 - best

def window_eps_float(Q, R, p):
    # float version for large Q (log-space pmf)
    from math import lgamma, exp
    lp = [lgamma(Q + 1) - lgamma(j + 1) - lgamma(Q - j + 1) + j * log(p) + (Q - j) * log(1 - p) for j in range(Q + 1)]
    pm = [exp(x) for x in lp]
    if R > Q:
        return 0.0
    s = sum(pm[:R]); best = s
    for a in range(1, Q - R + 2):
        s += pm[a + R - 1] - pm[a - 1] if a + R - 1 <= Q else -pm[a - 1]
        best = max(best, s)
    return max(0.0, 1 - best)

def LB_float(Q, R):
    from math import lgamma, exp
    N = 2 * Q
    tot = 0.0
    for k in range(Q + R, N + 1):
        tot += exp(lgamma(N + 1) - lgamma(k + 1) - lgamma(N - k + 1) - N * log(2))
    return tot

def interp_degree(J):
    """degree of the interpolant of (-1)^j through the points J (exact Newton form)."""
    xs = list(J); ys = [F((-1)**j) for j in xs]
    n = len(xs); coef = ys[:]
    for lvl in range(1, n):
        for i in range(n - 1, lvl - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - lvl])
    deg = 0
    for i in range(n):
        if coef[i] != 0:
            deg = i
    return deg

def sym_opt(Q, p, Rmax):
    pm = binom_pmf(Q, p)
    best = {R: F(0) for R in range(1, Rmax + 1)}
    bestJ = {R: None for R in range(1, Rmax + 1)}
    for mask in range(1, 2**(Q + 1)):
        J = [j for j in range(Q + 1) if mask >> j & 1]
        d = interp_degree(J)
        w = sum(pm[j] for j in J)
        for R in range(d + 1, Rmax + 1):
            if w > best[R]:
                best[R] = w; bestJ[R] = J
    return {R: (1 - best[R], bestJ[R]) for R in best}

def general_opt(Q, p, Rmax):
    """max p-biased mass of S subset {+-1}^Q such that parity|_S lies in span of monomials of
    degree <= R-1 restricted to S. Exhaustive; Q <= 4. Uses exact rank over Q via fractions-free
    integer elimination (sympy-free): rank via numpy on small integer matrices is exact enough here,
    but we use a fraction Gaussian elimination to be safe."""
    pts = [tuple(1 - 2 * ((x >> i) & 1) for i in range(Q)) for x in range(2**Q)]
    wt = [p**sum(1 for s in pt if s == -1) * (1 - p)**sum(1 for s in pt if s == 1) for pt in pts]
    par = [eval('*'.join(map(str, pt))) if Q else 1 for pt in pts]
    out = {}
    for R in range(1, Rmax + 1):
        mons = [S for k in range(R) for S in combinations(range(Q), k)]
        rows = []
        for pt in pts:
            row = []
            for S in mons:
                v = 1
                for i in S:
                    v *= pt[i]
                row.append(v)
            rows.append(row)
        best = F(0); bestS = None
        for mask in range(1, 2**(2**Q)):
            idx = [i for i in range(2**Q) if mask >> i & 1]
            w = sum(wt[i] for i in idx)
            if w <= best:
                continue
            A = [rows[i][:] for i in idx]
            Ab = [rows[i][:] + [par[i]] for i in idx]
            if rank(A) == rank(Ab):
                best = w; bestS = idx
        out[R] = (1 - best, bestS)
    return out

def rank(M):
    M = [[F(x) for x in r] for r in M]
    if not M:
        return 0
    rk = 0; ncol = len(M[0])
    for c in range(ncol):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c] / M[rk][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def main():
    p2 = F(1, 4)
    print("== Part A: exact small-Q table, r=2 (p=1/4). eps values (fraction of D measured) ==")
    print("LB = Pr[Bin(2Q,1/2)>=Q+R] (all M0); WIN = OpenAI window; SYM = best symmetric g; GEN = best multilinear g (Q<=4)")
    for Q in range(2, 13):
        Rmax = Q
        sym = sym_opt(Q, p2, Rmax)
        gen = general_opt(Q, p2, min(Rmax, Q)) if Q <= 4 else None
        for R in range(1, Rmax + 1):
            lb = LB(Q, R); win = window_eps(Q, R, p2); s = sym[R][0]
            line = f"Q={Q:2d} R={R:2d}  LB={float(lb):.5f}  WIN={float(win):.5f}  SYM={float(s):.5f} J={sym[R][1]}"
            if gen is not None:
                line += f"  GEN={float(gen[R][0]):.5f}"
            assert lb <= s + 0 or True
            if lb > s:
                line += "  !!LB>SYM (contradiction)"
            print(line)
        sys.stdout.flush()
    print()
    print("== Part B: R needed vs Q at fixed eps (r=2 window p=1/4; r->inf window p=1/2; lower bound for all M0) ==")
    for eps in (1e-1, 1e-2, 1e-3, 1e-4):
        print(f"-- eps = {eps}")
        print(" Q     R_LB   R_win(r=2)  R_win(r=inf)   R_LB/sqrt(Q ln1/e)  R_win_inf/sqrt(Q ln1/e)  ratio win_inf/LB")
        for Q in (8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
            def first(fn):
                for R in range(1, Q + 2):
                    if fn(R) <= eps:
                        return R
                return None
            rl = first(lambda R: LB_float(Q, R))
            rw2 = first(lambda R: window_eps_float(Q, R, 0.25))
            rwi = first(lambda R: window_eps_float(Q, R, 0.5))
            sc = sqrt(Q * log(1 / eps))
            print(f"{Q:5d} {rl:6d} {rw2:9d} {rwi:12d}   {rl/sc:12.3f}   {rwi/sc:16.3f}   {rwi/rl:10.3f}")
        sys.stdout.flush()

if __name__ == "__main__":
    main()
