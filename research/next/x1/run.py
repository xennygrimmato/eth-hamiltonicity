#!/usr/bin/env python3
"""Driver: python3 run.py <task> [args].  Tasks:
  bezout DMAX            unique Bezout witness check
  tuple N                literal (n,d,m,x,x') loop == factored sum, bit for bit (Ni params at N)
  nodes N M              node/sign expansion into integer combination of sums of products of quotients
  pi N [ni|ours]         pi~(N) for all N'<=N, error and rounding
  twin N | gold N2 | sg N | mertens N | stress N
"""
import sys, math, time
from math import gcd
from fractions import Fraction
from multiprocessing import Pool
from pipeline import *

def blen(n): return max(1, n.bit_length())

def D_needed(kind, X):
    """per-factor error exponent D from the budget (notebook section 2). X = largest argument."""
    b = blen(X)
    if kind == 'pi':      # k=4, T<=N^3, prod(B+1) <= 9.8(b+1)
        return 3 * b + math.ceil(math.log2(2 * 4 * 9.8 * (b + 1))) + 1
    if kind == 'pair':    # k=8, T<=X^5, prod(B+1) <= 96.1(b+1)^2
        return 5 * b + math.ceil(math.log2(2 * 8 * 96.1 * (b + 1) ** 2)) + 1
    if kind == 'mertens': # k=1, T<=N^2
        return 2 * b + 2
    raise ValueError

_P = None
def _init(M, p, t, jmax):
    global _P
    _P = Pipeline(M, p, t, jmax)
def _A(d): return d, _P.A(d)

def tables(M, p, t, X, procs=4):
    jmax = blen(X)
    P = Pipeline(M, p, t, jmax)
    with Pool(procs, initializer=_init, initargs=(M, p, t, jmax)) as pool:
        A = dict(pool.map(_A, range(1, X + 1), chunksize=8))
    return P, A

def prime_tilde(P, A, X):
    """Pt[n] = -A(n) Finv(n) sum_{dm=n, m>=2} A(d) Flog(m)  (denominator S^4)."""
    Flog = {m: P.Flog(m) for m in range(2, X + 1)}
    Pt = {}
    for n in range(2, X + 1):
        s = (0, 0)
        for d in range(1, n // 2 + 1):
            if n % d == 0:
                s = gadd(s, gmul(A[d], Flog[n // d]))
        v = gmul(gmul(A[n], P.Finv(n)), s)
        Pt[n] = (-v[0], -v[1])
    return Pt

def rnd(re, den):          # floor(Re + 1/2), exact
    return (2 * re + den) // (2 * den)

def report(name, vals, truth, den, budget):
    worst = Fraction(0); bad = 0
    for key in vals:
        re, im = vals[key]
        e = abs(Fraction(re, den) - truth[key])
        worst = max(worst, e)
        if rnd(re, den) != truth[key]: bad += 1
    print(f"{name}: {len(vals)} values, rounding failures {bad}, max |error| = {float(worst):.3e}"
          f" (2^{math.log2(worst) if worst else float('-inf'):.1f}), budget bound {budget:.3e}")
    sys.stdout.flush()
    return bad, worst

def main():
    task = sys.argv[1]
    if task == 'bezout':
        DM = int(sys.argv[2]); bad = 0
        for d in range(2, DM + 1):
            for x in range(1, d):
                w = sum(1 for u in range(d) if (x * u - 1) % d == 0 and 0 <= (x * u - 1) // d < x)
                if w != (1 if gcd(x, d) == 1 else 0): bad += 1
        print(f"bezout d<={DM}: mismatches {bad}")
        return
    if task == 'tuple':
        N = int(sys.argv[2]); b = blen(N)
        M, p, t = 35 * b + 185, 7 * b + 32, 7 * b + 25
        P = Pipeline(M, p, t, b)
        T0 = time.time(); lit = tuple_sum_pi(P, N); T1 = time.time()
        A = {d: P.A(d) for d in range(1, N + 1)}
        Pt = prime_tilde(P, A, N)
        fac = (0, 0)
        for n in range(2, N + 1): fac = gadd(fac, Pt[n])
        den = P.S ** 4
        print(f"tuple N={N} (Ni params M={M},p={p},t={t}): literal==factored: {lit == fac};"
              f" pi~={float(Fraction(lit[0], den)):.15f}+{float(Fraction(lit[1], den)):.1e}i,"
              f" round={rnd(lit[0], den)}, true={sum(sieve(N))}; literal loop {T1-T0:.1f}s")
        return
    if task == 'nodes':
        N, M = int(sys.argv[2]), int(sys.argv[3]); p = t = 12; b = blen(N)
        P = Pipeline(M, p, t, b)
        lit = tuple_sum_pi(P, N)
        # expansion: each factor value = sum_l sum_{part in (r,i)} C_l * (1 or i) * sign * q
        def parts(coefs, a, q):
            out = []
            for l in range(M):
                kr, ki = P.kparts(l, a, q)
                out.append((('C', id(coefs), l, 'r', 1 if kr >= 0 else -1), abs(kr)))
                out.append((('C', id(coefs), l, 'i', 1 if ki >= 0 else -1), abs(ki)))
            return out
        counts = {}
        for n in range(2, N + 1):
            jn = n.bit_length() - 1
            for d in range(1, n + 1):
                if n % d or n // d == 1: continue
                m = n // d; jm = m.bit_length() - 1
                xs = [0] if d == 1 else [x for x in range(1, d) if gcd(x, d) == 1]
                for x in xs:
                    f1 = [(('ONE',), P.S)] if d == 1 else parts(P.ce, d + x, d)
                    for xp in range(1, n):
                        if gcd(xp, n) != 1: continue
                        f2 = parts(P.ce, n + xp, n)
                        f3 = [((k[0], 'log', jm) + k[2:], q) for k, q in parts(P.clog[jm], m, 1 << jm)]
                        f4 = [((k[0], 'inv', jn) + k[2:], q) for k, q in parts(P.cinv[jn], n, 1 << jn)]
                        for k1, q1 in f1:
                            for k2, q2 in f2:
                                for k3, q3 in f3:
                                    for k4, q4 in f4:
                                        key = (k1, k2, k3, k4)
                                        counts[key] = counts.get(key, 0) + q1 * q2 * q3 * q4
        tabs = {id(P.ce): P.ce}
        def coef(k):
            if k[0] == 'ONE': return (1, 0)
            if k[1] == 'log': c = P.clog[k[2]][k[3]]; part, s = k[4], k[5]
            elif k[1] == 'inv': c = P.cinv[k[2]][k[3]]; part, s = k[4], k[5]
            else: c = tabs[k[1]][k[2]]; part, s = k[3], k[4]
            c = (s * c[0], s * c[1])
            return c if part == 'r' else (-c[1], c[0])
        tot = (0, 0)
        for key, cnt in counts.items():
            c = (1, 0)
            for k in key: c = gmul(c, coef(k))
            tot = gadd(tot, (c[0] * cnt, c[1] * cnt))
        tot = (-tot[0], -tot[1])
        print(f"nodes N={N} M={M}: {len(counts)} (node,part,sign) classes; integer combination of counts"
              f" == literal sum: {tot == lit}")
        return
    if task == 'pi':
        N = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'ni'
        b = blen(N)
        if mode == 'ni': M, p, t = 35 * b + 185, 7 * b + 32, 7 * b + 25
        else: M, p, t = params_for(D_needed('pi', N), b)
        T0 = time.time(); P, A = tables(M, p, t, N); Pt = prime_tilde(P, A, N)
        den = P.S ** 4; pr = sieve(N)
        vals, truth = {}, {}; acc = (0, 0); c = 0
        for n in range(2, N + 1):
            acc = gadd(acc, Pt[n]); c += pr[n]; vals[n] = acc; truth[n] = c
        budget = 2 * N ** 3 * 4 * 9.8 * (b + 1) * 2.0 ** -D_needed('pi', N)
        print(f"[pi {mode}] N={N} M={M} p={p} t={t} time {time.time()-T0:.0f}s")
        report(f"pi~(N'), N'<= {N}", vals, truth, den, 0.5 if mode == 'ni' else budget / 2)
        # per-n indicator errors
        worst = max(abs(Fraction(Pt[n][0], den) - pr[n]) for n in range(2, N + 1))
        print(f"   max_n |1~_prime(n) - 1_prime(n)| = {float(worst):.3e}")
        return
    if task in ('twin', 'gold', 'sg', 'stress'):
        N = int(sys.argv[2])
        X = {'twin': N + 2, 'gold': N, 'sg': 2 * N + 1, 'stress': N + 2}[task]
        b = blen(X); Dn = D_needed('pair', X)
        Ds = [Dn] if task != 'stress' else [int(v) for v in sys.argv[3].split(',')]
        for D in Ds:
            M, p, t = params_for(D, b)
            T0 = time.time(); P, A = tables(M, p, t, X); Pt = prime_tilde(P, A, X)
            den = P.S ** 8; pr = sieve(X)
            budget = 2 * X ** 5 * 8 * 96.1 * (b + 1) ** 2 * 2.0 ** -D / 2
            print(f"[{task}] N={N} X={X} D={D} (needed {Dn}) M={M} p={p} t={t} time {time.time()-T0:.0f}s")
            vals, truth = {}, {}
            if task in ('twin', 'stress', 'sg'):
                sh = (lambda n: n + 2) if task != 'sg' else (lambda n: 2 * n + 1)
                acc = (0, 0); c = 0
                for n in range(2, N + 1):
                    acc = gadd(acc, gmul(Pt[n], Pt[sh(n)])); c += pr[n] & pr[sh(n)]
                    vals[n] = acc; truth[n] = c
            else:
                for n2 in range(4, N + 1, 2):
                    acc = (0, 0); c = 0
                    for m in range(2, n2 // 2 + 1):
                        acc = gadd(acc, gmul(Pt[m], Pt[n2 - m])); c += pr[m] & pr[n2 - m]
                    vals[n2] = acc; truth[n2] = c
            report(f"{task} counts", vals, truth, den, budget)
        return
    if task == 'pattern':   # general j-copy pattern n+h_1,...,n+h_j, its own budget
        N = int(sys.argv[2]); hs = [int(v) for v in sys.argv[3].split(',')]; j = len(hs)
        X = N + max(hs); b = blen(X)
        D = (2 * j + 1) * b + math.ceil(j * math.log2(9.8 * (b + 1)) + math.log2(2 * 4 * j)) + 1
        M, p, t = params_for(D, b)
        T0 = time.time(); P, A = tables(M, p, t, X); Pt = prime_tilde(P, A, X)
        den = P.S ** (4 * j); pr = sieve(X)
        vals, truth = {}, {}; acc = (0, 0); c = 0
        for n in range(2, N + 1):
            v = (P.S ** 4, 0)
            for h in hs: v = gmul(v, Pt[n + h]) if n + h >= 2 else (0, 0)
            v = (v[0] // P.S ** 4, v[1] // P.S ** 4)   # exact: first factor was S^4
            acc = gadd(acc, v); c += all(pr[n + h] for h in hs)
            vals[n] = acc; truth[n] = c
        print(f"[pattern {hs}] N={N} X={X} D={D} M={M} p={p} t={t} time {time.time()-T0:.0f}s; final true count {c}")
        report(f"pattern {hs} counts", vals, truth, den,
               2 * X ** (2 * j + 1) * 4 * j * (9.8 * (b + 1)) ** j * 2.0 ** -D / 2)
        return
    if task == 'factors':   # per-factor errors vs the target 2^-D
        X, D = int(sys.argv[2]), int(sys.argv[3]); b = blen(X)
        M, p, t = params_for(D, b); P = Pipeline(M, p, t, b); S = P.S
        mp.mp.prec = 200
        def err(v, true): return abs(mp.mpc(mp.mpf(v[0]) / S, mp.mpf(v[1]) / S) - true)
        ee = max(err(P.Fe(x, d), mp.expjpi(mp.mpf(2 * x) / d)) for d in range(2, 60) for x in range(1, d))
        el = max(err(P.Flog(m), mp.log(m)) for m in range(2, X + 1, max(1, X // 400)))
        ei = max(err(P.Finv(m), 1 / mp.log(m)) for m in range(2, X + 1, max(1, X // 400)))
        print(f"[factors] X={X} D={D} M={M} p={p} t={t}: max err phase 2^{float(mp.log(ee, 2)):.1f},"
              f" log 2^{float(mp.log(el, 2)):.1f}, 1/log 2^{float(mp.log(ei, 2)):.1f}  (target 2^-{D})")
        return
    if task == 'mertens':
        N = int(sys.argv[2]); b = blen(N)
        D = D_needed('mertens', N) + (int(sys.argv[3]) if len(sys.argv) > 3 else 0)   # optional margin
        M, p, t = params_for(D, b)
        T0 = time.time(); P, A = tables(M, p, t, N); mu = mobius(N)
        acc = (0, 0); c = 0; vals, truth = {}, {}
        for n in range(1, N + 1):
            acc = gadd(acc, A[n]); c += mu[n]; vals[n] = acc; truth[n] = c
        print(f"[mertens] N={N} D={D} M={M} p={p} t={t} time {time.time()-T0:.0f}s")
        report("M~(x), x<=N", vals, truth, P.S, N ** 2 * 2.0 ** -D)
        worst = max(abs(Fraction(A[n][0], P.S) - mu[n]) for n in range(1, N + 1))
        print(f"   max_n |mu~(n) - mu(n)| = {float(worst):.3e}")
        return

if __name__ == '__main__':
    main()
