#!/usr/bin/env python3
"""Numerical test of the family pointwise large sieve used in T3_family_theorem.md (Prop. LS):
   rho = sum_{Q0<q<=Q} (1/phi(q)) sum*_{chi mod q} |sum_n c_n chi(n)|^2  /  ( H * sum |c_n|^2 ),
   H = sum_{Q0<q<=Q} phi*(q)/phi(q), c_n = (log p / sqrt p) p^{it} on primes p in a block [Q^a, 1.25 Q^a].
Characters via the multi-dimensional DFT of the unit group (primitive ones selected exactly).
Compared with the rigorous MV bound (N/Q0 + 1.5 Q)/H and with K = 1.5/S."""
import numpy as np, sys
from sympy import factorint, primitive_root, primerange, totient
def local_data(p, k):
    """generators and orders of (Z/p^k)^*, and a primitivity test on exponent vectors"""
    m = p ** k
    if p == 2:
        if k == 1: return m, [], [], lambda e: False          # no primitive char mod 2
        if k == 2: return m, [m - 1], [2], lambda e: e[0] == 1
        return m, [m - 1, 5], [2, 2 ** (k - 2)], lambda e: e[1] % 2 == 1
    g = primitive_root(m); o = (p - 1) * p ** (k - 1)
    return m, [g], [o], (lambda e: e[0] % o != 0) if k == 1 else (lambda e: e[0] % p != 0)
def dlog_tables(m, gens, ords):
    """for each unit n mod m, its exponent vector w.r.t. gens"""
    tab = {}
    idx = np.indices(ords).reshape(len(ords), -1).T if ords else np.zeros((1, 0), int)
    for e in idx:
        x = 1
        for gi, ei in zip(gens, e): x = x * pow(int(gi), int(ei), m) % m
        tab[x] = tuple(e)
    return tab
def family_sum(q, n_arr, c_arr):
    f = factorint(q); locs = [local_data(p, k) for p, k in f.items()]
    shape = []; tabs = []
    for m, gens, ords, prim in locs:
        shape += ords; tabs.append(dlog_tables(m, gens, ords))
    if any(len(l[2]) == 0 and l[0] == 2 for l in locs): return 0.0, 0  # 2 || q: no primitive chars
    A = np.zeros(shape if shape else [1], complex)
    for n, c in zip(n_arr, c_arr):
        if np.gcd(n, q) != 1: continue
        ix = []
        for (m, gens, ords, prim), tab in zip(locs, tabs): ix += list(tab[n % m])
        A[tuple(ix)] += c
    F = np.fft.fftn(A) if shape else A          # F[e] = sum_n c_n exp(-2 pi i <e, log n>/ord) : chi_e^{-1}(n) sums
    # primitive mask
    mask = np.ones(F.shape, bool); pos = 0
    grids = np.indices(F.shape) if shape else None
    for m, gens, ords, prim in locs:
        sub = [grids[pos + i] for i in range(len(ords))]
        loc = np.vectorize(lambda *e: prim(e))(*sub) if ords else np.zeros(F.shape, bool)
        mask &= loc; pos += len(ords)
    return float(np.sum(np.abs(F[mask]) ** 2)), int(mask.sum())
if __name__ == '__main__':
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    Q0 = int(Q / np.log(Q)); S = 0.47914534724162244
    qs = [q for q in range(Q0 + 1, Q + 1)]
    phis = {q: int(totient(q)) for q in qs}
    from sympy import divisors, mobius
    phistar = {q: int(sum(mobius(q // d) * totient(d) for d in divisors(q))) for q in qs}
    rng = np.random.default_rng(1)
    print('Q=%d Q0=%d' % (Q, Q0))
    for a in [0.5, 0.8, 0.95, 1.1, 1.3, 1.5, 1.7]:
        lo = int(Q ** a); hi = int(1.25 * Q ** a)
        P = np.array(list(primerange(lo, hi + 1)))
        if len(P) == 0: continue
        for t in [0.0, float(rng.uniform(5 * np.log(Q) ** 2, 10 * np.log(Q) ** 2))]:
            c = np.log(P) / np.sqrt(P) * np.exp(1j * t * np.log(P))
            tot = 0.0; H = 0.0
            for q in qs:
                s, nprim = family_sum(q, P, c); tot += s / phis[q]; H += nprim / phis[q]
                assert nprim == phistar[q], (q, nprim, phistar[q])
            rho = tot / (H * np.sum(np.abs(c) ** 2))
            mvb = (hi / Q0 + 1.5 * Q) / H
            print('  a=%.2f t=%7.1f block [%d,%d] (%d primes)  rho=%.4f   MV bound=%.3f   K=1.5/S=%.3f  H/(S(Q-Q0))=%.3f' % (a, t, lo, hi, len(P), rho, mvb, 1.5 / S, H / (S * (Q - Q0))))
