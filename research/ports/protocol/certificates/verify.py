#!/usr/bin/env python3
"""Standalone exact verifier for the bucket-game certificates (notes.md, section 2.3).

    python3 verify.py cert_B2.json [cert_B4.json ... cert_B32.json.gz]

Uses only the standard library (fractions, json, math).  No LP solver.

The game (units: log2 D2 = Q = 1, log2 D1 = P = 1/3):
  parties 0 = u1, 1 = u2, 2,3,4 = v1,v2,v3; supply edges u_k v_i (six).
  Pairs e = 0,1,2 are {v1v2}, {v2v3}, {v1v3}; for pair (vi,vj) put (a,c,b,d) = (u1,u2,vi,vj).
  A term of pair e lies in a bucket beta with log-rank bounds (r, r'):
      r  across {a,b}|{c,d},   r' across {a,d}|{b,c}.
  An option is (kind, o, o2) with o, o2 any of the five parties:
      kind 0 ("c"): wires  a-o: P,  b-o: Q,  c-o2: P,  d-o2: Q,  o-o2: r
      kind 1 ("b"): wires  a-o: P,  d-o: Q,  b-o2: Q,  c-o2: P,  o-o2: r'
  (a wire whose two ends coincide costs nothing).
  Wires on a supply edge go on that edge.  The u1u2 wire is routed u1-v_l-u2 (l = 1,2,3) and a
  v_iv_j wire is routed v_i-u_k-v_j (k = 1,2), with rational splitting fractions.  This is the
  routing model of level1_lp.py; the referee's mylp.py also allows longer simple paths, which can
  only lower the value, so certifying in this model is the conservative choice.

Buckets: B equal intervals of x = N/n0 in [0, T], T = 2(P^2+Q^2) = 20/9, x_k = kT/B.  Bucket k has
  r  <= min(sqrt(T - x_k), P+Q),   r' <= min(sqrt(x_{k+1}), P+Q).
Every sqrt is replaced by the RATIONAL UPPER bound up(s) = ceil(D*sqrt(s))/D, D = 10^9, computed with
integer isqrt and checked here (up(s) >= 0 and up(s)^2 >= s).  Rounding up is sound: every load is a
nonnegative combination of P, Q, r, r' with nonnegative weights, so it is monotone in (r, r'), and a
hub wire of log-dimension r_hat >= the true log-rank can always carry the term (pad <rho> into
<rho_hat>).

A certificate file gives, for every type (k_12, k_23, k_13) in [B]^3, a rational mixture over
options for each pair and rational routing fractions.  The verifier checks nonnegativity,
normalisation, that every option is well formed, recomputes all six edge loads exactly, and
checks max load <= c (the claimed bound in the file).  It prints the exact max load.
"""
import sys, json, math, gzip
from fractions import Fraction as F

P, Q = F(1, 3), F(1)
A = P + Q
T = 2 * (P * P + Q * Q)            # 20/9
DEN = 10 ** 9
U1, U2 = 0, 1
VP = [(2, 3), (3, 4), (2, 4)]      # pairs {12}, {23}, {13}
EDGES = [(u, v) for u in (0, 1) for v in (2, 3, 4)]
NAMES = ['u1', 'u2', 'v1', 'v2', 'v3']


def up_sqrt(s):
    """Rational upper bound ceil(DEN*sqrt(s))/DEN for a rational s >= 0, exact integer arithmetic."""
    s = F(s)
    assert s >= 0
    # want smallest integer m with m^2 >= DEN^2 * s
    num = DEN * DEN * s.numerator
    den = s.denominator
    m = math.isqrt(num // den)
    while m * m * den < num:
        m += 1
    r = F(m, DEN)
    assert r >= 0 and r * r >= s
    return r


def buckets(B):
    """[(r_hat, r'_hat)] for k = 0..B-1, rational upper bounds of the corner rank bounds."""
    xs = [T * k / B for k in range(B + 1)]
    return [(min(up_sqrt(T - xs[k]), A), min(up_sqrt(xs[k + 1]), A)) for k in range(B)]


def option_wires(e, kind, o, o2, r, rp):
    i, j = VP[e]
    a, c, b, d = U1, U2, i, j
    if kind == 0:
        ws = [(a, o, P), (b, o, Q), (c, o2, P), (d, o2, Q), (o, o2, r)]
    elif kind == 1:
        ws = [(a, o, P), (d, o, Q), (b, o2, Q), (c, o2, P), (o, o2, rp)]
    else:
        raise ValueError('kind')
    out = {}
    for x, y, l in ws:
        if x != y:
            k = (min(x, y), max(x, y))
            out[k] = out.get(k, F(0)) + l
    return out


def check_type(tau, entry, bk):
    """Return the exact max edge load of the certificate entry for type tau, or raise."""
    demand = {}
    for e in range(3):
        r, rp = bk[tau[e]]
        mix = entry['mix'][e]
        tot = F(0)
        for kind, o, o2, w in mix:
            w = F(w)
            assert w >= 0, 'negative weight'
            assert kind in (0, 1) and o in range(5) and o2 in range(5)
            tot += w
            for k, l in option_wires(e, kind, o, o2, r, rp).items():
                demand[k] = demand.get(k, F(0)) + w * l
        assert tot == 1, 'mixture of pair %d sums to %s' % (e, tot)
    load = {ed: F(0) for ed in EDGES}
    for k, l in demand.items():
        if k in load:                                   # supply edge: carried directly
            load[k] += l
            continue
        if k == (U1, U2):
            fr = entry['route_u1u2']                     # fractions via v1, v2, v3
            assert len(fr) == 3
            fr = [F(x) for x in fr]
            assert all(x >= 0 for x in fr) and sum(fr) == 1, 'u1u2 routing'
            for l_, x in zip((2, 3, 4), fr):
                load[(0, l_)] += x * l
                load[(1, l_)] += x * l
        else:
            p = VP.index(k)
            fr = [F(x) for x in entry['route_vv'][p]]    # fractions via u1, u2
            assert len(fr) == 2
            assert all(x >= 0 for x in fr) and sum(fr) == 1, 'vv routing'
            i, j = k
            for u, x in zip((0, 1), fr):
                load[(u, i)] += x * l
                load[(u, j)] += x * l
    return max(load.values())


def verify(path):
    with (gzip.open(path, 'rt') if path.endswith('.gz') else open(path)) as f:
        data = json.load(f)
    B = data['B']
    c = F(data['c'])
    bk = buckets(B)
    types = {tuple(t['type']): t for t in data['types']}
    worst, wt = F(0), None
    for k0 in range(B):
        for k1 in range(B):
            for k2 in range(B):
                tau = (k0, k1, k2)
                assert tau in types, 'missing type %s' % (tau,)
                m = check_type(tau, types[tau], bk)
                if m > worst:
                    worst, wt = m, tau
    assert len(types) == B ** 3
    ok = worst <= c
    ws = str(worst) if len(str(worst)) < 40 else '(%d-digit fraction)' % len(str(worst.denominator))
    print('%s: B = %d, %d types, exact max load = %s ~ %.12f at type %s; claimed c = %s: %s'
          % (path, B, B ** 3, ws, float(worst), wt, c, 'OK' if ok else 'FAIL'))
    if ok:
        print('   => n*(%d) <= %.10f, rate >= %.10f > 3/4' % (B, float(c), 1 / float(c)))
    return ok and c < F(4, 3)


if __name__ == '__main__':
    ok = all([verify(p) for p in sys.argv[1:]])
    sys.exit(0 if ok else 1)
