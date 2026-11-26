#!/usr/bin/env python3
"""Generate the certificate files cert_B{B}.json (floating-point LP per type, then exact rationalisation).

    python3 make_certs.py B [B ...]

The LP per type is the one of level1_lp.py (hubs at any of the five parties, both pairings, u1u2 routed
via v_l, v_iv_j routed via u_k), with the rational upper rank bounds of verify.buckets(B).  The float
solution is rationalised (weights to denominator <= 10^7, renormalised exactly, routing fractions
recomputed from the exact demands), and c_B is set to the exact maximum load over all types, so that
verify.py passes by construction; verify.py recomputes everything independently of this script.
"""
import sys, json, itertools, gzip
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
import verify as V

OPTS = [(kind, o, o2) for kind in (0, 1) for o in range(5) for o2 in range(5)]
LIM = 10 ** 7


def solve_type(tau, bk):
    nl = 3 * len(OPTS)
    FU, FV, NN = nl, nl + 3, nl + 9
    nv = nl + 10
    dem = {}                       # party pair -> row vector of demand
    for e in range(3):
        r, rp = (float(x) for x in bk[tau[e]])
        for k, (kind, o, o2) in enumerate(OPTS):
            for pr, l in V.option_wires(e, kind, o, o2, r, rp).items():
                dem.setdefault(pr, np.zeros(nv))[e * len(OPTS) + k] += float(l)
    Aub, Aeq, beq = [], [], []
    for (u, v) in V.EDGES:
        row = dem.get((u, v), np.zeros(nv)).copy()
        row[FU + (v - 2)] += 1
        for p, (x, y) in enumerate(V.VP):
            if v in (x, y):
                row[FV + 2 * p + u] += 1
        row[NN] = -1
        Aub.append(row)
    row = dem.get((0, 1), np.zeros(nv)).copy(); row[FU:FU + 3] -= 1; Aeq.append(row); beq.append(0)
    for p, pr in enumerate(V.VP):
        row = dem.get(pr, np.zeros(nv)).copy(); row[FV + 2 * p:FV + 2 * p + 2] -= 1; Aeq.append(row); beq.append(0)
    for e in range(3):
        row = np.zeros(nv); row[e * len(OPTS):(e + 1) * len(OPTS)] = 1; Aeq.append(row); beq.append(1)
    cvec = np.zeros(nv); cvec[NN] = 1
    res = linprog(cvec, A_ub=np.array(Aub), b_ub=np.zeros(6), A_eq=np.array(Aeq), b_eq=beq,
                  bounds=[(0, None)] * nv, method='highs')
    assert res.status == 0
    return res


def rationalise(tau, bk, res):
    x = res.x
    mix = []
    for e in range(3):
        ws = [(OPTS[k], F(max(x[e * len(OPTS) + k], 0.0)).limit_denominator(LIM)) for k in range(len(OPTS))]
        ws = [(o, w) for o, w in ws if w > 0]
        s = sum(w for _, w in ws)
        ws = [(o, w / s) for o, w in ws]
        mix.append([[o[0], o[1], o[2], str(w)] for o, w in ws])
    # exact demands of the non-edge wires, then routing fractions from the float flows
    demand = {}
    for e in range(3):
        r, rp = bk[tau[e]]
        for kind, o, o2, w in mix[e]:
            for pr, l in V.option_wires(e, kind, o, o2, r, rp).items():
                demand[pr] = demand.get(pr, F(0)) + F(w) * l
    nl = 3 * len(OPTS); FU, FV = nl, nl + 3

    def fracs(vals):
        vals = [max(v, 0.0) for v in vals]
        s = sum(vals)
        if s <= 1e-15:
            fr = [F(0)] * len(vals); fr[0] = F(1); return fr
        fr = [F(v / s).limit_denominator(LIM) for v in vals]
        fr[-1] = 1 - sum(fr[:-1])
        if fr[-1] < 0:
            fr = [F(1, len(vals))] * len(vals)
        return fr
    ru = fracs(x[FU:FU + 3])
    rv = [fracs(x[FV + 2 * p:FV + 2 * p + 2]) for p in range(3)]
    return {'type': list(tau), 'mix': mix, 'route_u1u2': [str(f) for f in ru],
            'route_vv': [[str(f) for f in fr] for fr in rv], 'lp_float': res.fun}




def main(B):
    bk = V.buckets(B)
    types, worst_float = [], 0.0
    for tau in itertools.product(range(B), repeat=3):
        res = solve_type(tau, bk)
        worst_float = max(worst_float, res.fun)
        types.append(rationalise(tau, bk, res))
    exact = max(V.check_type(tuple(t['type']), t, bk) for t in types)
    # publish c_B as a short decimal >= the exact maximum
    c = F(int(exact * 10 ** 9) + 1, 10 ** 9)
    assert c >= exact
    data = {'B': B, 'c': str(c), 'units': 'Q = log2 D2 = 1, P = 1/3; loads in these units per block',
            'float_game_value_with_rounded_ranks': worst_float, 'types': types}
    name = 'cert_B%d.json' % B
    opener = open
    if B >= 32:                       # large files are gzipped; verify.py reads both
        name, opener = name + '.gz', gzip.open
    with opener(name, 'wt') as f:
        json.dump(data, f, separators=(',', ':'))
    print('B', B, 'float max', worst_float, 'exact max load', float(exact), 'c', c)


if __name__ == '__main__':
    for b in sys.argv[1:]:
        main(int(b))
