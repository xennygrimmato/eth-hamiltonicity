#!/usr/bin/env python3
"""Clean exact certificate for B = 2 (writes cert_B2.json; also used for the Lean file).

    python3 make_cert_B2.py

Two type classes under the symmetry group (S_3 on v1,v2,v3 together with u1 <-> u2, order 12):
 * acyclic, e.g. (1,1,1): all three pairs in the bucket "r <= rho, r' trivial".  Mixture
     pair v1v2: c via u1 (o=u1,o'=v2) w.p. alpha, c via u2 (o=v1,o'=u2) w.p. 1-alpha
     pair v2v3: c via u1 (o=u1,o'=v3) w.p. 1-alpha, c via u2 (o=v2,o'=u2) w.p. alpha
     pair v1v3: plain routing with hubs (u1,u1) and (u2,u2) w.p. gamma each,
                c via u1 (o=u1,o'=v3) and c via u2 (o=v1,o'=u2) w.p. 1/2-gamma each;
     the u1u2 wire is routed through v2.  Three distinct edge loads
       L1 = 1 + 2a/3 - g/3,  L2 = 1 + a(rho-2/3) + 2g/3,  L3 = 3rho/2 - (a+g)rho + g,
     equalised exactly (a, g rational because rho_hat is rational).  With rho = sqrt(10)/3 the
     common value is 29/27 + 11 sqrt(10)/270 = 1.2029076084 (root of 270x^2 - 580x + 307).
 * cyclic, e.g. (1,1,0): every pair 1/2 via u1, 1/2 via u2; every edge carries (A + rho)/2.
The other types are obtained by relabelling parties; verify.py rechecks every type directly.
"""
import json, itertools
from fractions import Fraction as F
import verify as V

RHO = V.buckets(2)[1][0]           # rational upper bound of sqrt(10)/3 used by verify.py
assert RHO == V.buckets(2)[0][1]


def acyclic_params(rho):
    # solve L1 = L2 = L3 (linear in a, g):  L1-L2 = 0, L1-L3 = 0
    # L1-L2: a(2/3 - rho + 2/3) - g = 0  ->  a(4/3 - rho) = g
    # L1-L3: 1 + 2a/3 - g/3 - 3rho/2 + (a+g)rho - g = 0
    k = F(4, 3) - rho
    # substitute g = k a:  1 - 3rho/2 + a(2/3 - k/3 + rho + k rho - k) = 0
    a = (F(3, 2) * rho - 1) / (F(2, 3) - k / 3 + rho + k * rho - k)
    return a, k * a


BASE = {
    (1, 1, 1): lambda a, g: {
        'mix': [[[0, 0, 3, a], [0, 2, 1, 1 - a]],
                [[0, 0, 4, 1 - a], [0, 3, 1, a]],
                [[0, 0, 0, g], [0, 0, 4, F(1, 2) - g], [0, 1, 1, g], [0, 2, 1, F(1, 2) - g]]],
        'route_u1u2': [0, 1, 0]},
    (1, 1, 0): lambda a, g: {
        'mix': [[[0, 0, 3, F(1, 2)], [0, 2, 1, F(1, 2)]],
                [[0, 0, 4, F(1, 2)], [0, 3, 1, F(1, 2)]],
                [[1, 0, 2, F(1, 2)], [1, 4, 1, F(1, 2)]]],
        'route_u1u2': [1, 0, 0]},
}


def wires_marked(e, kind, o, o2):
    return V.option_wires(e, kind, o, o2, F(100), F(100))      # 100 marks the hub wire


def transport(tau, entry, pi, B=2):
    """Image of a certificate entry under the party permutation pi (a dict on 0..4)."""
    new_mix = [None] * 3
    new_tau = [None] * 3
    for e, (i, j) in enumerate(V.VP):
        f = V.VP.index(tuple(sorted((pi[i], pi[j]))))
        flip = (pi[0] == 1) != (pi[i] > pi[j])           # r <-> r' iff exactly one of the swaps
        new_tau[f] = B - 1 - tau[e] if flip else tau[e]
        out = []
        for kind, o, o2, w in entry['mix'][e]:
            img = {tuple(sorted((pi[x], pi[y]))): l for (x, y), l in wires_marked(e, kind, o, o2).items()}
            cand = [(k2, p, p2) for k2 in (0, 1) for p in range(5) for p2 in range(5)
                    if wires_marked(f, k2, p, p2) == img]
            assert cand, 'no image option'
            out.append([*cand[0], w])
        new_mix[f] = out
    ru = [F(0)] * 3
    for l, x in zip((2, 3, 4), entry['route_u1u2']):
        ru[pi[l] - 2] += F(x)
    return tuple(new_tau), {'mix': new_mix, 'route_u1u2': ru}


def main():
    a, g = acyclic_params(RHO)
    assert 0 <= a <= 1 and 0 <= g <= F(1, 2)
    perms = []
    for p in itertools.permutations((2, 3, 4)):
        for us in ((0, 1), (1, 0)):
            perms.append(dict(zip((0, 1, 2, 3, 4), us + p)))
    types = {}
    for tau, mk in BASE.items():
        ent = mk(a, g)
        for pi in perms:
            t2, e2 = transport(tau, ent, pi)
            types.setdefault(t2, e2)
    assert len(types) == 8
    bk = V.buckets(2)
    out = []
    for tau in sorted(types):
        e = types[tau]
        ent = {'type': list(tau),
               'mix': [[[k, o, o2, str(F(w))] for k, o, o2, w in m] for m in e['mix']],
               'route_u1u2': [str(F(x)) for x in e['route_u1u2']],
               'route_vv': [['1', '0']] * 3}
        out.append(ent)
    exact = max(V.check_type(tuple(t['type']), t, bk) for t in out)
    c = F(int(exact * 10 ** 9) + 1, 10 ** 9)
    data = {'B': 2, 'c': str(c), 'rho_hat': str(RHO), 'alpha': str(a), 'gamma': str(g),
            'exact_max_load': str(exact),
            'units': 'Q = log2 D2 = 1, P = 1/3; loads in these units per block', 'types': out}
    with open('cert_B2.json', 'w') as f:
        json.dump(data, f, indent=1)
    print('alpha', a, float(a), 'gamma', g, float(g))
    print('exact max load', exact, float(exact), 'c', c)


if __name__ == '__main__':
    main()
