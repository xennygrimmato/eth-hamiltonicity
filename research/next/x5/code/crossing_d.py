"""Prop. B.2 with d-dimensional harmonic levels: level = tuple (r_1..r_d), energy eps = sum(2 r_t + 1),
kernels B_d = prod_t B(r_t, n_t), C_d = prod_t C(r_t,n_t), factor (y-1) -> (y-1)^d.  d=1 is the paper.
Checks Psi(1) = +-matching, deg <= Theta = 2(e1+e2), and flattening ranks.  Usage: python3 crossing_d.py d e1 e2 [n]"""
import sys, itertools, random
from crossing import Bv, Cv, det_int, interpolate, rank_Q

def levels(d, emax):
    return [r for r in itertools.product(range(emax), repeat=d) if sum(2*x+1 for x in r) <= emax]
def en(r): return sum(2*x+1 for x in r)
def symbols(d, n, e):
    L = levels(d, e)
    out = []
    for I in itertools.combinations(L, n):
        for J in itertools.combinations(L, n):
            if sum(map(en, I)) + sum(map(en, J)) == e: out.append((I, J))
    return out
def prodk(f, r, n, y):
    p = 1
    for a, b in zip(r, n): p *= f(a, b, y)
    return p
def matrix(d, X, sa, sb, sc, sd):
    y = X*X; f = (y-1)**d
    B = lambda i, j: prodk(Bv, i, j, y); C = lambda i, j: prodk(Cv, i, j, y)
    rows = [('a', i) for i in sa[0]] + [('d', i) for i in sd[0]] + [('c', i) for i in sc[0]] + [('b', i) for i in sb[0]]
    cols = [('a', j) for j in sa[1]] + [('d', j) for j in sd[1]] + [('c', j) for j in sc[1]] + [('b', j) for j in sb[1]]
    def ent(p, i, q, j):
        dl = 1 if i == j else 0; Xi = X**en(i); Xj = X**en(j)
        if p == 'a': return {'a': 0, 'd': C(i, j), 'c': dl*Xi, 'b': f*Xi*B(i, j)}[q]
        if p == 'd': return {'a': -C(j, i), 'd': 0, 'c': Xj*B(j, i), 'b': -dl*Xi}[q]
        if p == 'c': return {'a': -dl*Xi, 'd': -Xi*B(i, j), 'c': 0, 'b': -f*C(i, j)}[q]
        if p == 'b': return {'a': -f*Xj*B(j, i), 'd': dl*Xi, 'c': f*C(j, i), 'b': 0}[q]
    return [[ent(p, i, q, j) for (q, j) in cols] for (p, i) in rows]
if __name__ == '__main__':
    d, e1, e2 = map(int, sys.argv[1:4]); n = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    S1, S2 = symbols(d, n, e1), symbols(d, n, e2); Th = 2*(e1+e2)
    print(f"d={d} e1={e1} e2={e2} n={n} |S1|={len(S1)} |S2|={len(S2)} Theta={Th}")
    co = {}
    for sa in S1:
        for sc in S1:
            for sb in S2:
                for sd in S2:
                    vals = [det_int(matrix(d, X, sa, sb, sc, sd)) for X in range(Th+1)]
                    co[(sa, sb, sc, sd)] = interpolate(vals)
    bad = 0
    for k in random.sample(list(co), min(30, len(co))):
        X = Th+2
        if det_int(matrix(d, X, *k)) != sum(c*X**i for i, c in enumerate(co[k])): bad += 1
    print("degree violations:", bad)
    eps = set(); offm = 0
    for (sa, sb, sc, sd), c in co.items():
        v = sum(c); m = sc == (sa[1], sa[0]) and sd == (sb[1], sb[0])
        if m: eps.add(v)
        elif v != 0: offm += 1
    print("values on matching:", eps, " nonzero off matching:", offm)
    for N in range(Th+1):
        if all(co[k][N] == 0 for k in co): continue
        def flat(rp, cp):
            idx = {'a': S1, 'b': S2, 'c': S1, 'd': S2}
            rows = []
            for r in itertools.product(idx[rp[0]], idx[rp[1]]):
                row = []
                for c in itertools.product(idx[cp[0]], idx[cp[1]]):
                    s = {rp[0]: r[0], rp[1]: r[1], cp[0]: c[0], cp[1]: c[1]}
                    row.append(co[(s['a'], s['b'], s['c'], s['d'])][N])
                rows.append(row)
            return rank_Q(rows)
        print(f"N={N:3d}  rk(ad|bc)={flat('ad','bc'):4d}  rk(ab|cd)={flat('ab','cd'):4d}")
