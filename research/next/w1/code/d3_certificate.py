"""Dual certificate for the Delta3 star bound: piece with c_1 >= 9 (so h(G1_i)+h(G1_j) >= 9 for all pairs)
must have q.c >= value. Prints the inequalities with nonzero dual multipliers and checks the certificate exactly
(rational rounding of the multipliers, then verifies the combination identity).
usage: python3 d3_certificate.py TYPES q1 q2 q3
"""
import sys, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

TYPES = sys.argv[1]
q = [float(Fraction(x)) for x in sys.argv[2:5]]
nodes = [(a, b, (-a - b) % 3) for a in range(3) for b in range(3)]
n = 9
name = lambda i: 'n%d%d%d' % nodes[i]
merges = [[[i for i, v in enumerate(nodes) if v[k] == g] for g in range(3)] for k in range(3)]
FULL = (1 << n) - 1
canon = lambda S: min(S, FULL ^ S)
cl = sorted(set(canon(S) for S in range(1, FULL)))
var = {S: i for i, S in enumerate(cl)}
nh = len(cl)
def hv(S):
    return None if S in (0, FULL) else var[canon(S)]
rows = {}
def add(terms, label):
    d = {}
    for c, S in terms:
        v = hv(S)
        if v is not None:
            d[v] = d.get(v, 0) + c
    key = tuple(sorted((k, c) for k, c in d.items() if c))
    if key and key not in rows:
        rows[key] = label
for assign in itertools.product(range(4), repeat=n):
    A = sum(1 << i for i in range(n) if assign[i] == 0)
    B = sum(1 << i for i in range(n) if assign[i] == 1)
    C = sum(1 << i for i in range(n) if assign[i] == 2)
    if not A:
        continue
    if B and 'S' in TYPES:
        add([(1, A | B), (-1, A), (-1, B)], ('SA', A, B))
    if B and C:
        if '1' in TYPES: add([(1, A), (-1, A | B), (-1, A | C)], ('L1', A, B, C))
        if '2' in TYPES: add([(2, A), (-1, A | B), (-1, A | C), (-1, B | C)], ('CHLW2', A, B, C))
        if 'H' in TYPES: add([(1, B | C), (-1, A | B), (-1, A | C)], ('L2', A, B, C))
keys = list(rows)
nv = nh + 3
R, Cc, V, b, labels = [], [], [], [], []
for r, key in enumerate(keys):
    for k, c in key:
        R.append(r); Cc.append(k); V.append(c)
    b.append(0); labels.append(rows[key])
nr = len(keys)
grp = lambda G: sum(1 << i for i in G)
def addrow(d, rhs, label):
    global nr
    for k, c in d.items():
        R.append(nr); Cc.append(k); V.append(c)
    b.append(rhs); labels.append(label); nr += 1
for k in range(3):
    gs = [grp(G) for G in merges[k]]
    for g in gs:
        addrow({hv(g): 1, nh + k: -1}, 0, ('t>=h', k, g))
    d = {nh + k: -1}
    for g in gs:
        d[hv(g)] = d.get(hv(g), 0) + 0.5
    addrow(d, 0, ('t>=half sum', k))
gs = [grp(G) for G in merges[0]]
addrow({nh + 0: -1}, -9, ('t1>=9',))
for i, j in itertools.combinations(gs, 2):
    addrow({hv(i): -1, hv(j): -1}, -9, ('pair>=9', i, j))
A = coo_matrix((V, (R, Cc)), shape=(nr, nv)).tocsr()
c = np.zeros(nv); c[nh:] = q
res = linprog(c, A_ub=A, b_ub=np.array(b, float), bounds=[(0, None)] * nv, method='highs')
print('TYPES', TYPES, 'q', q, 'LP value', res.fun)
y = -res.ineqlin.marginals  # y >= 0, c + A^T y >= 0 (reduced costs), value = -b.y
nz = [(y[i], labels[i]) for i in range(nr) if y[i] > 1e-9]
print('nonzero multipliers:', len(nz))
def fmt(S):
    return '{' + ','.join(name(i) for i in range(n) if (S >> i) & 1) + '}'
for w, lab in sorted(nz, key=lambda t: -t[0])[:60]:
    print('  %.4f' % w, lab[0], ' '.join(fmt(x) if isinstance(x, int) and x > 2 else str(x) for x in lab[1:]))
# exact check with rationals: y rounded to denominators <= 48
yr = [Fraction(float(v)).limit_denominator(48) if v > 1e-9 else Fraction(0) for v in y]
Acoo = A.tocoo()
lhs = [Fraction(0)] * nv
for r, k, v in zip(Acoo.row, Acoo.col, Acoo.data):
    if yr[r]:
        lhs[k] += yr[r] * Fraction(v).limit_denominator(4)
qr = [Fraction(x).limit_denominator(12) for x in sys.argv[2:5]]
cr = [Fraction(0)] * nh + qr
reduced = [cr[k] + lhs[k] for k in range(nv)]
ok = all(r >= 0 for r in reduced)
val = -sum(yr[i] * Fraction(b[i]).limit_denominator(4) for i in range(nr))
print('exact certificate: reduced costs all >= 0:', ok, ' certified lower bound =', val)
