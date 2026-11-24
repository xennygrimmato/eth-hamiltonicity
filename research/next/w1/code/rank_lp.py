"""Rank-inequality LP on K4 and Delta3.

Variables h(S) = log-rank of the bipartition S | rest of a single piece (pure tensor, parties = nodes).
Constraints: all known linear 4-party 0-entropy inequalities on every coarse-graining (A,B,C,D=rest):
  (SA)  h(AB) <= h(A) + h(B)
  (CHLW1) h(A) <= h(AB) + h(AC)                  [Cadney-Huber-Linden-Winter 2014, Thm 1]
  (CHLW2) 2h(A) <= h(AB) + h(AC) + h(BC)         [CHLW Thm 2]
  (SCSH)  h(BC) <= h(AB) + h(AC)                 [CHLW Hyp. 1, proved by Song-Chen-Sun-Hu 2023]
Merge costs: t_k >= max_g h(G^k_g), t_k >= (1/2) sum_g h(G^k_g)  (lower bounds valid for triangle networks;
for two groups t_k = h exactly).
Forced pieces: for each "forcing" constraint we minimise q.t over the polytope, for q on a simplex grid,
then V_lb = min_q max_{forcing in orbit} value.

usage: python3 rank_lp.py k4|d3
"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

which = sys.argv[1]
TYPES = sys.argv[2] if len(sys.argv) > 2 else 'S12H'   # S=subadd, 1=CHLW1, 2=CHLW2, H=SCSH
MODE = sys.argv[3] if len(sys.argv) > 3 else 'jobs'
if which == 'k4':
    n = 4
    # merges = pairings ab|cd, ac|bd, ad|bc ; nodes 0..3 = a,b,c,d
    merges = [[[0, 1], [2, 3]], [[0, 2], [1, 3]], [[0, 3], [1, 2]]]
    edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]  # one wire per edge
    wires = edges
else:
    nodes = [(a, b, (-a - b) % 3) for a in range(3) for b in range(3)]
    n = 9
    idx = {v: i for i, v in enumerate(nodes)}
    merges = [[[i for i, v in enumerate(nodes) if v[k] == g] for g in range(3)] for k in range(3)]
    wires = [(idx[v], idx[tuple((x + 1) % 3 for x in v)]) for v in nodes]  # n -> n+(1,1,1)

FULL = (1 << n) - 1
def canon(S):
    S2 = FULL ^ S
    return min(S, S2)
canon_list = sorted(set(canon(S) for S in range(1, FULL)))
var = {S: i for i, S in enumerate(canon_list)}
nh = len(canon_list)
def hv(S):
    if S == 0 or S == FULL:
        return None
    return var[canon(S)]

rows = set()
def add(terms):
    # terms: list of (coef, set); constraint sum coef*h(set) <= 0
    d = {}
    for c, S in terms:
        v = hv(S)
        if v is None:
            continue
        d[v] = d.get(v, 0) + c
    d = tuple(sorted((k, c) for k, c in d.items() if c != 0))
    if d:
        rows.add(d)

for assign in itertools.product(range(4), repeat=n):
    A = sum(1 << i for i in range(n) if assign[i] == 0)
    B = sum(1 << i for i in range(n) if assign[i] == 1)
    C = sum(1 << i for i in range(n) if assign[i] == 2)
    if A == 0:
        continue
    if B and 'S' in TYPES:
        add([(1, A | B), (-1, A), (-1, B)])
    if B and C:
        if '1' in TYPES: add([(1, A), (-1, A | B), (-1, A | C)])
        if '2' in TYPES: add([(2, A), (-1, A | B), (-1, A | C), (-1, B | C)])
        if 'H' in TYPES: add([(1, B | C), (-1, A | B), (-1, A | C)])
print('constraints', len(rows), 'vars', nh, flush=True)

# t variables after h
nv = nh + 3
R, Cc, V = [], [], []
for r, row in enumerate(rows):
    for k, c in row:
        R.append(r); Cc.append(k); V.append(c)
nr = len(rows)
extra = []  # (dict, rhs)
def grp(G):
    return sum(1 << i for i in G)
for k in range(3):
    gs = [grp(G) for G in merges[k]]
    for g in gs:
        extra.append(({hv(g): 1, nh + k: -1}, 0))
    d = {nh + k: -1}
    for g in gs:
        d[hv(g)] = d.get(hv(g), 0) + 0.5
    extra.append((d, 0))
for d, b in extra:
    for k, c in d.items():
        R.append(nr); Cc.append(k); V.append(c)
    nr += 1
A_base = coo_matrix((V, (R, Cc)), shape=(nr, nv)).tocsr()
b_base = np.zeros(nr)

def cross(S):
    return sum(1 for (u, w) in wires if ((S >> u) & 1) != ((S >> w) & 1))

def solve(q, forcing):
    """forcing: list of (dict coef on vars, rhs) meaning sum >= rhs."""
    from scipy.sparse import vstack, csr_matrix
    Rr, Cr, Vr, br = [], [], [], []
    for i, (d, rhs) in enumerate(forcing):
        for k, c in d.items():
            Rr.append(i); Cr.append(k); Vr.append(-c)
        br.append(-rhs)
    A = vstack([A_base, csr_matrix((Vr, (Rr, Cr)), shape=(len(forcing), nv))])
    b = np.concatenate([b_base, br])
    c = np.zeros(nv); c[nh:] = q
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * nv, method='highs')
    return res.fun, res.x

# forcing families
forcings = {}
# flattening of each bipartition S: some piece has h(S) >= cross(S)
FL = canon_list if n <= 4 else sorted(set(canon(sum(1 << i for i in G)) for M in merges for G in M) | set(canon(1 << i) for i in range(n)))
for S in FL:
    forcings[('flat', S)] = [({hv(S): 1}, cross(S))]
# star (network cost) of merge k: t_k >= E_k where E_k = crossing wires counted per bond; also pair upper bound
for k in range(3):
    gs = [grp(G) for G in merges[k]]
    Ek = sum(cross(g) for g in gs) / 2  # network cost of f_C under merge k (each wire on one bond)
    f = [({nh + k: 1}, Ek)]
    if len(gs) == 2:
        f.append(({hv(gs[0]): 1}, Ek))
    if len(gs) == 3:  # true cost <= h_i + h_j for every pair (path network)
        for i, j in itertools.combinations(gs, 2):
            f.append(({hv(i): 1, hv(j): 1}, Ek))
    forcings[('star', k)] = f

import time
if n > 4 and MODE == 'grid':
    G = 6
    out = {}
    for a in range(G + 1):
        for b in range(G + 1 - a):
            q = np.array([a / G, b / G, (G - a - b) / G])
            out[(a, b, G - a - b)] = solve(q, forcings[('star', 0)])[0]
            print('f_star0', (a, b, G - a - b), round(out[(a, b, G - a - b)], 4), flush=True)
    # V >= min_q max_k f_star_k(q), f_star_k(q) = f_star0(q permuted so that merge k -> merge 0)
    best = None
    for (a, b, c) in out:
        v = max(out[(a, b, c)], out[(b, a, c)], out[(c, b, a)])
        if best is None or v < best[0]:
            best = (v, (a, b, c))
    print('TYPES', TYPES, ': min_q max_k f_star_k(q) =', best[0], 'at q*6 =', best[1])
    sys.exit()
if n > 4:
    jobs = [(('star', 0), (0, 1, 1)), (('star', 0), (1/3, 1/3, 1/3)), (('star', 0), (1, 0, 0)), (('star', 0), (0, 1, 0)),
            (('star', 0), (0.5, 0.5, 0)), (('star', 0), (0, 0.5, 0.5)),
            (('flat', canon(sum(1 << i for i in merges[0][0]))), (1/3, 1/3, 1/3)),
            (('flat', canon(sum(1 << i for i in merges[0][0]))), (0, 0.5, 0.5)),
            (('flat', canon(1)), (1/3, 1/3, 1/3))]
    for key, q in jobs:
        t0 = time.time()
        val, x = solve(np.array(q), forcings[key])
        print(key, 'q =', np.round(q, 3), 'value', round(val, 4), 't =', np.round(x[nh:], 4),
              'h(groups m1) =', [round(x[hv(sum(1 << i for i in G))], 3) for G in merges[0]],
              'h(groups m2) =', [round(x[hv(sum(1 << i for i in G))], 3) for G in merges[1]],
              '(%.0fs)' % (time.time() - t0), flush=True)
    sys.exit()
grid = 12 if n <= 4 else 6
qs = [(a / grid, b / grid, (grid - a - b) / grid) for a in range(grid + 1) for b in range(grid + 1 - a)]
# value table
best = {}
vals = {}
for key, f in forcings.items():
    vals[key] = [solve(np.array(q), f)[0] for q in qs]
Vq = [max(vals[key][i] for key in vals) for i in range(len(qs))]
i0 = int(np.argmin(Vq))
print('min_q max_forcing q.t =', Vq[i0], 'at q =', qs[i0])
iu = qs.index((grid // 3 / grid, grid // 3 / grid, (grid - 2 * (grid // 3)) / grid))
print('uniform q value', Vq[iu])
top = sorted(((vals[key][iu], key) for key in vals), reverse=True)[:6]
for v, key in top:
    print('  uniform: forcing', key, 'value', round(v, 4))
for key in [k for k in forcings if k[0] == 'star']:
    val, x = solve(np.array([1 / 3, 1 / 3, 1 / 3]), forcings[key])
    print('star', key, 'uniform value', round(val, 4), 't =', np.round(x[nh:], 4))
    # also minimise the other two merges' sum
    q = np.array([0.0, 0.0, 0.0]); q[[j for j in range(3) if j != key[1]]] = 1
    val2, x2 = solve(q, forcings[key])
    print('   min of other two t sum =', round(val2, 4), ' t =', np.round(x2[nh:], 4))
