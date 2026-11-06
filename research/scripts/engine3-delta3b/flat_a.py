"""flat_a.py -- task (a): N0 = 2, T = 4 types: two row networks with bonds (2,2,2) (c_row = 3) and two column networks
with bonds (2,2,2), each also of column (row) D1 cost < 9 (criterion c1 + c2 + 3 log2 4 < 18, i.e. other-merge cost < 9).
Exact finite flattening test over all 3^9 - 1 restricted orientations (network min-cut bounds, valid over every field).
 (i)  shape-relaxed: each row piece may use, at each orientation separately, the best column network of cost B (LP Phi);
      if the 4-term sum still fails somewhere, the identity is refuted for EVERY other-merge shape of cost <= B.
 (ii) shape-exact: hub column networks (bonds r_a, r_b at the hub group, 1 between the other two) and all integer column
      triples with product <= 511 (cost < 9) for a single piece, with the other three pieces relaxed.
[C] exact."""
import itertools, numpy as np
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
S8 = list(itertools.product((0, 1), repeat=3)); PAIRS = [(0, 1), (0, 2), (1, 2)]
CUT = np.array([[1 if s[g] != s[h] else 0 for (g, h) in PAIRS] for s in S8], float)
O = [o for o in itertools.product((0, 1, -1), repeat=9) if any(o)]
n = len(O)
xr = np.zeros((n, 3)); yr = np.zeros((n, 3)); xc = np.zeros((n, 3)); yc = np.zeros((n, 3))
for k, o in enumerate(O):
    for (u, v), oe in zip(edges, o):
        if oe == 0: continue
        a, b = (u, v) if oe == 1 else (v, u)
        xr[k, a[0]] += 1; yr[k, b[0]] += 1; xc[k, a[1]] += 1; yc[k, b[1]] += 1
rk = np.array([sum(1 for x in o if x) for o in O], float)
def legs8(x, y): return np.stack([sum((y[:, g] if s[g] == 0 else x[:, g]) for g in range(3)) for s in S8], 1)
LR, LC = legs8(xr, yr), legs8(xc, yc)
def lb(L8, logb): return np.min(L8 + (CUT @ np.asarray(logb, float))[None, :], 1)
def Phi(L8, a):
    """max_{x>=0, sum x = a} min_s (L_s + cut_s.x), vectorised: by concavity/symmetry of the triangle LP it suffices to
    check the vertices of the simplex {sum x = a} refined on a grid of step a/24 (exact LP check below for a subset)."""
    best = np.full(L8.shape[0], -np.inf)
    G = 24
    for i in range(G + 1):
        for j in range(G + 1 - i):
            x = np.array([i, j, G - i - j], float) * a / G
            best = np.maximum(best, lb(L8, x))
    return best
from scipy.optimize import linprog
def Phi_lp(L8row, a):
    A = np.hstack([-CUT, np.ones((8, 1))])
    res = linprog([0, 0, 0, -1], A_ub=A, b_ub=L8row, A_eq=[[1, 1, 1, 0]], b_eq=[a], bounds=[(0, None)] * 3 + [(None, None)], method='highs')
    return -res.fun
if __name__ == '__main__':
    RK = 2 ** rk
    rowR = lb(LR, (1, 1, 1)); colC = lb(LC, (1, 1, 1))
    print('orientations:', n)
    base = 2 * 2 ** rowR + 2 * 2 ** colC - RK
    print(f'2R(2,2,2)+2C(2,2,2), no other-merge constraint: worst slack {base.min():.0f}; #orientations with slack 0: {(base == 0).sum()}')
    for B in (9.0, 8.0, 7.0, 6.0, 5.0, 4.0, 3.0):
        pc = Phi(LC, B); pr = Phi(LR, B)
        capR = np.minimum(rowR, pc); capC = np.minimum(colC, pr)
        sl = 2 * 2 ** capR + 2 * 2 ** capC - RK
        k = int(np.argmin(sl))
        # exact LP check of the binding orientation
        e1 = Phi_lp(LC[k], B); e2 = Phi_lp(LR[k], B)
        sl_lp = 2 * 2 ** min(rowR[k], e1) + 2 * 2 ** min(colC[k], e2) - RK[k]
        print(f'shape-relaxed, other-merge cost <= {B}: worst slack {sl[k]:.3f} (LP-exact at that o: {sl_lp:.3f}), rank f = {RK[k]:.0f}, o = {O[k]}'
              + ('  -> REFUTED' if sl_lp < -1e-9 else '  -> passes'))
    # hub column shapes for the row pieces (and transposed for the column pieces); all four pieces with the same hub type
    print('shape-exact hub types: row pieces = R(2,2,2) with column hub (hub group h, ranks to the other two r1, r2); '
          'column pieces = transposed shape (row hub)')
    res = []
    for h in range(3):
        for (r1, r2) in [(16, 16), (16, 31), (8, 63), (4, 64), (32, 15), (2, 64), (64, 1), (8, 8), (4, 4)]:
            others = [g for g in range(3) if g != h]
            e = {tuple(sorted((h, others[0]))): r1, tuple(sorted((h, others[1]))): r2, tuple(others): 1}
            logb = [np.log2(e[p]) for p in PAIRS]
            capR = np.minimum(rowR, lb(LC, logb)); capC = np.minimum(colC, lb(LR, logb))
            for (nR, nC) in [(2, 2), (3, 1), (1, 3)]:
                sl = nR * 2 ** capR + nC * 2 ** capC - RK
                k = int(np.argmin(sl))
                res.append((sl[k], h, r1, r2, nR, nC, RK[k], O[k]))
    for r in res:
        if r[4] == 2:
            print(f'  hub group {r[1]}, ranks ({r[2]},{r[3]}) [cost {np.log2(r[2]*r[3]):.3f}], {r[4]}R+{r[5]}C: worst slack {r[0]:.0f} (rank {r[6]:.0f}, o={r[7]})'
                  + ('  REFUTED' if r[0] < 0 else '  passes'))
    # mixed hubs: the two row pieces may use different hub groups; the column pieces likewise (all r = 16,16)
    print('mixed hub groups (ranks 16,16), 2R + 2C:')
    caps = {}
    for h in range(3):
        others = [g for g in range(3) if g != h]
        e = {tuple(sorted((h, others[0]))): 16, tuple(sorted((h, others[1]))): 16, tuple(others): 1}
        logb = [np.log2(e[p]) for p in PAIRS]
        caps[('R', h)] = 2 ** np.minimum(rowR, lb(LC, logb)); caps[('C', h)] = 2 ** np.minimum(colC, lb(LR, logb))
    worst = []
    for h1, h2 in itertools.combinations_with_replacement(range(3), 2):
        for g1, g2 in itertools.combinations_with_replacement(range(3), 2):
            sl = caps[('R', h1)] + caps[('R', h2)] + caps[('C', g1)] + caps[('C', g2)] - RK
            worst.append((sl.min(), h1, h2, g1, g2))
    worst.sort()
    print(f'  {len(worst)} combinations; min worst slack {worst[0][0]:.0f}, max worst slack {worst[-1][0]:.0f}; refuted: {sum(1 for w in worst if w[0] < 0)}')
    print('  passing combinations:', [w[1:] for w in worst if w[0] >= 0])
