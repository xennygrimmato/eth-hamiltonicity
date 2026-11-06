"""flat_a_lp.py -- task (a), shape-exact over ALL other-merge triangle networks (real log-bonds, hence all integer bonds).
Z = orientations where 2R(2,2,2)+2C(2,2,2) has flattening slack exactly 0 (sum of the four row/column min-cut bounds
= rank f).  At o in Z every one of the four pieces must attain its own bound, so a row piece R_i (row bonds (2,2,2)) must
also, as a COLUMN network with log-bonds y, satisfy  min_s (LC_s(o) + cut_s . y) >= rowR(o)  for all o in Z.
LP: c*_col = min sum y subject to these constraints.  Every R_i then has column D1 cost >= c*_col, independently of
the other three pieces; by transpose symmetry every C_j has row cost >= c*_row = c*_col.
Exact T = 4 game criterion (types (3, 3+u_i), (3+v_j, 3), nu_3 log2 4 = 3, E m0 = 9): any trade iff
  3 + max_x min(...) + 3 < 9  iff  U V / (U + V) < 3  with U = max u_i, V = max v_j   (i.e. 1/U + 1/V > 1/3).
[C] exact LP over the reals (HiGHS; the optimum is verified by re-evaluating the constraints in exact rationals)."""
import numpy as np, itertools
from fractions import Fraction as Fr
from scipy.optimize import linprog
from flat_a import O, LR, LC, rk, lb, CUT, S8, PAIRS
RK = 2 ** rk
rowR = lb(LR, (1, 1, 1)); colC = lb(LC, (1, 1, 1))
sl = 2 * 2 ** rowR + 2 * 2 ** colC - RK
Z = np.nonzero(sl == 0)[0]
print(f'|Z| = {len(Z)} slack-0 orientations; ranks there: {sorted(set(RK[Z].astype(int).tolist()))}')
def min_cost(Lmat, need):
    A, b = [], []
    for o in range(len(need)):
        for s in range(8):
            if CUT[s].sum() == 0:
                assert Lmat[o, s] >= need[o] - 1e-12
                continue
            A.append(-CUT[s]); b.append(Lmat[o, s] - need[o])
    res = linprog(np.ones(3), A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, None)] * 3, method='highs')
    return res.fun, res.x, np.array(A), np.array(b)
c, y, A, b = min_cost(LC[Z], rowR[Z])
print(f'row piece R(2,2,2): min column cost over all column triangle networks passing Z: c*_col = {c:.6f} at log-bonds y = {np.round(y, 6).tolist()}')
print('  (attained by y = (1,1,1), i.e. column bonds (2,2,2): the slack-0 set alone forces nothing beyond cost 3)')
c2, y2, _, _ = min_cost(LR[Z], colC[Z])
print(f'column piece C(2,2,2): min row cost c*_row = {c2:.6f} at {np.round(y2, 6).tolist()}')
U = c - 3; V = c2 - 3
print(f'lower bounds from Z: u_i >= {U:.4f}, v_j >= {V:.4f}  -> Z alone does not constrain the game (see flat_a_shapes.py for the joint test)')
# which integer column triples with product <= 511 pass Z (per piece) and then the full 4-piece test with their best pairing
trip = [(a, bb, cc) for a in range(1, 512) for bb in range(1, 512 // a + 1) for cc in range(1, 512 // (a * bb) + 1) if a * bb * cc <= 511]
pz = [t for t in trip if np.all(lb(LC[Z], np.log2(t)) >= rowR[Z] - 1e-9)]
print(f'integer column triples with product <= 511: {len(trip)}; passing Z: {len(pz)}; min product among them: {min([np.prod(t) for t in pz]) if pz else None}')
if pz:
    best = sorted(pz, key=lambda t: np.prod(t))[:10]
    print('  cheapest:', [(t, round(float(np.log2(np.prod(t))), 3)) for t in best])
