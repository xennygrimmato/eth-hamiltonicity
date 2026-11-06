"""flat_a_check.py -- flattening status (exact, 3^9-1 orientations) of the specific task-(a) shapes used in als_a.py.
Family: R1, R2 = row (2,2,2) and column network e_R;  C1, C2 = column (2,2,2) and row network e_C (None = unconstrained).
Exact T = 4 game criterion: with U = max(c_col(R_i)) - 3, V = max(c_row(C_j)) - 3: any trade iff 1/U + 1/V > 1/3.  [C]"""
import numpy as np
from flat_a import LR, LC, rk, lb
RK = 2 ** rk; rowR = lb(LR, (1, 1, 1)); colC = lb(LC, (1, 1, 1))
def test(eR, eC):
    capR = 2 ** (rowR if eR is None else np.minimum(rowR, lb(LC, np.log2(eR))))
    capC = 2 ** (colC if eC is None else np.minimum(colC, lb(LR, np.log2(eC))))
    sl = 2 * capR + 2 * capC - RK
    U = np.inf if eR is None else np.log2(np.prod(eR)) - 3; V = np.inf if eC is None else np.log2(np.prod(eC)) - 3
    crit = (1 / U if U > 0 else np.inf) + (1 / V if V > 0 else np.inf) > 1 / 3
    return sl.min(), U, V, crit
for eR, eC in [((6, 6, 6), (6, 6, 6)), ((8, 8, 7), (8, 8, 7)), ((5, 6, 6), (5, 6, 6)), ((7, 8, 8), (7, 8, 8)), ((8, 7, 8), (8, 7, 8)),
               ((4, 4, 3), None), ((4, 4, 2), None), ((3, 3, 3), None), ((4, 4, 4), (4, 4, 4)), ((2, 2, 2), (2, 2, 2)), ((16, 16, 1), (16, 16, 1))]:
    s, U, V, c = test(eR, eC)
    print(f'R: row(2,2,2) & col{eR}; C: col(2,2,2) & row{eC}:  worst flattening slack {s:.0f} ({"passes" if s >= 0 else "REFUTED"}); '
          f'U = {U:.3f}, V = {V:.3f}, game criterion for any trade {"met" if c else "NOT met"}')
