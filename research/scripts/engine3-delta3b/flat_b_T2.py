"""flat_b_T2.py -- task (b): N0 = 4, T = 2 piece types, criterion rho < 1/2 of engine3-open-door.md 1.7:
  V = max_w min_k ( w c_k(tau_1) + (1-w) c_k(tau_2) ) + nu_3 log2 T  <  E m0 / 2 = 9,  nu_3 log2 2 = 1.5.
Exact refutation for EVERY pair of tensors (any shapes, any real bond dims) [C]:
  V < 9 forces min(c_row, c_col) < 7.5 for both types.
  Case A: both types row-cheap (c_row < 7.5): the (row g | other rows) flattening of f has rank 4^6 = 2^12 but a row
          network of cost a has rank <= 2^a there, 2 * 2^7.5 < 2^12.   Case B (both column-cheap): transpose.
  Case C: type 1 row-cheap, type 2 column-cheap.  At every bit orientation o, rank(type 1) <= 2^Phi^row_o(7.5) and
          rank(type 2) <= 2^Phi^col_o(7.5), where Phi_o(a) = max over row (column) triangle networks with sum log bonds = a
          of the min-cut bound = min( L_const, min_g M_g + a, (M_0 + M_1 + M_2 + 2a)/3 )   (closed form of the LP;
          L_const = legs of the trivial cut, M_g = legs of the cut isolating group g).  If at some o
          2^Phi^row_o(7.5) + 2^Phi^col_o(7.5) < 2^rank, Case C is impossible (Phi is nondecreasing, so a < 7.5 is covered).
Also: the largest A such that "row-cheap type of cost < A + column-cheap type of cost < A" is still refuted, i.e. how much
room the refutation has, and the same statement for T = 3, 4 (single-orientation pigeonhole) for comparison."""
import numpy as np
from flat_bits import enumerate_bits, legs8, STATES, logbound, Phi
idx, xr, yr, xc, yc, fr, fc, rk = enumerate_bits()
LR = legs8(xr, yr).astype(float); LC = legs8(xc, yc).astype(float); r = rk.astype(float)
ISO = [(4, 3), (2, 5), (1, 6)]
def Phi_all(L8, a):
    Lc = np.minimum(L8[:, 0], L8[:, 7])
    M = np.stack([np.minimum(L8[:, i], L8[:, j]) for i, j in ISO], 1)
    return np.minimum(np.minimum(Lc, M.min(1) + a), (M.sum(1) + 2 * a) / 3)
# validate the closed form against the LP on random orientations
rng = np.random.default_rng(0)
for k in rng.integers(0, len(r), 200):
    for a in (3.0, 7.5, 11.0):
        assert abs(Phi_all(LR[k:k+1], a)[0] - Phi(LR[k], a)[0]) < 1e-7
print('closed form of Phi validated against the LP on 200 random orientations x 3 costs')
print('Case A: row-group flattening rank of f = 2^12;  two row networks of cost < 7.5: rank < 2 * 2^7.5 = 2^8.5 < 2^12  -> impossible')
def worst(A):
    s = 2 ** (Phi_all(LR, A) - r) + 2 ** (Phi_all(LC, A) - r)
    k = int(np.argmin(s)); return s[k], k
s, k = worst(7.5)
print(f'Case C at cost 7.5: min over {len(r)} bit orientations of (2^Phi_row + 2^Phi_col) / rank f = {s:.6f} at rank 2^{rk[k]}, '
      f'states {[STATES[q] for q in idx[k]]}; Phi_row = {Phi_all(LR[k:k+1],7.5)[0]}, Phi_col = {Phi_all(LC[k:k+1],7.5)[0]}'
      + ('  -> Case C IMPOSSIBLE: T = 2 refuted exactly' if s < 1 else '  -> not refuted'))
lo, hi = 0.0, 18.0
for _ in range(50):
    mid = (lo + hi) / 2
    if worst(mid)[0] < 1: lo = mid
    else: hi = mid
print(f'largest A with Case C refuted (row-cheap cost < A, column-cheap cost < A): A* = {lo:.6f}  (needed: 7.5)')
