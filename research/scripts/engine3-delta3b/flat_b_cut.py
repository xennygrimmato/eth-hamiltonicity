"""flat_b_cut.py -- task (b), T = 2 at N0 = 4, Case C (type R row-cheap: c_row(R) = a1 < 7.5; type C column-cheap:
c_col(C) = b2 < 7.5; other costs a2 = c_col(R), b1 = c_row(C)).  The exact criterion V < 9 is equivalent to
   (a2 - 7.5)_+ (b1 - 7.5)_+ < (7.5 - a1)(7.5 - b2)                          [R, two-line game, see flat_b_T2.py]
Cost-only relaxation of the flattening test (exact upper bounds, all shapes, all real bonds):
   for every bit orientation o:  2^min(Phi^row_o(a1), Phi^col_o(a2)) + 2^min(Phi^row_o(b1), Phi^col_o(b2)) >= 2^rank(o).
Cutting-plane search on the grid h = 1/4 (costs rounded UP to the grid stay feasible because Phi is nondecreasing; the V
condition is relaxed by h accordingly), so 'no grid point survives' is an EXACT refutation of Case C.  [C]"""
import numpy as np, sys, itertools
from flat_bits import enumerate_bits, legs8, STATES
idx, xr, yr, xc, yc, fr, fc, rk = enumerate_bits()
r = rk.astype(np.float32)
ISO = [(4, 3), (2, 5), (1, 6)]
def prep(L8):
    L8 = L8.astype(np.float32)
    Lc = np.minimum(L8[:, 0], L8[:, 7]); M = np.stack([np.minimum(L8[:, i], L8[:, j]) for i, j in ISO], 1)
    return Lc - r, M.min(1) - r, (M.sum(1) - 3 * r) / 3          # normalised by rank
PR = prep(legs8(xr, yr)); PC = prep(legs8(xc, yc))
def phi(P, a, sel=slice(None)):
    Lc, Mm, Ms = P
    return np.minimum(np.minimum(Lc[sel], Mm[sel] + a), Ms[sel] + 2 * a / 3)
h = 0.25
gc = np.arange(0, 7.5 + h - 1e-9, h)            # cheap costs a1, b2  (a1 < 7.5 rounds up to <= 7.5)
ge = np.arange(0, 27 + 1e-9, h)                 # expensive costs a2, b1 (Phi_o(a) = rank for a >= 1.5 rank, rank <= 18: saturated at 27)
A1, A2, B1, B2 = np.meshgrid(gc, ge, ge, gc, indexing='ij')
A1, A2, B1, B2 = [x.ravel().astype(np.float32) for x in (A1, A2, B1, B2)]
# relaxed V condition (pre-rounding point lies within h below the grid point in each coordinate)
lhs = np.maximum(A2 - h - 7.5, 0) * np.maximum(B1 - h - 7.5, 0)
rhs = (7.5 - A1 + h) * (7.5 - B2 + h)
alive = lhs < rhs
alive &= (A1 < 7.5 + h) & (B2 < 7.5 + h)
print(f'grid points (h = {h}): {A1.size}; satisfying the relaxed V < 9 condition: {alive.sum()}', flush=True)
def ok_at(o, mask):
    capR = np.minimum(phi(PR, A1[mask], o), phi(PC, A2[mask], o))
    capC = np.minimum(phi(PR, B1[mask], o), phi(PC, B2[mask], o))
    return 2.0 ** capR + 2.0 ** capC >= 1 - 1e-9
def full_check(i):
    capR = np.minimum(phi(PR, A1[i]), phi(PC, A2[i])); capC = np.minimum(phi(PR, B1[i]), phi(PC, B2[i]))
    s = 2.0 ** capR + 2.0 ** capC
    k = int(np.argmin(s)); return s[k], k
S = []
it = 0
while True:
    ids = np.nonzero(alive)[0]
    if len(ids) == 0:
        print(f'no grid point survives after {len(S)} orientations -> Case C refuted EXACTLY'); break
    # pick a survivor (the one with the most V-room) and test it on all orientations
    room = (rhs - lhs)[ids]
    i = ids[int(np.argmax(room))]
    s, k = full_check(i)
    if s >= 1 - 1e-9:
        print(f'grid point PASSES every orientation: a1={A1[i]}, a2={A2[i]}, b1={B1[i]}, b2={B2[i]}  -> cost-only relaxation cannot refute'); 
        # report all survivors' extreme points
        break
    S.append(k)
    m = ok_at(k, ids)
    alive[ids[~m]] = False
    it += 1
    print(f'  iter {it}: added orientation rank 2^{rk[k]} states {[STATES[q] for q in idx[k]]}; survivors {alive.sum()}', flush=True)
np.save('flat_b_cut_orients.npy', np.array(S))
