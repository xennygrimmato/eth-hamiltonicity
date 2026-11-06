"""flat_b_T3.py -- N0 = 4, T = 3 piece types, criterion rho < 1/2:  V = V' + 1.5 log2 3 < 9, i.e. V' < theta = 9 - 1.5 log2 3
= 6.6226.  V' = max over the simplex of min_k sum_j x_j c_k(tau_j) is attained on an edge (LP vertex), so V' < theta iff
every type has min(c_row, c_col) < theta and every PAIR satisfies the two-line condition
   (c_col(R) - theta)_+ (c_row(C) - theta)_+ < (theta - c_row(R)) (theta - c_col(C))   for R row-cheap, C column-cheap
(pairs of two row-cheap types are automatic).  Cases: 3 row-cheap: 3 * 2^theta < 2^12 = rank of a row-group flattening ->
impossible; 3 column-cheap: transpose; 1 row + 2 column: transpose of 2 row + 1 column.  Remaining: R1, R2 row-cheap
(a1, a1' < theta, column costs a2, a2'), C column-cheap (b2 < theta, row cost b1).
Cost-only relaxation of the bit-level flattening test (exact upper bounds, all shapes, real bonds); grid h = 1/4 on
(a1, a1', b2, b1), costs rounded up (Phi nondecreasing), and a2, a2' set to the supremum the pair condition allows,
computed at the cell's most favourable corner (so the relaxation is valid for all real costs).  [C]"""
import numpy as np
from flat_bits import enumerate_bits, legs8, STATES
idx, xr, yr, xc, yc, fr, fc, rk = enumerate_bits()
r = rk.astype(np.float32)
ISO = [(4, 3), (2, 5), (1, 6)]
def prep(L8):
    L8 = L8.astype(np.float32)
    Lc = np.minimum(L8[:, 0], L8[:, 7]); M = np.stack([np.minimum(L8[:, i], L8[:, j]) for i, j in ISO], 1)
    return Lc - r, M.min(1) - r, (M.sum(1) - 3 * r) / 3
PR = prep(legs8(xr, yr)); PC = prep(legs8(xc, yc))
def phi(P, a, sel=slice(None)):
    Lc, Mm, Ms = P
    return np.minimum(np.minimum(Lc[sel], Mm[sel] + a), Ms[sel] + 2 * a / 3)
th = 9 - 1.5 * np.log2(3); h = 0.25; TOP = 27.0
gc = np.arange(0, np.ceil(th / h) * h + 1e-9, h); ge = np.arange(0, TOP + 1e-9, h)
A1, A1p, B2, B1 = np.meshgrid(gc, gc, gc, ge, indexing='ij')
m = A1 <= A1p
A1, A1p, B2, B1 = [x[m].astype(np.float32) for x in (A1, A1p, B2, B1)]
def sup_a2(a1):
    lo_a1 = np.maximum(a1 - h, 0); lo_b2 = np.maximum(B2 - h, 0); lo_b1 = B1 - h
    num = np.maximum(th - lo_a1, 0) * np.maximum(th - lo_b2, 0)
    den = lo_b1 - th
    return np.where(den > 0, np.minimum(th + num / np.maximum(den, 1e-30), TOP), TOP).astype(np.float32)
A2 = sup_a2(A1); A2p = sup_a2(A1p)
alive = (A1 - h < th) & (A1p - h < th) & (B2 - h < th)
print(f'theta = {th:.6f}; grid points: {A1.size}', flush=True)
def ok_at(o, ids):
    c1 = np.minimum(phi(PR, A1[ids], o), phi(PC, A2[ids], o))
    c2 = np.minimum(phi(PR, A1p[ids], o), phi(PC, A2p[ids], o))
    c3 = np.minimum(phi(PR, B1[ids], o), phi(PC, B2[ids], o))
    return 2.0 ** c1 + 2.0 ** c2 + 2.0 ** c3 >= 1 - 1e-9
def full(i):
    s = (2.0 ** np.minimum(phi(PR, A1[i]), phi(PC, A2[i])) + 2.0 ** np.minimum(phi(PR, A1p[i]), phi(PC, A2p[i]))
         + 2.0 ** np.minimum(phi(PR, B1[i]), phi(PC, B2[i])))
    k = int(np.argmin(s)); return s[k], k
S = []
while True:
    ids = np.nonzero(alive)[0]
    if len(ids) == 0:
        print(f'no grid point survives after {len(S)} orientations -> T = 3 (2 row-cheap + 1 column-cheap) refuted EXACTLY'); break
    i = ids[len(ids) // 2]
    s, k = full(i)
    if s >= 1 - 1e-9:
        print(f'grid point passes every orientation: a1={A1[i]}, a1p={A1p[i]}, b2={B2[i]}, b1={B1[i]}, a2={A2[i]:.3f}, a2p={A2p[i]:.3f} -> NOT refuted by the cost relaxation')
        # survivors summary
        print(f'  survivors: {len(ids)}; min a1 {A1[ids].min()}, min b2 {B2[ids].min()}, b1 range {B1[ids].min()}..{B1[ids].max()}')
        break
    S.append(k); okm = ok_at(k, ids); alive[ids[~okm]] = False
    print(f'  added orientation rank 2^{rk[k]} {[STATES[q] for q in idx[k]]}; survivors {alive.sum()}', flush=True)
np.save('flat_b_T3_orients.npy', np.array(S))
