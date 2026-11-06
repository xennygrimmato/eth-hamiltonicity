"""cert_b.py -- the three bit orientations found by flat_b_cut.py, written out: which edges are split, rank of f, and the
closed-form bounds Phi^row_o(a), Phi^col_o(a) (log2 rank of the best row / column triangle network of cost a, minus rank).
Then an independent dense check of the T = 2 Case C refutation on a fine grid (h = 1/16) using only these 3 orientations."""
import numpy as np, itertools
from flat_bits import enumerate_bits, legs8, STATES, edges
idx, xr, yr, xc, yc, fr, fc, rk = enumerate_bits()
S = np.load('flat_b_cut_orients.npy')
ISO = [(4, 3), (2, 5), (1, 6)]
LRa, LCa = legs8(xr, yr), legs8(xc, yc)
def coeffs(L8, r):
    Lc = min(L8[0], L8[7]); M = [min(L8[i], L8[j]) for i, j in ISO]
    return Lc - r, min(M) - r, (sum(M) - 3 * r) / 3
for k in S:
    r = int(rk[k])
    desc = []
    for e, s in zip(edges, idx[k]):
        p, m = STATES[s]
        if p + m: desc.append(f'{e[0]}{"->" if p else "<-"}{e[1]}')
    cr = coeffs(LRa[k], r); cc = coeffs(LCa[k], r)
    print(f'orientation: rank f = 2^{r}; split edges (both bits; u->v: string at u on side X): {desc}')
    print(f'   Phi_row(a) - rank = min({cr[0]}, {cr[1]} + a, {cr[2]:.4f} + 2a/3);  Phi_col(a) - rank = min({cc[0]}, {cc[1]} + a, {cc[2]:.4f} + 2a/3)')
# fine-grid recheck with h = 1/16 on the 3 orientations only
h = 1 / 16
def phi(c, a): return np.minimum(np.minimum(c[0], c[1] + a), c[2] + 2 * a / 3)
CR = [coeffs(LRa[k], int(rk[k])) for k in S]; CC = [coeffs(LCa[k], int(rk[k])) for k in S]
gc = np.arange(0, 7.5 + 1e-9, h); ge = np.arange(0, 27 + 1e-9, h)
surv = 0
for a1 in gc:
    for b2 in gc:
        A2, B1 = np.meshgrid(ge, ge, indexing='ij')
        ok = np.ones(A2.shape, bool)
        for cr, cc in zip(CR, CC):
            capR = np.minimum(phi(cr, a1), phi(cc, A2)); capC = np.minimum(phi(cr, B1), phi(cc, b2))
            ok &= 2.0 ** capR + 2.0 ** capC >= 1 - 1e-12
        lhs = np.maximum(A2 - h - 7.5, 0) * np.maximum(B1 - h - 7.5, 0)
        ok &= lhs < (7.5 - a1 + h) * (7.5 - b2 + h)
        surv += ok.sum()
print(f'fine grid h = 1/16 with the 3 orientations: surviving grid points = {surv}' + ('  -> Case C refuted exactly' if surv == 0 else ''))
