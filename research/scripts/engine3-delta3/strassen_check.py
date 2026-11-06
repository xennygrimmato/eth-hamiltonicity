"""strassen_check.py -- caveat check: the finite criterion of engine3-open-door.md 1.7, applied verbatim, is met on Delta_3
by Strassen's rank-7 decomposition of each triangle (a triangle at N0 = 2 is <2,2,2> with node legs = 2x2 matrices).
f_Delta = tensor product of the three triangles, so f = sum of 7^3 = 343 terms, each a product over all 9 nodes:
cost 0 under rows AND columns (bonds (1,1,1) both ways).  Criterion: max_t <q,c_t> + log2 T = 0 + log2 343 = 8.42 < 9.
Exact check over Z on all 2^18 entries."""
from d3lib import *
import numpy as np, itertools
# Strassen: sum_{i,j,k} A_ij B_jk C_ki  (trace(ABC)) = sum_{r=1..7} <U_r,A><V_r,B><W_r,C>
# standard Strassen for C = AB: m1..m7; trace form: tr(ABC) = sum_{ijk} A_ij B_jk C_ki
E = lambda i, j: np.eye(2)[:, [i]] @ np.eye(2)[[j], :]
U = [E(0,0)+E(1,1), E(1,0)+E(1,1), E(0,0), E(1,1), E(0,0)+E(0,1), E(1,0)-E(0,0), E(0,1)-E(1,1)]
V = [E(0,0)+E(1,1), E(0,0), E(0,1)-E(1,1), E(1,0)-E(0,0), E(1,1), E(0,0)+E(0,1), E(1,0)+E(1,1)]
# product AB entries: c11=m1+m4-m5+m7, c12=m3+m5, c21=m2+m4, c22=m1-m2+m3+m6 ; tr(ABC) = sum_{ik} (AB)_ik C_ki
Wc = [E(0,0)+E(1,1), E(0,1)-E(1,1), E(1,0)+E(1,1), E(0,0)+E(0,1), E(1,0)-E(0,0), E(1,1), E(0,0)]
# W_r[k,i] = coefficient of m_r in (AB)_ik
Wc = [None]*7
coef = {(0,0): {0:1,3:1,4:-1,6:1}, (0,1): {2:1,4:1}, (1,0): {1:1,3:1}, (1,1): {0:1,1:-1,2:1,5:1}}
for r in range(7):
    M = np.zeros((2,2))
    for (i,k), d in coef.items():
        if r in d: M[k,i] = d[r]
    Wc[r] = M
T = np.einsum('ij,jk,ki->ijk'.replace('->ijk','->ijk'), np.ones((2,2)), np.ones((2,2)), np.ones((2,2)))
full = np.zeros((2,)*6)   # A_ij B_jk C_ki indicator form: tensor over (i,j),(j,k),(k,i)
for i, j, k in itertools.product((0,1), repeat=3): full[i,j,j,k,k,i] = 1
S = sum(np.einsum('ab,cd,ef->abcdef', U[r], V[r], Wc[r]) for r in range(7))
print('Strassen trace identity for the triangle tensor (exact over Z):', np.array_equal(S, full))
# map to Delta_3: triangle s has nodes p0=(0,s), p1=(1,s-1), p2=(2,s-2); strings: p0 holds (to p1, to p2), etc.
cfg = delta3(); f = cfg.target()
def node_leg_axes(v):
    return [k for k, (w, _) in enumerate(cfg.strings) if w == v]
def partner_axis(v, w):
    e = cfg.edges.index(tuple(sorted((v, w)))); return cfg.sidx[(v, e)]
terms_total = np.zeros((2,)*18); nterms = 0
facs = []
for s in range(3):
    p = [(0, s % 3), (1, (s - 1) % 3), (2, (s - 2) % 3)]
    # A on p0 indexed (i,j): i = string p0->p2 (shared with C's k... ) choose: A_ij at p0 with i=bit(p0,p2), j=bit(p0,p1)
    # B_jk at p1 with j=bit(p1,p0), k=bit(p1,p2); C_ki at p2 with k=bit(p2,p1), i=bit(p2,p0)
    ax = [(partner_axis(p[0], p[2]), partner_axis(p[0], p[1])), (partner_axis(p[1], p[0]), partner_axis(p[1], p[2])), (partner_axis(p[2], p[1]), partner_axis(p[2], p[0]))]
    facs.append([(ax, (U[r], V[r], Wc[r])) for r in range(7)])
letters = 'abcdefghijklmnopqr'
for combo in itertools.product(range(7), repeat=3):
    ops = []; subs = []
    for s, r in enumerate(combo):
        ax, mats = facs[s][r]
        for (a1, a2), M in zip(ax, mats):
            ops.append(M); subs.append(letters[a1] + letters[a2])
    terms_total += np.einsum(','.join(subs) + '->' + letters, *ops); nterms += 1
print(f'f_Delta = sum of {nterms} product terms (each a product over all 9 nodes): exact over Z:', np.array_equal(np.rint(terms_total), f), ' max err', np.abs(terms_total - f).max())
print(f'finite criterion value: 0 + log2({nterms}) = {np.log2(nterms):.4f} < 9  -> rho_Delta <= {np.log2(nterms)/9:.4f} by the criterion as stated')
print(f'per triangle alone: log2 7 = {np.log2(7):.4f} < 3; asymptotically (pieces = rank-one terms of <N,N,N>): rho <= omega/3 < 0.7909')
