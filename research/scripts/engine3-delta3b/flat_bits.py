"""flat_bits.py -- exact finite flattening analysis of Delta_3 at N0 = 4 (2 bits per string), task (b) of
engine3-open-door.md 3.2a.  [C] exact (network min-cut bounds, valid over every field; rank of a restricted f exact).

Bit-level restricted orientations: each of the 9 edges carries 2 parallel bits; each bit is either fixed (restricted to a
common value at both ends: the bit is removed) or split, with the string bit at the lower node on side X ('+') or on side Y
('-').  Per edge only the counts (p, m) = (#'+' bits, #'-' bits), p + m <= 2, matter: 6 states, 6^9 = 10,077,696 orientations.
The restricted f is a permutation matrix of rank 2^(sum p+m).

Row network with log-bonds x = (x01, x02, x12) (bits):  log2 rank <= phi_o(x) = min_{s in {X,Y}^3} [ sum_g legs of g on the
side opposite s_g + sum_{g<h, s_g != s_h} x_gh ]  (min cut).  Same for columns with the column leg counts.

Outputs:
 (1) the bit-scaled N0=2 certificate o* and the bounds for R(4,4,4), C(4,4,4);
 (2) Phi_o(a) = max_{x >= 0, sum x = a} phi_o(x) (LP), i.e. the best row-cost-a network, at the strongest orientations;
     the T-type pigeonhole refutation of the 3.2a criterion (all piece types, any shapes, any real bond dims);
 (3) the LP flattening floor of flatcert.py evaluated on bit-orientations (N0 = 4) and on fractional orientations
     (N0 -> infinity limit): does 4/9 persist?
"""
import itertools, numpy as np
from scipy.optimize import linprog
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
STATES = [(0, 0), (1, 0), (0, 1), (2, 0), (0, 2), (1, 1)]
S8 = list(itertools.product((0, 1), repeat=3)); PAIRS = [(0, 1), (0, 2), (1, 2)]
CUT = np.array([[1 if s[g] != s[h] else 0 for (g, h) in PAIRS] for s in S8])      # (8,3)

def enumerate_bits():
    idx = np.array(list(itertools.product(range(6), repeat=9)), dtype=np.int8)     # (6^9, 9)
    P = np.array([s[0] for s in STATES], dtype=np.int8)[idx]; M = np.array([s[1] for s in STATES], dtype=np.int8)[idx]
    n = idx.shape[0]
    xr = np.zeros((n, 3), np.int8); yr = np.zeros((n, 3), np.int8); xc = np.zeros((n, 3), np.int8); yc = np.zeros((n, 3), np.int8)
    fr = np.zeros((n, 3), np.int8); fc = np.zeros((n, 3), np.int8)                # net flows (out - in) per group
    for e, (u, v) in enumerate(edges):
        p, m = P[:, e], M[:, e]
        xr[:, u[0]] += p; yr[:, v[0]] += p; xr[:, v[0]] += m; yr[:, u[0]] += m
        xc[:, u[1]] += p; yc[:, v[1]] += p; xc[:, v[1]] += m; yc[:, u[1]] += m
        fr[:, u[0]] += p - m; fr[:, v[0]] -= p - m; fc[:, u[1]] += p - m; fc[:, v[1]] -= p - m
    rk = (P + M).sum(1).astype(np.int16)
    return idx, xr, yr, xc, yc, fr, fc, rk

def legs8(x, y):
    """(n,8): legs opposite to the side of each group, for each side assignment s."""
    return np.stack([sum((y[:, g] if s[g] == 0 else x[:, g]).astype(np.int16) for g in range(3)) for s in S8], 1)

def logbound(L8, logbonds):
    return np.min(L8 + (CUT @ np.asarray(logbonds, float))[None, :], axis=1)

def Phi(L8row, a):
    """max over x>=0, sum x = a of min_s (L_s + cut_s . x)   (LP, one orientation)."""
    # variables x0,x1,x2,t ; maximize t
    A = np.hstack([-CUT, np.ones((8, 1))]); b = L8row.astype(float)
    res = linprog([0, 0, 0, -1], A_ub=A, b_ub=b, A_eq=[[1, 1, 1, 0]], b_eq=[a], bounds=[(0, None)] * 3 + [(None, None)], method='highs')
    return -res.fun, res.x[:3]

if __name__ == '__main__':
    idx, xr, yr, xc, yc, fr, fc, rk = enumerate_bits()
    LR = legs8(xr, yr); LC = legs8(xc, yc)
    print(f'bit-level orientations: {idx.shape[0]}')
    # (1) bit-scaled o*
    ostar = (1, 1, 1, 1, 1, -1, 1, 1, -1)
    k = sum((3 if o == 1 else 4) * 6 ** (8 - e) for e, o in enumerate(ostar))     # state (2,0) for +, (0,2) for -
    assert rk[k] == 18
    for lab, LL in (('row', LR), ('col', LC)):
        print(f'o* (both bits of every edge split as in the N0=2 certificate): rank f = 2^{rk[k]};  {lab} legs per side s: {LL[k].tolist()}')
    for lab, LL, b in (('R(4,4,4)', LR, (2, 2, 2)), ('C(4,4,4)', LC, (2, 2, 2)), ('R(8,8,8)', LR, (3, 3, 3)), ('R(64,64,64)=f', LR, (6, 6, 6))):
        print(f'  {lab}: log2 rank bound at o* = {logbound(LL[k:k+1], b)[0]:.0f}')
    lb = 2 ** logbound(LR, (2, 2, 2)) + 2 ** logbound(LC, (2, 2, 2)) - 2.0 ** rk
    j = int(np.argmin(lb))
    print(f'R(4,4,4)+C(4,4,4), all {idx.shape[0]} bit orientations: worst slack {lb[j]:.0f} (rank f = 2^{rk[j]}, states {[STATES[s] for s in idx[j]]})'
          + ('  -> EXACT REFUTATION' if lb[j] < 0 else ''))
    lb3 = 2 * 2 ** logbound(LR, (2, 2, 2)) + 2 ** logbound(LC, (2, 2, 2)) - 2.0 ** rk
    print(f'R+R+C (4,4,4): worst slack {lb3.min():.0f}')
    # (2) best possible row network of row cost a at o*: Phi(a); same for columns by symmetry
    print('Phi_o*(a) = max log2 rank at o* of a row network of total log-bond a (LP over real bonds):')
    for a in [0, 3, 6, 7, 7.5, 8, 9, 10, 11, 12, 14, 18]:
        pr, xx = Phi(LR[k], a); pc, _ = Phi(LC[k], a)
        print(f'   a = {a:5}: row {pr:.4f} (x = {np.round(xx, 3).tolist()}),  col {pc:.4f}')
    # closed-form inverse: min sum x s.t. min_s (L_s + cut_s.x) >= target.  Sides s and complement give the same cut; the
    # cut of the side isolating group g is x_gh + x_gk; the two constant sides (cut 0) need L >= target.  Requirements
    # A_g = max(0, target - min(L over the two sides isolating g)); min sum = max(max_g A_g, sum_g A_g / 2).
    def inv_all(L8, target):
        const = np.minimum(L8[:, 0], L8[:, 7]).astype(float)
        iso = [(4, 3), (2, 5), (1, 6)]      # sides isolating group 0, 1, 2 (s and its complement)
        A = np.stack([np.maximum(0.0, target - np.minimum(L8[:, a], L8[:, b])) for a, b in iso], 1)
        v = np.maximum(A.max(1), A.sum(1) / 2)
        return np.where(const >= target - 1e-12, v, np.inf)
    # check against the LP at o*
    for a_t in (14, 16, 17, 17.5, 18):
        print(f'  check at o*: min row cost for log rank {a_t}: closed form {inv_all(LR[k:k+1], a_t)[0]:.4f}')
    for T in (2, 3, 4, 6, 8, 16, 64):
        t = np.log2(T)
        v = np.minimum(inv_all(LR, rk - t), inv_all(LC, rk - t))
        j = int(np.argmax(np.where(np.isfinite(v), v, -1)))
        print(f'  T = {T}: forced type has min(c_row, c_col) >= {v[j]:.4f} (states {[STATES[s] for s in idx[j]]}, rank 2^{rk[j]});'
              f' + 1.5 log2 T = {v[j]+1.5*t:.4f} vs 9' + ('  -> REFUTED (every T-type family)' if v[j] + 1.5 * t >= 9 - 1e-9 else '  -> not refuted by one-orientation pigeonhole'))
    # (3) LP flattening floor on bit orientations (flatcert model: d_k = max_G |net flow_G|, in bits; divide by m0 = 2)
    dr = np.abs(fr).max(1); dc = np.abs(fc).max(1); val = np.minimum(dr, dc)
    print(f'flatcert floor at N0 = 4 (bit orientations): D = {val.max()/2} of 9 (in units log2 N0 = 2 bits); histogram (bits): '
          f'{dict(zip(*np.unique(val, return_counts=True)))}')
