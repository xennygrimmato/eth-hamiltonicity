"""ansatz_cost.py -- exact finite refutations (cost-only relaxation: every shape and every real bond dimension of the given
total cost; network min-cut bounds of restricted flattenings, valid over every field) for three-merge ansaetze on Delta_3.
A piece type with cost vector (c_r, c_c, c_d) has, at bit orientation o, log2 rank <= min_k Phi_{o,k}(c_k)  (Phi = best shape).
An identity f = sum of pieces needs  sum_pieces 2^{min_k Phi_{o,k}(c_k)} >= 2^{|o|}  at every o.
Families tested (symmetry group of Delta_3 fixing the triangle class acts as S_3 on {rows, cols, diags}; sigma'(r,c) = (c-r,-r)
cycles rows->cols->diags and fixes every triangle; the transpose swaps rows<->cols and fixes diags):
  F3(a,b,e): the sigma'-orbit of a type with costs (a,b,e) (T = 3: R, C, D);  game value (a+b+e)/3 (uniform q optimal by symmetry).
  F6(a,b,e): the S_3-orbit (T = 6: two pieces per merge);  game value (a+b+e)/3.
  own-only: R + C + D with own costs (a,a,a) and other merges unconstrained (cost 12 m0 = generic hub cap).
Criterion: V_tot = (a+b+e)/3 + 1.5 log2 T;  rho<1/2 iff < 4.5 m0, any trade iff < 9 m0."""
import numpy as np, itertools, sys
from lib3m import *

def unique_keys(m0):
    idx, X, Y, rk = enumerate_orients(m0)
    K = np.concatenate([rk[:, None]] + [Mg(legs8(X[k], Y[k])) for k in 'rcd'], 1).astype(np.int16)
    K = np.unique(K, axis=0)
    return K[:, 0].astype(float), {k: K[:, 1 + 3 * i: 4 + 3 * i].astype(float) for i, k in enumerate('rcd')}

def Phi(M, rk, a):
    """max t <= rk with ginv(t) <= a (vectorised bisection)."""
    lo = np.zeros_like(rk); hi = rk.copy()
    ok = ginv(M, hi) <= a + 1e-12
    for _ in range(50):
        mid = (lo + hi) / 2; g = ginv(M, mid) <= a + 1e-12
        lo = np.where(g, mid, lo); hi = np.where(g, hi, mid)
    return np.where(ok, rk, lo)

def table(m0, grid):
    rk, M = unique_keys(m0)
    P = {k: np.stack([Phi(M[k], rk, a) for a in grid], 1) for k in 'rcd'}   # (n, len(grid))
    return rk, P

def passes(rk, P, gi_list):
    """gi_list: list of (i_r, i_c, i_d) grid indices, one per piece.  Returns worst slack in log2 terms (min over o of
    log2(sum 2^bound) - rk)."""
    s = np.zeros_like(rk)
    for (ir, ic, idd) in gi_list:
        s += 2.0 ** np.minimum(np.minimum(P['r'][:, ir], P['c'][:, ic]), P['d'][:, idd])
    v = np.log2(s) - rk
    return v.min()

if __name__ == '__main__':
    for m0 in (1, 2):
        h = 0.25 if m0 == 1 else 0.5
        grid = np.arange(0, 12 * m0 + 1e-9, h); G = len(grid); top = G - 1
        rk, P = table(m0, grid)
        print(f'\nN0 = {2**m0}: {len(rk)} distinct orientation keys; grid step {h}; thresholds rho<1/2 {4.5*m0}, trade {9*m0}', flush=True)
        # own-only R+C+D: least a with (a,top,top),(top,a,top),(top,top,a) passing
        for a_i in range(G):
            if passes(rk, P, [(a_i, top, top), (top, a_i, top), (top, top, a_i)]) >= -1e-9:
                print(f'  R+C+D own-cost only (other merges unconstrained): passes first at own cost a = {grid[a_i]} '
                      f'(refuted for every shape with all three own costs < {grid[a_i]})', flush=True); break
        for T, orbit in ((3, lambda a, b, e: [(a, b, e), (e, a, b), (b, e, a)]),
                         (6, lambda a, b, e: [(a, b, e), (e, a, b), (b, e, a), (b, a, e), (a, e, b), (e, b, a)])):
            best = None; nps = 0
            for ai in range(G):
                for bi in range(G):
                    for ei in range(bi, G) if T == 6 else range(G):
                        if best is not None and grid[ai] + grid[bi] + grid[ei] >= best[0]: continue
                        if passes(rk, P, orbit(ai, bi, ei)) >= -1e-9:
                            best = (grid[ai] + grid[bi] + grid[ei], (grid[ai], grid[bi], grid[ei]))
            Vt = best[0] / 3 + 1.5 * np.log2(T)
            print(f'  F{T} (orbit of one type, T = {T}): least passing a+b+e = {best[0]} at {best[1]} -> game {best[0]/3:.4f}, '
                  f'V_tot >= {Vt:.4f}: rho<1/2 {"REFUTED" if Vt >= 4.5*m0 else "OPEN"}; any trade {"REFUTED" if Vt >= 9*m0 else "OPEN"}'
                  f' (any trade needs a+b+e < {3*(9*m0-1.5*np.log2(T)):.3f}; rho<1/2 needs < {3*(4.5*m0-1.5*np.log2(T)):.3f})', flush=True)
            # with own shape cost fixed: a = 3 m0 (bonds (2,2,2) at N0=2, (4,4,4) at N0=4)
            a0 = int(round(3 * m0 / h)); bb = None
            for bi in range(G):
                for ei in range(G):
                    if bb is not None and grid[bi] + grid[ei] >= bb[0]: continue
                    if passes(rk, P, orbit(a0, bi, ei)) >= -1e-9: bb = (grid[bi] + grid[ei], (grid[bi], grid[ei]))
            if bb is None:
                print(f'    own cost {3*m0} (bonds {2**m0}^3): NO other-merge costs pass -> refuted outright', flush=True)
            else:
                Vt = (3 * m0 + bb[0]) / 3 + 1.5 * np.log2(T)
                print(f'    own cost {3*m0}: least passing b+e = {bb[0]} at {bb[1]} -> V_tot >= {Vt:.4f}', flush=True)
