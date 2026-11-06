"""floor_assign.py -- sharper finite lower bound for SMALL T: the witnesses must be among the T types.
Roles: CVZ_k (some type has c_k >= 9 m0 - 1.5 log2 T, k = r,c,d; over C) and box roles B_o (some type has c >= g(o,T)
componentwise; flattening, every field).  Each role is realised by one of the T types; a type's cost vector dominates the max of
its roles.  The designer picks the assignment (set partition of the roles into <= T blocks) minimising the game value; so
   V_tot >= min_{assignments} max_x min_k sum_j x_j L_jk + 1.5 log2 T.
Roles are added greedily (from the Pareto set of box corners, the candidate that raises the bound most).  Valid lower bound
for every role set.  Runs N0 = 2 and N0 = 4 for T = 2..6; with CVZ roles and with flattening roles only."""
import numpy as np, itertools, sys
from scipy.optimize import linprog
from lib3m import *
from floor_finite import pareto

def game(L):
    L = np.asarray(L, float); n = len(L)
    if n == 1: return L[0].min()
    A = np.hstack([-L.T, np.ones((3, 1))])
    r = linprog(np.r_[np.zeros(n), -1], A_ub=A, b_ub=np.zeros(3), A_eq=[np.r_[np.ones(n), 0]], b_eq=[1],
                bounds=[(0, None)] * n + [(None, None)], method='highs')
    return -r.fun

def partitions(n, T):
    # set partitions of range(n) into at most T blocks (restricted growth strings)
    def rec(i, a, m):
        if i == n: yield list(a); return
        for b in range(min(m + 1, T)):
            a.append(b); yield from rec(i + 1, a, max(m, b + 1)); a.pop()
    yield from rec(0, [], 0)

def lb(roles, T):
    roles = np.asarray(roles, float); best = np.inf; arg = None
    for a in partitions(len(roles), T):
        blocks = [roles[[i for i in range(len(roles)) if a[i] == b]].max(0) for b in range(max(a) + 1)]
        v = game(blocks)
        if v < best: best, arg = v, a
    return best, arg

if __name__ == '__main__':
    for m0 in (1, 2):
        idx, X, Y, rk = enumerate_orients(m0)
        Ms = {k: Mg(legs8(X[k], Y[k])).astype(float) for k in 'rcd'}
        print(f'\nN0 = {2**m0}: thresholds rho<1/2: V_tot < {4.5*m0};  any trade: V_tot < {9*m0}', flush=True)
        for T in (2, 3, 4, 5, 6):
            lt = np.log2(T); t = rk - lt; ok = t > 0
            G = np.stack([ginv(Ms[k][ok], t[ok]) for k in 'rcd'], 1)
            cand = np.unique(np.round(G, 9), axis=0)
            sc = [cand.min(1)] + [cand @ np.array(w) for w in itertools.product((0, 1, 2, 3, 4), repeat=3) if sum(w) > 0]
            sel = set()
            for s in sc: sel.update(np.argsort(-s)[:15].tolist())
            cand = pareto(cand[sorted(sel)])
            for use_cvz in (True, False):
                roles = [list((9 * m0 - 1.5 * lt) * np.eye(3)[k]) for k in range(3)] if use_cvz else []
                cur = -np.inf
                maxroles = 7 if T <= 3 else 6
                while len(roles) < maxroles:
                    bestc = None
                    for c in cand:
                        v, _ = lb(roles + [list(c)], T)
                        if bestc is None or v > bestc[0] + 1e-12: bestc = (v, list(c))
                    if bestc is None or bestc[0] <= cur + 1e-9: break
                    cur = bestc[0]; roles.append(bestc[1])
                v, a = lb(roles, T)
                tot = v + 1.5 * lt
                print(f'  T = {T}, {"CVZ+flat" if use_cvz else "flat only"}: game LB {v:.4f} -> V_tot >= {tot:.4f} '
                      f'[rho<1/2 {"REFUTED" if tot >= 4.5*m0 - 1e-9 else "open"}; any trade {"REFUTED" if tot >= 9*m0 - 1e-9 else "open"}]'
                      f'  roles {[tuple(np.round(r, 3)) for r in roles]} worst assignment {a}', flush=True)
