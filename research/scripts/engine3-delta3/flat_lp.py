"""flat_lp.py -- can ANY finite N0 = 2 identity on Delta_3 pass the exact finite flattening test while the finite
criterion (engine3-open-door.md 1.7) credits it with a trade?  [exact up to LP solver tolerance; certificates printed]

Pieces: types tau = (row bond pattern p, column bond pattern p'), meaning the piece is a row network with bonds p AND a
column network with bonds p' (bond dims in D = {1,2,4,8,16,32,64}); its rank across a restricted orientation o is at most
min(BR_p(o), BC_p'(o)) (network min-cut bounds of flat_finite.py).  Cost vector c(tau) = (sum log2 p, sum log2 p').
An identity f = sum_t pi_t forces  sum_tau n_tau min(BR,BC)(o) >= rank f(o) = 2^{#oriented edges}  for all o.
Finite trade criterion at weighting q (row weight q):  max_t <q,c_t> + log2 T < 9  (E m0 = 9).
For q in a grid Q (all k/m, m <= 12) and each attainable budget B < 9 - 1, LP: min sum n_tau over types with
<q,c> <= B subject to the flattening constraints (constraint generation).  If LP_min(B) >= 2^{9-B} for every B, no identity
whose pieces all have <q,c> <= B and T < 2^{9-B} terms exists; reported as the margin  min_B [B + log2 LP_min(B)] - 9.
Since bonds are restricted to powers of 2 the costs are integers, so for a given identity V = min_q max_t <q,c_t> is
attained at a rational q = k/m with m <= 18; the grid covers m <= 12 (stated as such)."""
import itertools, sys, numpy as np
from fractions import Fraction
from scipy.optimize import linprog
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
O = []
for o in itertools.product((0, 1, -1), repeat=9):
    if not any(o): continue
    first = next(x for x in o if x)
    if first == 1: O.append(o)          # o and -o give the same constraint
cnt = np.zeros((len(O), 4, 3), dtype=int)
for k, o in enumerate(O):
    for (u, v), oe in zip(edges, o):
        if oe == 0: continue
        a, b = (u, v) if oe == 1 else (v, u)
        cnt[k, 0, a[0]] += 1; cnt[k, 1, b[0]] += 1; cnt[k, 2, a[1]] += 1; cnt[k, 3, b[1]] += 1
rk = np.array([sum(1 for x in o if x) for o in O]); RK = 2.0 ** rk
pairs = [(0, 1), (0, 2), (1, 2)]; S = list(itertools.product((0, 1), repeat=3))
def logbounds(x, y, patterns):
    A = np.stack([sum((y[:, g] if s[g] == 0 else x[:, g]) for g in range(3)) for s in S], 0)
    Bm = np.array([[sum(np.log2(p[k]) for k, (g, h) in enumerate(pairs) if s[g] != s[h]) for s in S] for p in patterns])
    return np.min(A[None, :, :] + Bm[:, :, None], axis=1)
D = (1, 2, 4, 8, 16, 32, 64)
pats = list(itertools.product(D, repeat=3)); cost = np.array([int(round(sum(np.log2(p)))) for p in pats])
LR = logbounds(cnt[:, 0], cnt[:, 1], pats); LC = logbounds(cnt[:, 2], cnt[:, 3], pats)
def prune(L):
    keep = []
    order = np.argsort(cost, kind='stable')
    for i in order:
        dom = False
        for j in keep:
            if cost[j] <= cost[i] and np.all(L[j] >= L[i] - 1e-12): dom = True; break
        if not dom:
            # drop previously kept patterns of equal cost dominated by i
            keep = [j for j in keep if not (cost[i] <= cost[j] and np.all(L[i] >= L[j] - 1e-12))] + [i]
    return sorted(keep, key=lambda i: cost[i])
kR = prune(LR); kC = prune(LC)
print(f'orientations (up to reversal) {len(O)}; nondominated row patterns {len(kR)}, column patterns {len(kC)}', flush=True)
print('  nondominated row patterns by cost:', {int(c): [pats[i] for i in kR if cost[i] == c] for c in sorted(set(cost[kR]))})
types = [(i, j) for i in kR for j in kC]
TA = np.array([cost[i] for i, j in types]); TB = np.array([cost[j] for i, j in types])
TI = np.array([i for i, j in types]); TJ = np.array([j for i, j in types])
ER = 2.0 ** LR; EC = 2.0 ** LC
def bnd(sel, cols):
    return np.minimum(ER[TI[sel]][:, cols], EC[TJ[sel]][:, cols])
ALL = np.arange(len(O))
def lp_min(sel):
    """min sum n s.t. sum_tau n_tau bound_tau(o) >= rank f(o) for all o, n >= 0, by constraint generation."""
    act = sorted(set(np.argsort(-RK)[:300].tolist()) | set(np.random.default_rng(0).choice(len(O), 300, replace=False).tolist()))
    while True:
        Ba = bnd(sel, act)
        res = linprog(np.ones(len(sel)), A_ub=-Ba.T, b_ub=-RK[act], bounds=[(0, None)] * len(sel), method='highs')
        if res.status != 0: return np.inf, None
        n = res.x; nz = np.nonzero(n > 1e-12)[0]
        cov = n[nz] @ bnd(sel[nz], ALL)
        viol = np.nonzero(cov < RK * (1 - 1e-9))[0]
        if len(viol) == 0: return res.fun, n
        act = sorted(set(act) | set(viol[np.argsort(cov[viol] / RK[viol])[:500]].tolist()))
import os
QM = int(os.environ.get('QM', '12'))
qs = sorted({Fraction(k, m) for m in range(1, QM + 1) for k in range(0, m + 1)})
worst = None; rows = []
for q in qs:
    qf = float(q); val = qf * TA + (1 - qf) * TB
    margins = []
    for B in sorted(set(np.round(val, 9))):
        if B >= 8 - 1e-9: break
        sel = np.nonzero(val <= B + 1e-9)[0]
        import time; _t = time.time(); m, n = lp_min(sel)
        if os.environ.get('VERB'): print(f'   q={q} B={B}: {len(sel)} types, LP min {m:.4f}, {time.time()-_t:.1f}s', flush=True)
        margin = B + (np.log2(m) if np.isfinite(m) else np.inf) - 9
        margins.append((margin, B, m, sel, n))
    mm = min(margins, key=lambda t: t[0]) if margins else (np.inf, None, None, None, None)
    rows.append((q, mm[0], mm[1], mm[2]))
    if worst is None or mm[0] < worst[0]: worst = (mm[0], q, mm[1], mm[2], mm[3], mm[4])
    print(f'q = {str(q):>5}: min over B of [B + log2 LPmin T(B)] - 9 = {mm[0]:+.4f}  (at B = {mm[1]}, LP min T = {mm[2]})', flush=True)
print(f'\nWORST q = {worst[1]}: margin {worst[0]:+.4f} at B = {worst[2]}, LP min T = {worst[3]:.4f}')
if worst[0] < 0:
    sel, n = worst[4], worst[5]
    print('  flattening-feasible fractional family (types with weight > 1e-6):')
    for k, w in zip(sel, n):
        if w > 1e-6: print(f'    n = {w:.4f}: row {pats[types[k][0]]}, col {pats[types[k][1]]}, costs ({TA[k]}, {TB[k]})')
else:
    print('  => no identity on Delta_3 at N0 = 2 with bond dims powers of 2 passes the flattening test AND the finite trade criterion (for q in the grid).')
