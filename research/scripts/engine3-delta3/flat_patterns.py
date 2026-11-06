"""flat_patterns.py -- which two-term identities f_Delta = R + C (R row network with bonds bR, C column network with
bonds bC, bond dims in {1,2,3,4,6,8}) survive the exact finite flattening test of flat_finite.py (all 3^9 restricted
orientations, network min-cut bounds; valid over every field).  Also: R + C + R' and R + C + C' with equal bonds."""
import itertools, numpy as np
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
O = [o for o in itertools.product((0, 1, -1), repeat=9) if any(o)]
cnt = np.zeros((len(O), 4, 3), dtype=int)   # xr, yr, xc, yc
for k, o in enumerate(O):
    for (u, v), oe in zip(edges, o):
        if oe == 0: continue
        a, b = (u, v) if oe == 1 else (v, u)
        cnt[k, 0, a[0]] += 1; cnt[k, 1, b[0]] += 1; cnt[k, 2, a[1]] += 1; cnt[k, 3, b[1]] += 1
rk = np.array([sum(1 for x in o if x) for o in O])
pairs = [(0, 1), (0, 2), (1, 2)]
S = list(itertools.product((0, 1), repeat=3))
def logbounds(x, y, patterns):
    """x,y: (nO,3).  returns (n_patterns, nO) array of log2 of the min-cut bound."""
    A = np.stack([sum((y[:, g] if s[g] == 0 else x[:, g]) for g in range(3)) for s in S], 0)          # (8, nO)
    Bm = np.array([[sum(np.log2(p[k]) for k, (g, h) in enumerate(pairs) if s[g] != s[h]) for s in S] for p in patterns])  # (nP, 8)
    return np.min(A[None, :, :] + Bm[:, :, None], axis=1)
dims = (1, 2, 3, 4, 6, 8)
pats = list(itertools.product(dims, repeat=3))
cost = np.array([sum(np.log2(p)) for p in pats])
LR = logbounds(cnt[:, 0], cnt[:, 1], pats); LC = logbounds(cnt[:, 2], cnt[:, 3], pats)
BR = 2.0 ** LR; BC = 2.0 ** LC; RK = 2.0 ** rk
passing = np.zeros((len(pats), len(pats)), dtype=bool)
for i in range(len(pats)):
    slack = BR[i][None, :] + BC - RK[None, :]
    passing[i] = slack.min(axis=1) >= -1e-9
idx = {p: i for i, p in enumerate(pats)}
def show(pR, pC):
    i, j = idx[pR], idx[pC]
    sl = (BR[i] + BC[j] - RK); k = int(np.argmin(sl))
    print(f'  R{pR} + C{pC}: costs ({cost[i]:.3f}, {cost[j]:.3f})  {"PASSES" if passing[i, j] else "REFUTED"}  (worst slack {sl[k]:.0f} at rank {RK[k]:.0f}, o = {O[k]})')
print('Two-term identities f = R + C, selected patterns:')
for pR, pC in [((2,2,2),(2,2,2)), ((2,2,4),(2,2,4)), ((2,2,4),(2,4,2)), ((2,2,4),(4,2,2)), ((2,4,4),(2,4,4)), ((2,4,4),(4,2,4)),
               ((4,4,4),(4,4,4)), ((8,8,8),(1,1,1)), ((4,4,8),(2,2,2)), ((4,8,8),(1,1,1)), ((4,8,8),(2,2,2)), ((4,8,8),(4,8,8)), ((2,2,2),(8,8,8))]:
    show(pR, pC)
ii, jj = np.nonzero(passing)
tot = cost[ii] + cost[jj]; mx = np.maximum(cost[ii], cost[jj])
k = np.argmin(tot); print(f'min c_R + c_C over passing pairs: {tot[k]:.3f}, e.g. R{pats[ii[k]]} + C{pats[jj[k]]};  #passing pairs with that sum: {int(np.sum(np.abs(tot - tot[k]) < 1e-9))}')
k = np.argmin(mx); print(f'min max(c_R, c_C) over passing pairs: {mx[k]:.3f}, e.g. R{pats[ii[k]]} + C{pats[jj[k]]}')
for c0 in (4, 5, 6, 7, 8, 9):
    sel = np.abs(mx - mx[mx >= c0 - 1e-9].min()) < 1e-9
print('passing pairs with both costs <= 6:', sorted({(pats[a], pats[b]) for a, b in zip(ii, jj) if cost[a] <= 6 + 1e-9 and cost[b] <= 6 + 1e-9})[:20])
print('symmetric-bond pairs R(p)+C(p) passing:', [p for p in pats if passing[idx[p], idx[p]] and p == tuple(sorted(p))])
print('Three terms (equal bonds p):')
for p in [(2,2,2),(2,2,4),(2,4,4),(4,4,4)]:
    i = idx[p]
    for lab, tot3 in (('R+C+R', 2 * BR[i] + BC[i]), ('R+C+C', BR[i] + 2 * BC[i])):
        sl = tot3 - RK; k = int(np.argmin(sl))
        print(f'  {lab} bonds {p}: {"PASSES" if sl[k] >= 0 else "REFUTED"} (worst slack {sl[k]:.0f} at rank {RK[k]:.0f})')
for T in range(2, 9):
    i = idx[(2, 2, 2)]
    best = None
    for a in range(T + 1):
        sl = (a * BR[i] + (T - a) * BC[i] - RK).min()
        if best is None or sl > best[0]: best = (sl, a)
    print(f'  T = {T} terms with bonds (2,2,2), best split {best[1]} row + {T-best[1]} col: worst slack {best[0]:.0f} -> {"PASSES" if best[0] >= 0 else "REFUTED"}')
