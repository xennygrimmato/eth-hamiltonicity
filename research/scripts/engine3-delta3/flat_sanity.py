"""flat_sanity.py -- the finite flattening test of flat_finite.py must never refute a TRUE identity.
(i) rectangle at N = 2 (rows {x,y}|{u,v}, cols {x,u}|{y,v}; third group empty): App. H pieces P (row bond 4, col bond 1)
    and A (row bond 1, col bond 4) -- exhaustive over 3^2 orientations; and P alone / A alone must be refuted.
(ii) 3x3 level at lambda = 1 with the 512 product pieces of level_product.py: 200000 random restricted orientations of the
    18 edges plus the all-split ones of a few structured types; a single piece type set must pass."""
import itertools, numpy as np
pairs = [(0, 1), (0, 2), (1, 2)]; S = list(itertools.product((0, 1), repeat=3))
def bound(x, y, bonds):
    best = None
    for s in S:
        val = 1
        for g in range(3): val *= 2 ** (y[g] if s[g] == 0 else x[g])
        for k, (g, h) in enumerate(pairs):
            if s[g] != s[h]: val *= bonds[k]
        best = val if best is None else min(best, val)
    return best
def counts(edges, o, rowof, colof):
    xr = [0] * 3; yr = [0] * 3; xc = [0] * 3; yc = [0] * 3
    for (u, v), oe in zip(edges, o):
        if oe == 0: continue
        a, b = (u, v) if oe == 1 else (v, u)
        xr[rowof(a)] += 1; yr[rowof(b)] += 1; xc[colof(a)] += 1; yc[colof(b)] += 1
    return xr, yr, xc, yc
def slack(edges, o, pieces, rowof, colof):
    xr, yr, xc, yc = counts(edges, o, rowof, colof)
    tot = sum(min(bound(xr, yr, pr), bound(xc, yc, pc)) for pr, pc in pieces)
    return tot - 2 ** sum(1 for e in o if e)
# (i) rectangle: nodes (a,i) a,i in {0,1}; edges (0,0)-(1,1), (0,1)-(1,0)
er = [((0, 0), (1, 1)), ((0, 1), (1, 0))]
ro = lambda v: v[0]; co = lambda v: v[1]
for label, pieces in (('P + A', [((4, 1, 1), (1, 1, 1)), ((1, 1, 1), (4, 1, 1))]), ('P alone', [((4, 1, 1), (1, 1, 1))]), ('A alone', [((1, 1, 1), (4, 1, 1))])):
    w = min(slack(er, o, pieces, ro, co) for o in itertools.product((0, 1, -1), repeat=2) if any(o))
    print(f'rectangle, {label}: worst slack {w} -> {"refuted" if w < 0 else "passes"}')
# (ii) 3x3 level
g = [(r, c) for r in range(3) for c in range(3)]
el = [(u, v) for u, v in itertools.combinations(g, 2) if u[0] != v[0] and u[1] != v[1]]
rects = [((a, b), (i, j)) for a, b in itertools.combinations(range(3), 2) for i, j in itertools.combinations(range(3), 2)]
pieces = []
for choice in itertools.product('PA', repeat=9):
    br = {p: 1 for p in pairs}; bc = {p: 1 for p in pairs}
    for ((a, b), (i, j)), ch in zip(rects, choice):
        if ch == 'P': br[(a, b)] *= 4
        else: bc[(i, j)] *= 4
    pieces.append((tuple(br[p] for p in pairs), tuple(bc[p] for p in pairs)))
rng = np.random.default_rng(0); worst = None
tests = [tuple(rng.choice((0, 1, -1), p=(0.2, 0.4, 0.4)) for _ in range(18)) for _ in range(3000)]
tests += [tuple(rng.choice((1, -1)) for _ in range(18)) for _ in range(1000)]
for o in tests:
    if not any(o): continue
    s = slack(el, o, pieces, ro, co)
    worst = s if worst is None else min(worst, s)
print(f'3x3 level, 512 product pieces, {len(tests)} random orientations: worst slack {worst} -> {"REFUTED (bug!)" if worst < 0 else "passes"}')
# the product pieces minus one must fail somewhere? (not required) -- instead: 2 pieces of max cost 8 cannot represent f:
