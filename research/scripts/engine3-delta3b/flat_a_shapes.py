"""flat_a_shapes.py -- task (a), shape-exact joint flattening test.  Row pieces R_i = row (2,2,2) AND column triangle
network with integer bonds t_i (product <= 511, i.e. column cost < 9); column pieces C_j = column (2,2,2) AND row network
with bonds t'_j.  Exact test over all 3^9-1 restricted orientations.  [C] exact.
 (1) symmetric families t1 = t2 = t'1 = t'2 = t (transpose-closed);  (2) all pairs {t1, t2} for the row pieces with the
 column pieces the transposes (t'_j = t_j);  report the cheapest passing families and the game value."""
import numpy as np, itertools
from flat_a import O, LR, LC, rk, lb
RK = 2 ** rk
rowR = lb(LR, (1, 1, 1)); colC = lb(LC, (1, 1, 1))
trip = [(a, b, c) for a in range(1, 512) for b in range(1, 512 // a + 1) for c in range(1, 512 // (a * b) + 1) if a * b * c <= 511]
# maximal triples only (bounds are monotone in each bond)
tset = set(trip)
maxi = [t for t in trip if all((t[0] + (k == 0), t[1] + (k == 1), t[2] + (k == 2)) not in tset for k in range(3))]
print(f'integer triples with product <= 511: {len(trip)}, maximal: {len(maxi)}')
def caps(t):
    lg = np.log2(t)
    return 2 ** np.minimum(rowR, lb(LC, lg)), 2 ** np.minimum(colC, lb(LR, lg))
CR = {}; CC = {}
for t in maxi:
    CR[t], CC[t] = caps(t)
sym = []
for t in maxi:
    sl = 2 * CR[t] + 2 * CC[t] - RK
    sym.append((sl.min(), t))
npass = [t for s, t in sym if s >= 0]
print(f'(1) symmetric families: {len(npass)} of {len(maxi)} maximal shapes pass (cost < 9 by construction)')
# min cost over ALL triples (not only maximal) that pass symmetric
allpass = []
for t in trip:
    cr, cc = caps(t)
    if (2 * cr + 2 * cc - RK).min() >= 0: allpass.append(t)
allpass.sort(key=lambda t: np.prod(t))
print(f'    all triples passing (symmetric family): {len(allpass)}; cheapest: {[(t, round(float(np.log2(np.prod(t))),3)) for t in allpass[:12]]}')
if allpass:
    t = allpass[0]; c = np.log2(np.prod(t))
    print(f'    cheapest symmetric passing family: column shape {t}, piece costs (3, {c:.3f}); game value V = 3 + (c-3)/2 + 3 = {3+(c-3)/2+3:.3f} vs E m0 = 9')
# (2) pairs of shapes for the two row pieces (column pieces = transposes, which is forced by tau-symmetry only in the symmetric ansatz)
best = None; cnt = 0
for t1, t2 in itertools.combinations_with_replacement(maxi, 2):
    sl = CR[t1] + CR[t2] + CC[t1] + CC[t2] - RK
    if sl.min() >= 0: cnt += 1
print(f'(2) unordered pairs {{t1,t2}} of maximal shapes (transpose-closed families): {cnt} pass')
