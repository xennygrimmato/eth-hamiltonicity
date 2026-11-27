import numpy as np, itertools, sys
from octa_test import build, check
# fixed integer parameters (rows beta in {0,b2}, columns alpha in {0,a2}, diagonals gamma in {g1,g2}), scan g
cands = [(1,1,2,3),(1,1,3,5),(1,2,3,4),(1,1,2,4),(1,2,3,5),(2,1,3,4),(1,3,2,5),(1,1,3,4),(1,2,4,5),(2,3,1,5),(1,1,-2,3),(1,1,3,7),(1,2,-1,3)]
G = list(range(4, 41))
for (a2, b2, g1, g2) in cands:
    okg, badg = [], []
    for g in G:
        r = check(g, (0, a2 % g), (0, b2 % g), (g1 % g, g2 % g))
        if r is None: badg.append((g, 'deg')); continue
        bad, ms = r
        (okg if not bad else badg).append((g, len(bad)) if bad else g)
    print((a2, b2, g1, g2), "works for", len(okg), "of", len(G), "; fails:", badg)
