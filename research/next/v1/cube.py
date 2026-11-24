# Cube instance: 8 parties (vertices of {0,1}^3), bond dimension N=2, wires on the 4 body diagonals v -- v^7.
# Cuts: the three coordinate bipartitions.  Every wire crosses every cut (rank 16 each).
# Question: is the best three-cut splitting cheaper than the best two-cut splitting?
import sys, itertools, numpy as np
from split import *
N = 2
T = wires(N, [(v, v ^ 7) for v in range(8) if v < (v ^ 7)], 8)
cut = lambda k: [v for v in range(8) if not (v >> k) & 1]
C = [cut(0), cut(1), cut(2)]
print("ranks of Omega across the cuts:", [np.linalg.matrix_rank(flatten(T, c)[0]) for c in C]); sys.stdout.flush()
def search(cuts, tot, restarts, iters=1500):
    k = len(cuts); hits = []
    for comp in itertools.product(range(tot+1), repeat=k):
        if sum(comp) != tot or list(comp) != sorted(comp, reverse=True): continue   # symmetric cuts: sorted profiles
        r = best(T, cuts, list(comp), restarts=restarts, iters=iters)
        print("    ranks", comp, "residual %.2e" % r); sys.stdout.flush()
        if r < 1e-9: hits.append(comp)
    return hits
print("two cuts:")
for tot in [7, 6]:
    print("  total", tot); h = search(C[:2], tot, 6); print("  ->", h)
    if not h: break
print("three cuts:")
for tot in [6, 5]:
    print("  total", tot); h = search(C, tot, 6); print("  ->", h)
    if not h: break
