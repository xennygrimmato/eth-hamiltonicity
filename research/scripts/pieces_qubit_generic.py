"""Same optimisation as pieces_qubit_class_fast.py but with a RANDOM change of basis W (generic
position).  If the optimum agrees with the Krawtchouk case, the qubit class value is governed purely
by dimension counting (Schubert-generic intersections)."""
import sys, math, random
sys.path.insert(0, '.')
import pieces_qubit_class_fast as m
from flint import nmod_mat
P = m.P
def best_random(l, seed=1):
    f1, f2, W = m.setup(l)
    rnd = random.Random(seed)
    W = [[rnd.randrange(P) for j in range(l+1)] for k in range(l+1)]
    Fv = [rnd.randrange(P) for k in range(l+1)]
    lo, hi = 0.0, 4.0*l
    for _ in range(30):
        mid = (lo+hi)/2
        if m.feasible(l, mid, f1, f2, W, Fv): hi = mid
        else: lo = mid
    return hi/(4*l)
for l in [int(a) for a in sys.argv[1:]]:
    print(l, best_random(l), flush=True)
