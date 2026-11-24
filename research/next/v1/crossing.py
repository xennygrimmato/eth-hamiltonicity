# Two-cut crossing: parties a,b,c,d; wires a-c and b-d; cuts ab|cd ("rows") and ad|bc ("columns").
# f2(N) = min p+q with Omega = X + Y, rank_rows(X)<=p, rank_cols(Y)<=q.   Antisymmetriser gives N(N-1)/2 + 1.
import sys, numpy as np
from split import *
for N in [2, 3, 4]:
    T = wires(N, [(0, 2), (1, 3)], 4); cuts = [[0, 1], [0, 3]]
    print("N =", N, " trivial", N*N, " antisym", N*(N-1)//2 + 1, " N^sqrt2 = %.2f" % N**np.sqrt(2)); sys.stdout.flush()
    ub = N*(N-1)//2 + 1
    for tot in range(ub, max(1, ub-4), -1):
        found = None
        for q in range(0, tot+1):
            p = tot - q
            r = best(T, cuts, [p, q], restarts=12 if N < 4 else 6, iters=1500)
            if r < 1e-9: found = (p, q); break
        print("   total", tot, "->", "EXACT at (p,q)=%s" % (found,) if found else "no exact splitting found"); sys.stdout.flush()
        if not found: break
