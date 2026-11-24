import numpy as np, sys, collections
exec(open("cube2.py").read().split("print(\"crossing")[0])
out = collections.Counter(); bestE = {}
for ranks in [[4, 1, 1], [5, 1, 1], [4, 2, 1], [3, 3, 1], [3, 2, 2], [2, 2, 2]]:
    found = 0
    for seed in range(60):
        res, terms = als_terms(T, C, ranks, seed, iters=1500)
        if res > 1e-10: continue
        found += 1
        M = tuple(tuple(rk(X, S) for X in terms) for S in C)
        E = power_exponent(M) if M not in bestE else bestE[M]; bestE[M] = E; out[(tuple(ranks), M)] += 1
    print(ranks, "exact solutions in 60 seeds:", found); sys.stdout.flush()
for (ranks, M), cnt in sorted(out.items(), key=lambda kv: bestE[kv[0][1]]):
    print(ranks, "x%d" % cnt, "rank matrix", M, "E = %.4f" % bestE[M])
