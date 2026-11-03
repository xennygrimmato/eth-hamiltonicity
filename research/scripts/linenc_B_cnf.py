"""Task B: the CNF phi(G, r, order) and its designated variable z.

Checks, by an exact DPLL model counter (linenc_lib.count_models):
  (1) #(phi & ~z) - #(phi & z) == n * #HC(G)                         [full encoding]
  (2) #phi == number of valid labellings (parsimony of all auxiliary variables)
  (3) clause width <= 3
  (4) ablations, each must fail on at least one instance:
        no_cross  (drop the interleaving term),
        no_touch  (drop the local 'touching' correction b_e = a_f inside Cross),
        no_rot    (drop the local rotation sign, the analogue of prod sigma_v),
        add_M     (add a spurious (-1)^{#mixed edges}),
        naive     (the O(m) prefix circuit in place of Cross).
Prints PASS/FAIL.
"""
import random
import sys
import os
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc_lib import *  # noqa

rng = random.Random(7)
VARIANTS = ['full', 'no_cross', 'no_touch', 'no_rot', 'add_M', 'naive']
wrong = {v: 0 for v in VARIANTS}
fails = dict(identity=0, parsimony=0, width=0)
inst = []
NTRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
t0 = time.time()
for trial in range(NTRIALS):
    n = rng.randint(6, 9)
    maxm = n * (n - 1) // 2
    m = rng.randint(n + 1, min(maxm, 2 * n + 1))
    edges = random_graph(n, m, rng, min_deg2=True)
    r = rng.randrange(n)
    perm = list(range(n)); rng.shuffle(perm)
    pos = {v: perm[v] for v in range(n)}
    target = n * hc_count(n, edges)
    nlab = len(valid_labellings(n, edges, r))
    row = dict(n=n, m=len(edges), target=target)
    for var in VARIANTS:
        B, z, prim, info = build_cnf(n, edges, r, pos, var)
        neg = count_models(B.nv, B.clauses, prim, [-z])
        posc = count_models(B.nv, B.clauses, prim, [z])
        gap = neg - posc
        if var == 'full':
            row.update(vars=B.nv, clauses=len(B.clauses), gap=gap, models=neg + posc, **info)
            if gap != target:
                fails['identity'] += 1
            if neg + posc != nlab:
                fails['parsimony'] += 1
            if max(len(c) for c in B.clauses) > 3:
                fails['width'] += 1
        elif gap != target:
            wrong[var] += 1
    inst.append(row)
    print(row, flush=True)

print(f"{NTRIALS} instances, {time.time() - t0:.0f}s")
for k, v in fails.items():
    print(f"check {k:10s}: {'PASS' if v == 0 else 'FAIL'} ({v} failures)")
for var in VARIANTS[1:]:
    print(f"ablation {var:9s}: wrong on {wrong[var]}/{NTRIALS} -> {'PASS' if wrong[var] else 'FAIL'}"
          " (must be wrong somewhere)")
ok = not any(fails.values()) and all(wrong[v] for v in VARIANTS[1:])
print("ALL PASS" if ok else "SOME FAIL")
