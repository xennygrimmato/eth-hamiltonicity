"""Task A: the sign of a valid singleton-blob labelling, labelling by labelling.

(i)   Koszul sign (exterior algebra, random generator order)  ==  paper's sign rule at g = n
      (prod_v [omega_v](R_v) * prod_v sigma_v * (-1)^{interleaving}), random vertex order and
      random crossing order;
(ii)  Koszul sign == (-1)^c  (c = #cycles of mixed arcs; each mixed cycle of length L gives
      (-1)^L from the coefficients and (-1)^{L-1} from reordering, i.e. -1);
(iii) Whitney:  c == Cross + sum_v rot_v  (mod 2), Cross = interleaving parity of mixed chords;
(iv)  the D&C crossing circuit == brute-force crossing parity, on random x in {0,1}^E;
(v)   the O(m) prefix proposal is identically 0 on valid labellings (halving obstruction) and
      differs from Cross;
(vi)  sum over valid labellings of the sign == n * #HC(G).
Prints PASS/FAIL per check.
"""
import random
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc_lib import *  # noqa

rng = random.Random(20261103)
fails = {k: 0 for k in ('i', 'ii', 'iii', 'iv', 'v_zero', 'v_differs', 'vi')}
stats = dict(graphs=0, labellings=0, nonzero_cross=0, rand_x=0, naive_wrong=0)

for trial in range(160):
    n = rng.randint(4, 9)
    maxm = n * (n - 1) // 2
    m = rng.randint(n, min(maxm, 2 * n + (4 if n <= 7 else 1)))
    edges = random_graph(n, m, rng, min_deg2=True)
    r = rng.randrange(n)
    perm = list(range(n)); rng.shuffle(perm)
    pos = {v: perm[v] for v in range(n)}
    Gn = Gens(n, r, rng)
    order = list(range(len(edges))); rng.shuffle(order)
    labs = valid_labellings(n, edges, r)
    stats['graphs'] += 1
    total = 0
    # circuits for (iv)/(v): inputs are fresh variables x_e
    Bc = Builder()
    xin = [Bc.new() if (r not in e) else FALSE for e in edges]
    Xc, _, _ = cross_circuit(Bc, n, edges, pos, xin)
    Nc = naive_cross_circuit(Bc, n, edges, pos, xin)
    for lab in labs:
        stats['labellings'] += 1
        ks = koszul_sign(Gn, n, lab)
        ps = paper_sign(Gn, n, edges, pos, order, lab)
        if ks != ps or ks not in (1, -1):
            fails['i'] += 1
        A = arcs(lab)
        M = len(A)
        c = n_cycles(A)
        if ks != (-1) ** c:
            fails['ii'] += 1
        xs = [1 if (s not in ('N', 'one') and s[0] == 'A') else 0 for s in lab]
        cr = cross_parity_brute(edges, pos, xs)
        stats['nonzero_cross'] += cr
        if (c - cr - rot_sum(pos, A)) % 2:
            fails['iii'] += 1
        asg = [0] * (Bc.nv + 1)
        for k, l in enumerate(xin):
            if l != FALSE:
                asg[l] = xs[k]
        eval_gates(Bc, asg)
        if lit_val(asg, Xc) != cr:
            fails['iv'] += 1
        nv_ = lit_val(asg, Nc)
        if nv_ != 0:
            fails['v_zero'] += 1
        if nv_ != cr:
            stats['naive_wrong'] += 1
        total += ks
    if total != n * hc_count(n, edges):
        fails['vi'] += 1
    # (iv) on arbitrary x (not only valid labellings)
    for _ in range(30):
        xs = [rng.randint(0, 1) if l != FALSE else 0 for l in xin]
        asg = [0] * (Bc.nv + 1)
        for k, l in enumerate(xin):
            if l != FALSE:
                asg[l] = xs[k]
        eval_gates(Bc, asg)
        stats['rand_x'] += 1
        if lit_val(asg, Xc) != cross_parity_brute(edges, pos, xs):
            fails['iv'] += 1

if stats['naive_wrong'] == 0:
    fails['v_differs'] = 1
print("stats:", stats)
for k, v in fails.items():
    print(f"check {k:10s}: {'PASS' if v == 0 else 'FAIL'} ({v} failures)")
print("ALL PASS" if not any(fails.values()) else "SOME FAIL")
