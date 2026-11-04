"""Loophole 1, Theorem D (general straight-line drawings), checked labelling by labelling.

For a generic straight-line drawing D (integer points, distinct x-coordinates so no edge is
vertical, no three points collinear, no three edges through one crossing point) and every valid
labelling eta:
  (a) koszul sign kappa(eta) == (-1)^{c(eta)}                       (Lemma S2, re-checked)
  (b) c(eta) == sum_v N_v(eta) + Q_D(x(eta))  (mod 2)              (Theorem D)
      N_v = [short turn pred(v)->v->succ(v) passes 'north'],  Q_D = #crossing pairs of mixed edges
  (c) the same identity for every 2-regular directed subgraph of K_n with a random drawing
      (all cycle systems, not only those that occur in valid labellings of sparse G)
  (d) ablations: dropping N or dropping Q must fail somewhere; and Q_D + Q_D' is local
      (Q_D(x)+Q_D'(x) == sum_v N_v+N'_v) for two drawings of the same G.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc2_lib import *  # noqa

rng = random.Random(20261104)
fails = dict(a=0, b=0, c=0, d_local=0)
abl = dict(noN=0, noQ=0)
st = dict(graphs=0, labellings=0, Q1=0, Kn_systems=0)
for trial in range(150):
    n = rng.randint(4, 9)
    maxm = n*(n-1)//2
    m = rng.randint(n, min(maxm, 2*n + (4 if n <= 7 else 1)))
    edges = random_graph(n, m, rng, min_deg2=True)
    r = rng.randrange(n)
    P = generic_drawing(n, rng, edges=edges)
    P2 = generic_drawing(n, rng, edges=edges)
    C = crossing_matrix(P, edges); C2 = crossing_matrix(P2, edges)
    Gn = Gens(n, r, rng)
    labs = valid_labellings(n, edges, r)
    st['graphs'] += 1
    for lab in labs:
        st['labellings'] += 1
        A = arcs(lab)
        c = n_cycles(A)
        if trial < 60 and koszul_sign(Gn, n, lab) != (-1)**c:
            fails['a'] += 1
        mix = mixed_edges(edges, lab)
        q = mixed_cross_parity(C, edges, mix); N = north_sum(P, A)
        st['Q1'] += q
        if (c - N - q) % 2: fails['b'] += 1
        if (c - q) % 2: abl['noN'] += 1
        if (c - N) % 2: abl['noQ'] += 1
        q2 = mixed_cross_parity(C2, edges, mix); N2 = north_sum(P2, A)
        if (q + q2 - N - N2) % 2: fails['d_local'] += 1

# (c) all directed 2-regular subgraphs (vertex-disjoint cycle systems) of K_n, n <= 7
for trial in range(12):
    n = rng.randint(5, 7)
    edges = [(i, j) for i in range(n) for j in range(i+1, n)]
    P = generic_drawing(n, rng, edges=edges)
    C = crossing_matrix(P, edges); E = eid_map(edges)
    # all partial permutations without fixed points/2-cycles: choose support S and a derangement
    for k in range(3, n+1):
        for S in itertools.combinations(range(n), k):
            for perm in itertools.permutations(S):
                sig = dict(zip(S, perm))
                if any(sig[v] == v or sig[sig[v]] == v for v in S):
                    continue
                A = list(sig.items())
                mix = [E[frozenset(a)] for a in A]
                c = n_cycles(A)
                st['Kn_systems'] += 1
                if (c - north_sum(P, A) - mixed_cross_parity(C, edges, mix)) % 2:
                    fails['c'] += 1
print('stats:', st)
print('ablations (must be > 0):', abl)
for k, v in fails.items():
    print(f'check {k:8s}: {"PASS" if v == 0 else "FAIL"} ({v} failures)')
ok = not any(fails.values()) and all(abl.values())
print('ALL PASS' if ok else 'SOME FAIL')
