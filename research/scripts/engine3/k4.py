"""Task D (reduced): K4 with the three 2+2 merges (each merge = one perfect matching kept inside groups, the other
four edges crossing).  A term under merge k is any tensor; its cost is log2 rank across the split (Majdoddin's
(L4) charge; 2 groups so network cost = flattening rank).  Since ranks add within one split, one term per merge
suffices: min S = min { r0 + r1 + r2 : G = T0 + T1 + T2, rank_k(T_k) <= r_k }.
(i) flattening certificate D (cert_flat method);  (ii) GF(2) SAT at N=2 for the least S;  (iii) floors."""
import itertools, sys, time, threading, numpy as np
from pysat.solvers import Solver
from lib import *
from cert_flat import D as Dcert
nodes = [0, 1, 2, 3]; edges = [(0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2)]
merges = [[{0, 1}, {2, 3}], [{0, 2}, {1, 3}], [{0, 3}, {1, 2}]]
cfg = graph_config(nodes, edges, merges, 2)
print("K4, three 2+2 merges: flattening certificate D =", Dcert(cfg)[0], " (rank floor of one split: 4 = |cut|; input floor 3)")
G = graph_tensor(cfg).reshape(-1); NL = 12
def encode(ranks):
    from sat_C import Enc
    E = Enc(); tv = []
    for k, r in enumerate(ranks):
        if r == 0: continue
        gl = group_legs(cfg, merges[k]); A = {}; B = {}
        for lv in itertools.product(range(2), repeat=6):
            for t in range(r): A[(lv, t)] = E.var(); B[(lv, t)] = E.var()
        tv.append((k, r, gl, A, B))
    for idx, e in enumerate(itertools.product(range(2), repeat=NL)):
        lits = []
        for (k, r, gl, A, B) in tv:
            la = tuple(e[i] for i in gl[0]); lb = tuple(e[i] for i in gl[1])
            for t in range(r): lits.append(E.AND([A[(la, t)], B[(lb, t)]]))
        E.XOR_eq(lits, int(G[idx]))
    return E
tlim = float(sys.argv[1]) if len(sys.argv) > 1 else 60
for S in range(1, 17):
    res = []
    for r in itertools.product(range(S + 1), repeat=3):
        if sum(r) != S or list(r) != sorted(r, reverse=True): continue  # symmetric under permuting merges
        E = encode(r)
        with Solver(name='glucose4', bootstrap_with=E.cl) as s:
            tm = threading.Timer(tlim, s.interrupt); tm.start(); ok = s.solve_limited(expect_interrupt=True); tm.cancel()
        res.append((r, {True: 'SAT', False: 'UNSAT', None: 't/o'}[ok]))
    print(f"S={S}:", res, flush=True)
    if any(x[1] == 'SAT' for x in res): break
