"""General XOR-AND MC for <2,2,2>, k gates, first gate fixed to an orbit representative plane.
WLOG all gate-input constants are 0 (a constant only changes a gate by an affine combination of
inputs/earlier gates, which every consumer absorbs). usage: gen_orbit.py k i0 i1 threads"""
import sys, itertools, time, json
from mc_sat import Enc, matmul_targets, eval_circuit
k, i0, i1, th = map(int, sys.argv[1:5])
SYM = len(sys.argv) > 5 and sys.argv[5] == 'sym'
orbs = json.load(open('plane_orbits.json'))
n, m, f = matmul_targets(2, 2, 2)
rows = list(itertools.product([0, 1], repeat=n))
for oi in range(i0, min(i1, len(orbs))):
    pk, sz = orbs[oi]
    l1, l2 = pk[0], pk[1]
    E = Enc(n, m, k, f, threads=th)
    for j in range(k):
        for s_ in range(2):
            E.s.add_clause([-E.c[j][s_][0]])
    for s_, l in ((0, l1), (1, l2)):
        for i in range(n):
            # input bit i of mc_sat ordering: A(i,j)=2i+j, B=4+2j+k -- same as orbits.py
            E.s.add_clause([E.c[0][s_][1 + i] if (l >> i) & 1 else -E.c[0][s_][1 + i]])
    if SYM: E.add_symmetry(first_fixed=True)
    for x in rows: E.add_row(x)
    t = time.time(); sat, sol = E.s.solve(); dt = time.time() - t
    print(f"orbit {oi} plane {pk} size {sz}: {'SAT' if sat else 'UNSAT'} {dt:.1f}s", flush=True)
    if sat:
        C = E.model_circuit(sol); assert all(eval_circuit(C, x, n, k, m) == f(x) for x in rows)
        json.dump(C, open(f'circ222_k{k}_orbit{oi}.json', 'w'))
