"""calibration of the general MC encoder with symmetry breaking on a bilinear map from e5_sweep.structured()
usage: calib.py name k sym(0/1)"""
import sys, itertools, time
from mc_sat import Enc, eval_circuit
from e5_sweep import structured
name, k, sym = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
a, b, T = structured()[name]; c = len(T); n = a + b
f = lambda bits: [sum(bits[u] & bits[a + v] for u in range(a) for v in range(b) if T[o][u][v]) & 1 for o in range(c)]
E = Enc(n, c, k, f, threads=1)
if sym: E.add_symmetry(first_fixed=False)
rows = list(itertools.product([0, 1], repeat=n))
for r in rows: E.add_row(r)
t = time.time(); sat, sol = E.s.solve()
if sat:
    C = E.model_circuit(sol); assert all(eval_circuit(C, r, n, k, c) == f(r) for r in rows)
print(f"{name} k={k} sym={sym}: {'SAT' if sat else 'UNSAT'} {time.time()-t:.1f}s", flush=True)
