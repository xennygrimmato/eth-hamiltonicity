"""General XOR-AND MC test with ALL rows encoded up front (no CEGAR). usage: gen_full.py p q r k threads"""
import sys, itertools, time
from mc_sat import Enc, matmul_targets, eval_circuit
p,q,r,k,th = map(int, sys.argv[1:6])
n,m,f = matmul_targets(p,q,r)
E = Enc(n,m,k,f,threads=th)
rows = list(itertools.product([0,1],repeat=n))
for x in rows: E.add_row(x)
t=time.time(); sat,sol = E.s.solve(); dt=time.time()-t
print(f"<{p},{q},{r}> general k={k}: {'SAT' if sat else 'UNSAT'} {dt:.1f}s", flush=True)
if sat:
    C=E.model_circuit(sol); assert all(eval_circuit(C,x,n,k,m)==f(x) for x in rows); print(C)
