"""One-point MILP [N, exact]: F*(rho) = min over a balanced r-partition (|S_h| = n/r), clause assignment and
<= rho singleton rows per group, of the number of foreign-and-unmeasured occurrences at ONE point.
Since sum_o R_o >= sum_t F_t >= Q F*, every singleton-row design (and every design with rho = 0) has
  max_o R_o >= ceil(Q F* / M).
usage: python3 milp_onepoint.py FAM n rho r timelimit
"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import make_instance, occurrences
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
fam = sys.argv[1]; n, rho, r, tl = map(int, sys.argv[2:6])
cl = make_instance(fam, n, 1); occ = occurrences(cl); m = len(cl)
idx = {}
def var(x):
    if x not in idx: idx[x] = len(idx)
    return idx[x]
rows = []; lo = []; hi = []
def add(c, l, u): rows.append(c); lo.append(l); hi.append(u)
for v in range(n): add({var(('x', v, g)): 1 for g in range(r)}, 1, 1)
for g in range(r): add({var(('x', v, g)): 1 for v in range(n)}, n // r, n // r)
for e in range(m): add({var(('y', e, g)): 1 for g in range(r)}, 1, 1)
for v in range(n):
    for g in range(r): add({var(('w', v, g)): 1, var(('x', v, g)): -1}, -np.inf, 0)
for g in range(r): add({var(('w', v, g)): 1 for v in range(n)}, -np.inf, rho)
for k, (e, v) in enumerate(occ):
    for g in range(r):
        c = {var(('z', k)): 1, var(('y', e, g)): -1, var(('x', v, g)): 1}
        for g2 in range(r): c[var(('w', v, g2))] = c.get(var(('w', v, g2)), 0) + 1
        add(c, 0, np.inf)
N = len(idx); A = lil_matrix((len(rows), N))
for i, c in enumerate(rows):
    for j, a in c.items(): A[i, j] = a
lb = np.zeros(N); ub = np.ones(N); lb[var(('x', 0, 0))] = 1
cobj = np.zeros(N)
for k in range(len(occ)): cobj[var(('z', k))] = 1
res = milp(cobj, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(N), bounds=Bounds(lb, ub),
           options={'time_limit': tl})
print(json.dumps({'fam': fam, 'n': n, 'rho': rho, 'r': r, 'M': len(occ), 'status': res.status,
                  'Fstar': None if res.x is None else round(res.fun), 'dual': getattr(res, 'mip_dual_bound', None)}))
