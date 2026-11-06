"""Exact optimum (or MILP bounds) of R for the singleton-measurement class [N, HiGHS via scipy.milp]:
min R s.t. balanced r-partitions per point (|S_{t,h}| = n/r), clause assignments, <= rho singleton rows
per group per point, and every occurrence foreign-and-unmeasured at <= R points.
In this class R_o is exactly that count (coordinatewise decoupling), so the MILP optimum is the exact
min R over all singleton-row designs.  Symmetry breaking: variable 0 in group 0 at every point.
usage: python3 milp_singleton.py FAM n Q rho r timelimit
"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import make_instance, occurrences
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
fam = sys.argv[1]; n, Q, rho, r, tl = map(int, sys.argv[2:7])
cl = make_instance(fam, n, 1); occ = occurrences(cl); m = len(cl)
idx = {}
def var(name):
    if name not in idx: idx[name] = len(idx)
    return idx[name]
for t in range(Q):
    for v in range(n):
        for g in range(r): var(('x', t, v, g)); var(('w', t, v, g))
    for e in range(m):
        for g in range(r): var(('y', t, e, g))
    for k in range(len(occ)): var(('z', t, k))
var('R')
N = len(idx)
rows = []; lo = []; hi = []
def add(coefs, l, u):
    rows.append(coefs); lo.append(l); hi.append(u)
for t in range(Q):
    for v in range(n): add({var(('x', t, v, g)): 1 for g in range(r)}, 1, 1)
    for g in range(r): add({var(('x', t, v, g)): 1 for v in range(n)}, n // r, n // r)
    for e in range(m): add({var(('y', t, e, g)): 1 for g in range(r)}, 1, 1)
    for v in range(n):
        for g in range(r): add({var(('w', t, v, g)): 1, var(('x', t, v, g)): -1}, -np.inf, 0)
    for g in range(r): add({var(('w', t, v, g)): 1 for v in range(n)}, -np.inf, rho)
    for k, (e, v) in enumerate(occ):
        for g in range(r):
            c = {var(('z', t, k)): 1, var(('y', t, e, g)): -1, var(('x', t, v, g)): 1}
            for g2 in range(r): c[var(('w', t, v, g2))] = c.get(var(('w', t, v, g2)), 0) + 1
            add(c, 0, np.inf)
for k in range(len(occ)):
    c = {var(('z', t, k)): 1 for t in range(Q)}; c[var('R')] = -1
    add(c, -np.inf, 0)
A = lil_matrix((len(rows), N))
for i, c in enumerate(rows):
    for j, a in c.items(): A[i, j] = a
lb = np.zeros(N); ub = np.ones(N); ub[var('R')] = Q
for t in range(Q): lb[var(('x', t, 0, 0))] = 1          # symmetry breaking
integ = np.ones(N); integ[var('R')] = 0
cobj = np.zeros(N); cobj[var('R')] = 1
res = milp(cobj, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integ, bounds=Bounds(lb, ub),
           options={'time_limit': tl, 'disp': False})
dual = getattr(res, 'mip_dual_bound', None)
print(json.dumps({'fam': fam, 'n': n, 'Q': Q, 'rho': rho, 'r': r, 'status': res.status, 'msg': res.message[:60],
                  'R_best': None if res.x is None else round(res.fun, 3), 'dual_bound': dual,
                  'M': len(occ), 'vars': N, 'cons': len(rows)}))
