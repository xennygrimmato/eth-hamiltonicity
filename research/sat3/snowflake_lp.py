"""Relaxations of the sqrt-rank geometry for the piece-floor objective (spec S3).

sqrt(rank) satisfies: (T) d is a metric, (T2) q = d^2 = rank is a metric. Over metrics with (T)+(T2) we
maximise sum_m (L - H_m) subject to all hub-hub distances <= 1 (a lower bound for sum_m b_m^+ of the
optimiser; it equals it when the optimum has all delta_m = 1). Variables q (squared distances): (T2) is
linear in q, (T) is sqrt(q_xz) <= sqrt(q_xy) + sqrt(q_yz). Local SLSQP from many starts -> the values
are lower bounds on the relaxation optimum (not certificates).
usage: python3 snowflake_lp.py DESIGN [starts] [mode]   mode: both | T (metric only) | T2 (d^2 metric only)
"""
import sys, itertools, math
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from verify_pf import design

name = sys.argv[1]; starts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
mode = sys.argv[3] if len(sys.argv) > 3 else 'both'
des = design({'crossing': 'crossing', 'k4': 'K4', 'delta3': 'Delta3'}[name])
E = len(des['edges']); nl = 2 * E
hub = {}; o = nl
for m, g in enumerate(des['groups']):
    for k in range(max(g) + 1):
        hub[(m, k)] = o; o += 1
n = o
pairs = list(itertools.combinations(range(n), 2)); P = {p: i for i, p in enumerate(pairs)}
def ix(a, b): return P[(min(a, b), max(a, b))]
# objective coefficients on d
c = np.zeros(len(pairs))
p = len(des['groups'])
for e, (u, v) in enumerate(des['edges']):
    w = des['w'][e]
    c[ix(2*e, 2*e+1)] += w * p
    for m, g in enumerate(des['groups']):
        c[ix(2*e, hub[(m, g[u])])] -= w
        c[ix(2*e+1, hub[(m, g[v])])] -= w
hubpairs = [ix(hub[(m, i)], hub[(m, j)]) for m, g in enumerate(des['groups']) for i in range(max(g)+1) for j in range(i+1, max(g)+1)]
tri = []
for a, b, cc in itertools.combinations(range(n), 3):
    for (x, y, z) in ((a, b, cc), (a, cc, b), (b, cc, a)):
        tri.append((ix(x, y), ix(x, z), ix(z, y)))   # d(x,y) <= d(x,z)+d(z,y)
tri = np.array(tri)
eps = 1e-12
def f(q): return -c @ np.sqrt(q + eps)
def gf(q): return -c * 0.5 / np.sqrt(q + eps)
cons = []
if mode in ('both', 'T2'):
    A = np.zeros((len(tri), len(pairs)))
    A[np.arange(len(tri)), tri[:, 0]] = -1; A[np.arange(len(tri)), tri[:, 1]] += 1; A[np.arange(len(tri)), tri[:, 2]] += 1
    cons.append({'type': 'ineq', 'fun': lambda q: A @ q, 'jac': lambda q: A})
if mode in ('both', 'T'):
    def tf(q):
        s = np.sqrt(q + eps); return s[tri[:, 1]] + s[tri[:, 2]] - s[tri[:, 0]]
    def tj(q):
        s = 0.5 / np.sqrt(q + eps); J = np.zeros((len(tri), len(pairs)))
        r = np.arange(len(tri)); J[r, tri[:, 1]] += s[tri[:, 1]]; J[r, tri[:, 2]] += s[tri[:, 2]]; J[r, tri[:, 0]] -= s[tri[:, 0]]
        return J
    cons.append({'type': 'ineq', 'fun': tf, 'jac': tj})
H = np.zeros((len(hubpairs), len(pairs))); H[np.arange(len(hubpairs)), hubpairs] = -1
cons.append({'type': 'ineq', 'fun': lambda q: 1 + H @ q, 'jac': lambda q: H})
rng = np.random.default_rng(0); best = -1e9
for s in range(starts):
    X = rng.normal(size=(n, 3)) * rng.uniform(0.3, 2)
    q0 = np.array([((X[i]-X[j])**2).sum() for i, j in pairs])  # Euclidean squared: q0 is not a metric in general
    q0 = np.minimum(q0, 4.0) * 0.25 + 0.01
    r = minimize(f, q0, jac=gf, constraints=cons, bounds=[(0, 16)] * len(pairs), method='SLSQP', options={'maxiter': 3000, 'ftol': 1e-12})
    val = -r.fun / p
    if r.success or True:
        viol = min(min(cc['fun'](r.x).min() for cc in cons), 0)
        if viol > -1e-6 and val > best + 1e-9:
            best = val; bq = r.x
    print(s, round(val, 6), r.success, flush=True)
print('BEST per-merge value (sum (L-H_m))/p with delta<=1:', best, 'mode', mode)
np.save(__file__.rsplit('/', 1)[0] + '/data/snowflake_%s_%s.npy' % (name, mode), bq)
