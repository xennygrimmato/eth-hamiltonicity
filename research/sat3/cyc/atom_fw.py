"""Shannon relaxation of the "subspace ansatz with shifts" for Delta_3, one factor (atom).

An atom: subspaces V_h of K^N (any dimensions k_h >= 0), W_n = sum of the hubs of n, W_n and W_n' independent on
the nine edges; hub point = 1_{V_h} - (k_h/N) 1 (R-factor removed); legs d = 1_{W_n} - 1_{W_n'} (made sum-zero).
   c_e   = [K_n + K_n' - (K_n - K_n')(w_n - w_n')/N] / sqrt(w_n + w_n' - (w_n - w_n')^2/N),   K_n = sum_{h in n} k_h,
   Gamma = 9 sum_e c_e^2 / sum_{same-class pairs} [k_h + k_h' - (k_h - k_h')^2/N].
Tripod atom: 36.  Uniform arrangement (k,w,N) = (2,5,10): 32.4.
Here the rank function is relaxed to an arbitrary polymatroid r on the nine hubs (k_h = r(h), w_n = r(n)) and
N >= r(all) is free: local maximisation of Gamma by Frank-Wolfe steps (LP + line search) from several starts.
An upper bound would need a global optimum; this is a search for a polymatroid with Gamma > 36.
"""
import numpy as np, itertools, sys
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
H = [(u, v) for u in range(3) for v in range(3)]
idx = {h: i for i, h in enumerate(H)}
nodes = [tuple(idx[(u, (i + t*u) % 3)] for u in range(3)) for t in range(3) for i in range(3)]
edges = [(3*t+i, 3*t+(i+1) % 3) for t in range(3) for i in range(3)]
pairs = [(3*u+v, 3*u+w) for u in range(3) for v in range(3) for w in range(v+1, 3)]
mask = lambda S: sum(1 << i for i in S)
NV = 512; NN = 512          # variable index of N
rows, cols, vals = [], [], []; nr = 0
def add(ent):
    global nr
    for c, v in ent:
        if c != 0: rows.append(nr); cols.append(c); vals.append(v)
    nr += 1
full = 511
for i in range(9): add([(full, 1), (full ^ (1 << i), -1)])                    # monotone  (>= 0 form)
for i in range(9):
    for j in range(i+1, 9):
        for S in range(512):
            if S >> i & 1 or S >> j & 1: continue
            add([(S | 1 << i, 1), (S | 1 << j, 1), (S | 1 << i | 1 << j, -1), (S, -1)])
add([(NN, 1), (full, -1)])                                                    # N >= r(all)
A = coo_matrix((vals, (rows, cols)), shape=(nr, 513)).tocsr()
er, ec, ev = [], [], []; ne = 0
for (a, b) in edges:
    ma, mb = mask(nodes[a]), mask(nodes[b])
    er += [ne]*3; ec += [ma | mb, ma, mb]; ev += [1, -1, -1]; ne += 1
er += [ne]*9; ec += [1 << i for i in range(9)]; ev += [1]*9; ne += 1          # normalisation sum k_h = 9
E = coo_matrix((ev, (er, ec)), shape=(ne, 513)).tocsr()
beq = np.zeros(ne); beq[-1] = 9
bounds = [(0, 0)] + [(0, None)]*511 + [(0, 60)]

def parts(x):
    N = x[NN]; num = 0.0
    for (a, b) in edges:
        Ka = sum(x[1 << h] for h in nodes[a]); Kb = sum(x[1 << h] for h in nodes[b])
        wa, wb = x[mask(nodes[a])], x[mask(nodes[b])]
        den = wa + wb - (wa - wb)**2/N
        if den > 1e-12: num += (Ka + Kb - (Ka - Kb)*(wa - wb)/N)**2/den
    D = sum(x[1 << a] + x[1 << b] - (x[1 << a] - x[1 << b])**2/N for a, b in pairs)
    return num, D
def gamma(x):
    num, D = parts(x); return 9*num/D if D > 1e-12 else 0.0
def grad(x, eps=1e-6):
    g = np.zeros(513); base = gamma(x)
    act = [1 << h for h in range(9)] + [mask(n) for n in nodes] + [NN]
    for c in act:
        y = x.copy(); y[c] += eps; g[c] = (gamma(y) - base)/eps
    return g
def lp(c):
    res = linprog(-c, A_ub=-A, b_ub=np.zeros(nr), A_eq=E, b_eq=beq, bounds=bounds, method="highs")
    return res.x if res.status == 0 else None
def rank_fn_tripod():
    x = np.zeros(513)
    T = {idx[(0, 0)], idx[(1, 0)], idx[(2, 0)]}
    for S in range(1, 512): x[S] = min(2, sum(1 for i in range(9) if S >> i & 1 and i in T))
    x[NN] = 2; return x*3     # sum k_h = 3 -> scale to 9
def feasible(x): return (A @ x).min() > -1e-7 and abs(E @ x - beq).max() < 1e-7
x0 = rank_fn_tripod(); print("tripod atom: feasible", feasible(x0), "Gamma", gamma(x0))
best = (gamma(x0), x0)
for start in range(int(sys.argv[2]) if len(sys.argv) > 2 else 12):
    c = rng.normal(size=513); c[NN] = 0
    for i in range(9): c[1 << i] += 2*rng.random()
    x = lp(c)
    if x is None: continue
    x[NN] = max(x[NN], x[full]) if rng.random() < .5 else x[full]*(1 + rng.random())
    if start % 3 == 0: x = 0.5*x + 0.5*x0
    cur = gamma(x)
    for it in range(60):
        y = lp(grad(x))
        if y is None: break
        ts = np.linspace(0, 1, 41); vals_ = [gamma((1-t)*x + t*y) for t in ts]
        j = int(np.argmax(vals_))
        if vals_[j] <= cur + 1e-9: break
        x = (1-ts[j])*x + ts[j]*y; cur = vals_[j]
    print("start", start, "local optimum Gamma = %.5f" % cur, " k_h =", np.round([x[1 << i] for i in range(9)], 3),
          " w_n =", np.round([x[mask(n)] for n in nodes], 3), " N = %.3f" % x[NN]); sys.stdout.flush()
    if cur > best[0]: best = (cur, x.copy())
print("BEST Gamma over polymatroids found:", best[0])
np.save("out/atom_fw_best.npy", best[1])
