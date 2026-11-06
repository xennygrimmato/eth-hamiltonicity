"""entropy_dual.py -- the Shannon certificate of Q*:  sum_c I(col_c) + sum_d I(diag_d) - 2 I(R_0) >= 0  on 9 variables.
Solves the LP dual (nonnegative combination of elemental inequalities) and prints the elemental inequalities used, so
that one can see which steps are subadditivity-type (valid for flattening ranks) and which are conditional-MI (SSA-type,
NOT valid for ranks in general)."""
import numpy as np, itertools
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
nodes = [(r, c) for r in range(3) for c in range(3)]
n = 9; FULL = (1 << n) - 1
def mask(vs): return sum(1 << nodes.index(v) for v in vs)
def name(S): return '{' + ','.join(f'{r}{c}' for (r, c) in nodes if S >> nodes.index((r, c)) & 1) + '}'
rows = [mask([(r, c) for c in range(3)]) for r in range(3)]
cols = [mask([(r, c) for r in range(3)]) for c in range(3)]
diags = [mask([(r, c) for r in range(3) for c in range(3) if (r - c) % 3 == d]) for d in range(3)]
ineqs = []; labels = []
# elemental: I(i;j|K) >= 0 and H(V) - H(V\i) >= 0, as vectors g with g.H >= 0
for i in range(n):
    g = np.zeros(1 << n); g[FULL] += 1; g[FULL & ~(1 << i)] -= 1; ineqs.append(g); labels.append(f'H(V)-H(V\\{name(1<<i)})')
for i in range(n):
    for j in range(i + 1, n):
        rest = FULL & ~(1 << i) & ~(1 << j); K = rest
        while True:
            g = np.zeros(1 << n)
            g[(1 << i) | K] += 1; g[(1 << j) | K] += 1; g[(1 << i) | (1 << j) | K] -= 1; g[K] -= 1
            ineqs.append(g); labels.append(f'I({name(1<<i)};{name(1<<j)}|{name(K)})')
            if K == 0: break
            K = (K - 1) & rest
G = np.array(ineqs)            # m x 512
target = np.zeros(1 << n)
def MI(S): return {S: 1, FULL & ~S: 1, FULL: -1}
for S in cols + diags:
    for k, v in MI(S).items(): target[k] += v
for k, v in MI(rows[0]).items(): target[k] -= 2 * v
# find y >= 0 with G^T y = target (exact), minimise sum y
m = G.shape[0]
GT = csr_matrix(G[:, 1:].T); r = linprog(np.ones(m), A_eq=GT, b_eq=target[1:], bounds=[(0, None)] * m, method='highs')  # H(empty)=0 is not a free coordinate
print('status', r.status, r.message)
y = r.x
used = [(labels[i], round(y[i], 4)) for i in range(m) if y[i] > 1e-9]
print(f'certificate: {len(used)} elemental inequalities, total weight {y.sum():.3f}')
for l, w in sorted(used, key=lambda t: -t[1]): print(f'  {w:6.3f}  {l}')
# sanity: residual
print('residual', np.abs(G[:, 1:].T @ y - target[1:]).max())
