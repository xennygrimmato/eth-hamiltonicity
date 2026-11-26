"""Structure of the rank metric rho_2(a,b)^2 = rk(a-b) on Mat_2(F_2) (16 points).

1. combinatorial model: {0} u [3]x[3] u S_3
2. equality case of the contracting inequality at mu = 2: the only extremal table is rho_2
3. graph identity dim(graph a + graph b) - mu = rk(a - b) for mu = 2, 3 (bridge to the Grassmannian)
"""
import itertools, builtins, numpy as np
if __name__ != "__main__":
    print = lambda *a, **k: None

def rank2(M):                      # rank over F_2 by elimination
    M = [list(r) for r in M]; r = 0; rows, cols = len(M), len(M[0])
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(rows):
            if i != r and M[i][c]: M[i] = [x ^ y for x, y in zip(M[i], M[r])]
        r += 1
    return r

mats = [((a, b), (c, d)) for a, b, c, d in itertools.product([0, 1], repeat=4)]
add = lambda A, B: tuple(tuple(x ^ y for x, y in zip(r, s)) for r, s in zip(A, B))
rk = {A: rank2(A) for A in mats}
Z = ((0, 0), (0, 0)); I = ((1, 0), (0, 1))
R1 = [A for A in mats if rk[A] == 1]; R2 = [A for A in mats if rk[A] == 2]
if __name__ == "__main__": print("ranks:", {r: sum(1 for A in mats if rk[A] == r) for r in range(3)})

# --- 1. model -------------------------------------------------------------------------------------------------
vecs = [(1, 0), (0, 1), (1, 1)]                               # nonzero vectors x_0, x_1, x_2
dot = lambda u, v: (u[0] & v[0]) ^ (u[1] & v[1])
ys = [next(y for y in vecs if dot(y, x) == 0) for x in vecs]  # y_j = the functional vanishing on x_j
cell = {(i, j): tuple(tuple(vecs[i][r] & ys[j][c] for c in range(2)) for r in range(2)) for i in range(3) for j in range(3)}
assert sorted(cell.values()) == sorted(R1)
inv = {v: k for k, v in cell.items()}
def perm_of(g):                                               # g x_i = x_{sigma(i)}
    mul = lambda g, x: tuple((g[r][0] & x[0]) ^ (g[r][1] & x[1]) for r in range(2))
    return tuple(vecs.index(mul(g, x)) for x in vecs)
sig = {g: perm_of(g) for g in R2}
parity = lambda s: sum(1 for i in range(3) for j in range(i) if s[j] > s[i]) % 2
ok = True
for (i, j), W in cell.items():
    ok &= rk[W] == 1
    for (k, l), W2 in cell.items(): ok &= rk[add(W, W2)] == (i != k) + (j != l)
    for g, s in sig.items(): ok &= rk[add(g, W)] == (2 if i == s[j] else 1)
for g, s in sig.items():
    for h, t in sig.items():
        if g != h: ok &= rk[add(g, h)] == (1 if parity(s) != parity(t) else 2)
print("model {0} u [3]x[3] u S_3 with the stated distance table:", ok)
hexI = [W for W in R1 if rk[add(I, W)] == 1]
print("hexagon of I: cells", sorted(inv[W] for W in hexI), "(the off-diagonal cells)")
adj = {W: [U for U in hexI if U != W and rk[add(U, W)] == 1] for W in hexI}
print("each hexagon cell has", {len(v) for v in adj.values()}, "rank-one neighbours in the hexagon; opposite cell is W + I:",
      all(add(W, I) in hexI and rk[add(W, add(W, I))] == 2 for W in hexI))
# 6-cycle?
cyc = [hexI[0]]
while True:
    nxt = [U for U in adj[cyc[-1]] if U not in cyc]
    if not nxt: break
    cyc.append(nxt[0])
print("hexagon is one 6-cycle:", len(cyc) == 6 and cyc[0] in adj[cyc[-1]], [inv[W] for W in cyc])

# --- 2. equality case at mu = 2 -------------------------------------------------------------------------------
# Step 1-3 of Anthropic's Theorem D.2 hold at mu = 2.  Unknowns: n(W), W of rank one (translation invariant, shown in
# the notebook).  For every invertible V the three transversal splittings V = W + W' must have the same n(W) + n(W').
rows = []
for V in R2:
    splits = sorted({tuple(sorted((W, add(V, W)))) for W in R1 if rk[add(V, W)] == 1})
    assert len(splits) == 3
    for s in splits[1:]:
        r = np.zeros(9)
        for W in splits[0]: r[R1.index(W)] += 1
        for W in s: r[R1.index(W)] -= 1
        rows.append(r)
A = np.array(rows); sv = np.linalg.svd(A, compute_uv=False)
print("equal-sum system: %d equations, rank %d  => solution space of dimension %d (constants)" % (len(rows), int((sv > 1e-9).sum()), 9 - int((sv > 1e-9).sum())))
# characters chi_V(a) = (-1)^{tr(V^{-1} a)}: check chi_V(W) = -1 exactly on the hexagon of V
def inv2(V):
    (a, b), (c, d) = V; return ((d, b), (c, a))               # det = 1 over F_2
def tr_prod(A, B): return (A[0][0] & B[0][0]) ^ (A[0][1] & B[1][0]) ^ (A[1][0] & B[0][1]) ^ (A[1][1] & B[1][1])
chi = {V: {a: 1 - 2*tr_prod(inv2(V), a) for a in mats} for V in R2}
print("chi_V = -1 exactly on rank-one W with rk(V - W) = 1:", all((chi[V][W] == -1) == (rk[add(V, W)] == 1) for V in R2 for W in R1))
print("the six characters chi_V are distinct:", len({tuple(chi[V][a] for a in mats) for V in R2}) == 6)
# the inequality  tau_{V'} chi_{V'}(a+W) + tau_V chi_V(a) <= 0  (V' = W + W'', W, W'' non-adjacent non-opposite in the hexagon of V)
# summed over a gives 0, so it is an equality for every a; then tau = 0.  Numerical check by LP: maximise |tau|.
from scipy.optimize import linprog
G = []
for V in R2:
    hexV = [W for W in R1 if rk[add(V, W)] == 1]
    for W in hexV:
        for W2 in hexV:
            V2 = add(W, W2)
            if rk[V2] != 2 or V2 == V: continue
            for a in mats:
                r = np.zeros(6); r[R2.index(V2)] += chi[V2][add(a, W)]; r[R2.index(V)] += chi[V][a]; G.append(r)
G = np.array(G); best = 0
for k in range(6):
    for sgn in (1, -1):
        c = np.zeros(6); c[k] = -sgn
        res = linprog(c, A_ub=G, b_ub=np.zeros(len(G)), bounds=[(-1, 1)]*6, method="highs")
        best = max(best, -res.fun)
print("largest |tau_V| allowed by the midpoint inequalities: %.2e  (0 => rank-two squared distances are all exactly 2)" % best)

# --- 3. graphs ------------------------------------------------------------------------------------------------
for mu in (2, 3):
    allm = [tuple(tuple(bits[r*mu + c] for c in range(mu)) for r in range(mu)) for bits in itertools.product([0, 1], repeat=mu*mu)]
    basis = [tuple(int(i == j) for j in range(mu)) for i in range(mu)]
    def graph(a): return [x + tuple(sum(a[r][c] & x[c] for c in range(mu)) % 2 for r in range(mu)) for x in basis]
    import random; random.seed(1)
    pairs = [(a, b) for a in allm for b in allm] if mu == 2 else [(random.choice(allm), random.choice(allm)) for _ in range(20000)]
    good = all(rank2(graph(a) + graph(b)) - mu == rank2([[x ^ y for x, y in zip(r, s)] for r, s in zip(a, b)]) for a, b in pairs)
    print("mu = %d: dim(graph a + graph b) - mu = rk(a - b) on %d pairs: %s" % (mu, len(pairs), good))
