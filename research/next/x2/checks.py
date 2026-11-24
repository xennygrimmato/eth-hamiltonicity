"""x2 sanity checks: (1) Euclidean sup of perimeter/Fermat-Weber; (2) random metric spaces:
3-hub (grouped MM) inequality with rank exponent = max grouped flattening is never violated;
(3) every 3-point metric is a tripod (theta >= 0)."""
import numpy as np
from scipy.optimize import minimize
rng = np.random.default_rng(1)

def fw(pts):
    f = lambda o: np.linalg.norm(pts - o, axis=1).sum()
    return minimize(f, pts.mean(0), method="Nelder-Mead", options=dict(xatol=1e-10, fatol=1e-12)).fun

# (1) sup P/FW over Euclidean triangles
best = 0
for _ in range(20000):
    p = rng.normal(size=(3, 2))
    P = sum(np.linalg.norm(p[i]-p[j]) for i, j in [(0,1),(1,2),(0,2)])
    best = max(best, P / fw(p))
print("(1) sup P/FW Euclidean triangles ~", best, " sqrt3 =", 3**0.5)

# (2) random finite metric spaces (shortest paths of random weighted graphs), random graph tensor on
# parties grouped in 3 groups, hubs = arbitrary points of the space; check
#   sum_e w_e|uv| <= sum_p deg(p)|p o_G(p)| + rho * min_o sum_X |o o_X|,  rho = max_X deg_X (flattening)
viol = 0; worst = -1e9
for trial in range(3000):
    n = rng.integers(6, 12)
    W = rng.uniform(0.1, 1, (n, n)); W = (W + W.T) / 2
    mask = rng.random((n, n)) < 0.5; mask = mask | mask.T
    D = np.where(mask, W, np.inf); np.fill_diagonal(D, 0)
    for k in range(n): D = np.minimum(D, D[:, [k]] + D[[k], :])
    if not np.isfinite(D).all(): continue
    m = rng.integers(3, n - 2)  # parties 0..m-1, rest are candidate hub points
    grp = rng.integers(0, 3, m)
    wt = np.triu(rng.integers(0, 3, (m, m)), 1)
    lhs = sum(wt[u, v] * D[u, v] for u in range(m) for v in range(m))
    deg = wt + wt.T
    degX = [sum(deg[u, v] for u in range(m) for v in range(m) if grp[u] == X and grp[v] != X) for X in range(3)]
    rho = max(degX)
    hubs = rng.integers(0, n, 3)
    rhs = sum(deg[p].sum() * D[p, hubs[grp[p]]] for p in range(m))
    rhs += rho * min(sum(D[o, hubs[X]] for X in range(3)) for o in range(n))
    worst = max(worst, lhs - rhs); viol += lhs > rhs + 1e-9
print("(2) violations:", viol, " max(lhs-rhs) =", worst)

# (3) tripod weights of random 3-point metrics
ok = True
for _ in range(10000):
    p = rng.random((3, 5)); d = {(i, j): np.abs(p[i]-p[j]).sum() for i in range(3) for j in range(3)}
    th = [(d[(i,(i+1)%3)] + d[(i,(i+2)%3)] - d[((i+1)%3,(i+2)%3)]) / 2 for i in range(3)]
    ok &= min(th) >= -1e-12
print("(3) all tripod weights >= 0:", ok)
