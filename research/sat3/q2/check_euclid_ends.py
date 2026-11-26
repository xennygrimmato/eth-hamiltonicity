"""Ends-as-sites in Euclidean space (q2-notes.md, Prop. E2).
(1) the construction x_(u,v) = (e_u - e_v)/sqrt2 has first-order value |w_cut| = K^{3/2}/(2 sqrt2) on
    every exactly balanced cut;
(2) for ANY antisymmetric family of unit vectors u_(u,v) the mean over exactly balanced cuts of
    |w_cut|^2 equals K/(4(K-1)) * sum_u |X_u|^2 <= K^2 (K-1)/4   (exhaustive over cuts, K = 6, 8)."""
import numpy as np, itertools, math
rng = np.random.default_rng(0)
def cuts(K):
    for A in itertools.combinations(range(K), K // 2):
        if 0 in A: yield A
for K in (6, 8):
    # (1)
    E = np.eye(K)
    vals = []
    for A in cuts(K):
        B = [v for v in range(K) if v not in A]
        w = sum((E[u] - E[v]) / math.sqrt(2) for u in A for v in B)
        vals.append(np.linalg.norm(w))
    print(f"K={K}: construction: |w| in [{min(vals):.6f}, {max(vals):.6f}], K^1.5/(2 sqrt2) = {K**1.5/(2*math.sqrt(2)):.6f}")
    # (2)
    for dim in (3, K, 4 * K):
        U = {}
        for u in range(K):
            for v in range(u + 1, K):
                g = rng.standard_normal(dim); g /= np.linalg.norm(g)
                U[(u, v)] = g; U[(v, u)] = -g
        X = [sum(U[(u, v)] for v in range(K) if v != u) for u in range(K)]
        m2 = np.mean([np.linalg.norm(sum(U[(u, v)] for u in A for v in range(K) if v not in A)) ** 2 for A in cuts(K)])
        pred = K / (4 * (K - 1)) * sum(np.dot(x, x) for x in X)
        print(f"   random unit directions in R^{dim}: mean |w|^2 = {m2:.6f}, formula = {pred:.6f}, cap K^2(K-1)/4 = {K*K*(K-1)/4}")
