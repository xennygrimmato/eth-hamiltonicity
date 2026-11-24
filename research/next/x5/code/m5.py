"""Idea 2: M5 = {0, I, e11, e22, e11+e12} in (Mat_2(F_2), sqrt rank).
(1) exact non-Euclidean check (Cayley-Menger / Gram), all 4-subsets Euclidean, 5-subset count and orbits
(2) l1 (cut cone) membership by LP
(3) lower bounds on covers of weighted wire networks on M5 from explicit spectral points
    (partition-star metrics delta <= M5): max sum w_e delta(e) vs sum w_e M5(e)."""
import itertools, numpy as np, sympy as sp
from scipy.optimize import linprog

def mats(mu):
    return [np.array(b, dtype=np.uint8).reshape(mu, mu) for b in itertools.product([0, 1], repeat=mu * mu)]

def rk2(a):
    a = a.copy() % 2; r = 0; n, m = a.shape
    for c in range(m):
        piv = next((i for i in range(r, n) if a[i, c]), None)
        if piv is None: continue
        a[[r, piv]] = a[[piv, r]]
        for i in range(n):
            if i != r and a[i, c]: a[i] ^= a[r]
        r += 1
    return r

M2 = mats(2)
key = lambda a: tuple(a.flatten())
RK = {(key(a), key(b)): rk2(a ^ b) for a in M2 for b in M2}
d2 = lambda a, b: RK[(key(a), key(b))]          # squared distance

def gram_exact(pts):
    """Gram matrix (based at pts[0]) of squared-distance data, exact; Euclidean iff PSD"""
    n = len(pts)
    G = sp.Matrix(n - 1, n - 1, lambda i, j: sp.Rational(d2(pts[0], pts[i + 1]) + d2(pts[0], pts[j + 1]) - d2(pts[i + 1], pts[j + 1]), 2))
    return G

def is_euclid(pts):
    G = np.array([[0.5 * (d2(pts[0], pts[i]) + d2(pts[0], pts[j]) - d2(pts[i], pts[j])) for j in range(1, len(pts))] for i in range(1, len(pts))])
    return np.linalg.eigvalsh(G).min() > -1e-9

Z = np.zeros((2, 2), np.uint8); S = np.eye(2, dtype=np.uint8)
A = np.array([[1, 0], [0, 0]], np.uint8); D = np.array([[0, 0], [0, 1]], np.uint8); C = np.array([[1, 1], [0, 0]], np.uint8)
M5 = [Z, S, A, D, C]; names = ['0', 'S', 'A', 'D', 'C']

if __name__ == '__main__':
    print("M5 squared distances:")
    for i in range(5):
        print(names[i], [d2(M5[i], M5[j]) for j in range(5)])
    G = gram_exact(M5)
    print("Gram (based at 0):", G.tolist(), " eigenvalues:", [sp.nsimplify(e) for e in G.eigenvals()])
    print("det Gram =", G.det(), " (negative => not Euclidean)")
    # 4-subsets & 5-subsets
    bad4 = sum(1 for Q in itertools.combinations(range(16), 4) if not is_euclid([M2[i] for i in Q]))
    bad5 = [Q for Q in itertools.combinations(range(16), 5) if not is_euclid([M2[i] for i in Q])]
    print("non-Euclidean 4-subsets:", bad4, " 5-subsets:", len(bad5), "of", len(list(itertools.combinations(range(16), 5))))
    # orbits under a -> P a Q + B, transpose
    GL = [g for g in M2 if rk2(g) == 2]
    idx = {key(a): i for i, a in enumerate(M2)}
    maps = []
    for P in GL:
        for Qm in GL:
            for B in M2:
                for t in (0, 1):
                    maps.append(tuple(idx[key(((P @ (a.T if t else a) @ Qm) % 2) ^ B)] for a in M2))
    seen = set(); orbits = []
    for Qs in bad5:
        fs = frozenset(Qs)
        if fs in seen: continue
        orb = {frozenset(m[i] for i in Qs) for m in maps}
        seen |= orb; orbits.append((sorted(Qs), len(orb)))
    print("orbits of non-Euclidean 5-subsets:", [(o[1], sorted(sorted(d2(M2[a], M2[b]) for a, b in itertools.combinations(o[0], 2)))) for o in orbits])
    # (2) cut cone LP
    pairs = list(itertools.combinations(range(5), 2))
    dist = np.array([np.sqrt(d2(M5[i], M5[j])) for i, j in pairs])
    cuts = [set(c) for r in (1, 2) for c in itertools.combinations(range(5), r) if not (r == 2 and 0 not in c and False)]
    cuts = [c for c in cuts if not (len(c) == 2 and 0 not in c) or True]
    cuts = list({frozenset(c) if 0 in c else frozenset(set(range(5)) - c) for c in cuts})
    Acut = np.array([[1.0 if ((i in c) != (j in c)) else 0.0 for c in cuts] for i, j in pairs])
    res = linprog(np.zeros(len(cuts)), A_eq=Acut, b_eq=dist, bounds=[(0, None)] * len(cuts))
    print("M5 in cut cone (l1-embeddable):", res.status == 0)
    # (3) explicit spectral points: partition-star metrics <= M5
    def partitions(s):
        if not s: yield []; return
        f, rest = s[0], s[1:]
        for p in partitions(rest):
            for k in range(len(p)):
                yield p[:k] + [[f] + p[k]] + p[k + 1:]
            yield [[f]] + p
    parts = list(partitions(list(range(5))))
    def best_explicit(w):
        best = 0
        for p in parts:
            if len(p) < 2: continue
            blk = {v: b for b, B in enumerate(p) for v in B}
            # variables w_B >= 0; constraint w_[u]+w_[v] <= d(u,v) for u,v in different blocks
            nb = len(p); Aub = []; bub = []; c = np.zeros(nb)
            for e, (i, j) in enumerate(pairs):
                if blk[i] != blk[j]:
                    row = np.zeros(nb); row[blk[i]] += 1; row[blk[j]] += 1
                    Aub.append(row); bub.append(dist[e]); c -= w[e] * row
            r = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub), bounds=[(0, None)] * nb)
            best = max(best, -r.fun)
        return best
    tests = {'all 10 pairs': np.ones(10)}
    for nm, es in [('0S,AD,CD', [('0', 'S'), ('A', 'D'), ('C', 'D')]), ('0S,AD,CD,AC', [('0', 'S'), ('A', 'D'), ('C', 'D'), ('A', 'C')]),
                   ('square 0ASD sides+diags', [('0', 'A'), ('A', 'S'), ('S', 'D'), ('D', '0'), ('0', 'S'), ('A', 'D')]),
                   ('diagonals 0S,AD', [('0', 'S'), ('A', 'D')])]:
        w = np.zeros(10)
        for a, b in es:
            i, j = sorted((names.index(a), names.index(b))); w[pairs.index((i, j))] = 1
        tests[nm] = w
    for nm, w in tests.items():
        print(f"network {nm:28s} M5-length {w @ dist:.4f}  best explicit point {best_explicit(w):.4f}  ratio {best_explicit(w)/(w@dist):.4f}")
    # worst weighting: min over w>=0 of best_explicit(w)/(w.dist): random search + local
    rng = np.random.default_rng(0); worst = (9, None)
    for t in range(3000):
        w = rng.exponential(size=10) * (rng.random(10) < 0.6)
        if w.sum() == 0: continue
        r = best_explicit(w) / (w @ dist)
        if r < worst[0]: worst = (r, w)
    print("worst ratio explicit/M5 over random weightings:", round(worst[0], 4), "w =", np.round(worst[1] / worst[1].max(), 2), "pairs", [(names[i] + names[j]) for i, j in pairs])
