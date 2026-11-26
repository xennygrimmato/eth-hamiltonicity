"""Lemma N (q2-notes.md, section 2): for K points in any metric space there is an exactly
balanced cut (A,B) such that for ALL supplier pairs (y0,y1)
    (K-1) * [sum_{i in A} d(x_i,y0) + sum_{i in B} d(x_i,y1)]  >=  sum_{u<v} d(x_u,x_v).
Brute-force check on random finite metric spaces (random points in l1, l2, l_inf, random
trees, random graph metrics); suppliers range over all points of the ambient finite space."""
import itertools, random, math, sys

def graph_metric(n, p, rng):
    INF = 1e18
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p or j == i + 1:
                w = rng.uniform(0.2, 1.0)
                d[i][j] = d[j][i] = w
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    return d

def tree_metric(n, rng):
    INF = 1e18
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for j in range(1, n):
        i = rng.randrange(j)
        w = rng.uniform(0.2, 1.0)
        d[i][j] = d[j][i] = w
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    return d

def lp_metric(n, dim, p, rng):
    pts = [[rng.gauss(0, 1) for _ in range(dim)] for _ in range(n)]
    def dist(a, b):
        if p == 'inf':
            return max(abs(x - y) for x, y in zip(a, b))
        return sum(abs(x - y) ** p for x, y in zip(a, b)) ** (1.0 / p)
    return [[dist(a, b) for b in pts] for a in pts]

def check(d, K, rng):
    n = len(d)
    rows = rng.sample(range(n), K)
    total = sum(d[rows[u]][rows[v]] for u in range(K) for v in range(u + 1, K))
    best_gap = None  # max over cuts of min over suppliers of (K-1)*star - total
    for A in itertools.combinations(range(K), K // 2):
        if 0 not in A:
            continue
        B = [i for i in range(K) if i not in A]
        sA = min(sum(d[rows[i]][y] for i in A) for y in range(n))
        sB = min(sum(d[rows[i]][y] for i in B) for y in range(n))
        gap = (K - 1) * (sA + sB) - total
        if best_gap is None or gap > best_gap:
            best_gap = gap
    return best_gap

rng = random.Random(1)
worst = 1e9
trials = 0
for K in (4, 6, 8):
    for rep in range(60):
        kind = rep % 5
        n = K + 12
        if kind == 0: d = graph_metric(n, 0.2, rng)
        elif kind == 1: d = tree_metric(n, rng)
        elif kind == 2: d = lp_metric(n, 3, 1, rng)
        elif kind == 3: d = lp_metric(n, 5, 2, rng)
        else: d = lp_metric(n, 4, 'inf', rng)
        g = check(d, K, rng)
        worst = min(worst, g)
        trials += 1
print("trials", trials, "min over trials of [max over balanced cuts of min over suppliers of (K-1)*star - sum_pairs] =", worst)
print("Lemma N predicts this is >= 0:", worst >= -1e-9)

# equality case: K-pod with unit legs (all pairs at distance 2), suppliers at the centre
K = 8
print("pod, K=8: (K-1)*K =", (K - 1) * K, " sum_pairs =", 2 * K * (K - 1) // 2)
