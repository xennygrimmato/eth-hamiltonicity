"""Independent check of the orthogonal flat price on AG(2,g) with p merge classes, with internal edges.
Builds lines as explicit point sets (no label functions shared with ag_floor.py), places legs at finite M, computes
b_k = (L - H_k)/delta_k with exact Euclidean distances for every merge k separately, and compares with the closed form
E*(sqrt(p-1)+(g+1-p)/sqrt(p))/((g+1)) per merge.  Also checks the vanishing of cross terms used in the CS cap."""
import itertools, numpy as np
from fractions import Fraction

def gf(g):
    if g == 4:
        mul = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
        return list(range(4)), (lambda a, b: a ^ b), (lambda a, b: mul[a][b])
    return list(range(g)), (lambda a, b: (a + b) % g), (lambda a, b: (a * b) % g)

def lines(g):
    F, add, mul = gf(g)
    P = [(x, y) for x in F for y in F]
    dirs = [(1, s) for s in F] + [(0, 1)]
    cls = []
    for (dx, dy) in dirs:
        Ls = set()
        for (x0, y0) in P:
            Ls.add(frozenset((add(x0, mul(t, dx)), add(y0, mul(t, dy))) for t in F))
        assert len(Ls) == g
        cls.append(sorted(Ls, key=lambda L: sorted(L)))
    return P, cls

def simplex(g):
    # regular simplex of side 1 in R^(g-1)
    V = np.eye(g) / np.sqrt(2)
    c = V.mean(0); V = V - c
    # project to the (g-1)-dim hyperplane
    Q, _ = np.linalg.qr(V.T)
    W = V @ Q[:, :g - 1]
    return W

def check(g, p, M=1e7):
    P, cls = lines(g)
    idx = {pt: i for i, pt in enumerate(P)}
    grp = [[None] * len(P) for _ in range(g + 1)]
    for c, Ls in enumerate(cls):
        for li, L in enumerate(Ls):
            for pt in L: grp[c][idx[pt]] = li
    W = simplex(g); dim = p * (g - 1)
    def hub(k, G):
        x = np.zeros(dim); x[k * (g - 1):(k + 1) * (g - 1)] = W[G]; return x
    E = list(itertools.combinations(range(len(P)), 2))
    L = 0.0; H = np.zeros(p)
    for (u, v) in E:
        s = sum(hub(k, grp[k][u]) - hub(k, grp[k][v]) for k in range(p))
        ue = s / np.linalg.norm(s)
        lu, lv = M * ue, -M * ue
        L += np.linalg.norm(lu - lv)
        for k in range(p):
            H[k] += np.linalg.norm(lu - hub(k, grp[k][u])) + np.linalg.norm(lv - hub(k, grp[k][v]))
    delta = max(np.linalg.norm(hub(0, a) - hub(0, b)) for a, b in itertools.combinations(range(g), 2))
    b = (L - H) / delta
    closed = len(E) * (np.sqrt(p - 1) + (g + 1 - p) / np.sqrt(p)) / (g + 1)
    # cross-term check with random hubs
    rng = np.random.default_rng(1)
    h = rng.normal(size=(g + 1, g, 3))
    cross = sum(np.dot(h[0][grp[0][u]] - h[0][grp[0][v]], h[1][grp[1][u]] - h[1][grp[1][v]]) for (u, v) in E)
    return b, closed, len(E), cross

for g in (2, 3, 4, 5):
    for p in range(2, g + 2):
        b, closed, nE, cross = check(g, p)
        print(f'g={g} p={p} E={nE}: b_k/E = {np.round(b/nE,5)}  closed/E = {closed/nE:.5f}  cross-term(random hubs) = {cross:.2e}')
