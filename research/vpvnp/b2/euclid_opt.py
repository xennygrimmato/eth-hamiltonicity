# Maximise the single-price hub bound sum_k max(0,(L-H_k)/delta_k) over EUCLIDEAN configurations
# of 18 legs + 9 hubs (3 per merge) in R^m. Smoothed objective, L-BFGS, random restarts.
import sys, itertools
import numpy as np
from scipy.optimize import minimize

nodes = [(r, c) for r in range(3) for c in range(3)]
tri = {v: (v[0] + v[1]) % 3 for v in nodes}
legs = [(u, v) for u in nodes for v in nodes if u != v and tri[u] == tri[v]]
edges = [(i, legs.index((b, a))) for i, (a, b) in enumerate(legs) if a < b]
mergef = [lambda v: v[0], lambda v: v[1], lambda v: (v[0] - v[1]) % 3]
names = 'RCD'

def unpack(z, m, K):
    P = z[:18 * m].reshape(18, m)
    Hs = z[18 * m:].reshape(K, 3, m)
    return P, Hs

def values(z, m, ks, eps=0.0):
    P, Hs = unpack(z, m, len(ks))
    nrm = lambda x: np.sqrt((x * x).sum(-1) + eps)
    L = sum(nrm(P[a] - P[b]) for a, b in edges)
    out = []
    for j, k in enumerate(ks):
        H = sum(nrm(P[i] - Hs[j, mergef[k](u)]) for i, (u, v) in enumerate(legs))
        dd = [nrm(Hs[j, g] - Hs[j, g2]) for g, g2 in itertools.combinations(range(3), 2)]
        out.append((L, H, dd))
    return out

def obj(z, m, ks, eps, tau):
    tot = 0.0
    for (L, H, dd) in values(z, m, ks, eps):
        dd = np.array(dd)
        dmax = tau * np.log(np.exp(dd / tau).sum())  # soft max
        tot += (L - H) / dmax
    return -tot

def exact(z, m, ks):
    res = []
    for (L, H, dd) in values(z, m, ks):
        res.append((L - H) / max(dd))
    return res

if __name__ == '__main__':
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    ks = [int(c) for c in (sys.argv[2] if len(sys.argv) > 2 else '012')]
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    best = (-1e9, None)
    for t in range(trials):
        z = rng.normal(size=18 * m + 9 * len(ks) // 3 * m if False else 18 * m + 3 * len(ks) * m)
        for eps, tau in ((1e-2, 0.1), (1e-4, 0.02), (1e-6, 0.005)):
            r = minimize(obj, z, args=(m, ks, eps, tau), method='L-BFGS-B', options={'maxiter': 4000})
            z = r.x
        b = exact(z, m, ks)
        s = sum(max(0, x) for x in b)
        if s > best[0]:
            best = (s, b, z)
        print(t, round(s, 4), [round(x, 3) for x in b], flush=True)
    print('BEST', best[0], best[1])
    np.save('euclid_best_m%d_%s.npy' % (m, ''.join(map(str, ks))), best[2])
