"""Idea 2(b): price-method floors (b2's (*)) for piece problems on 5 parties {0,S,A,C,D}.
Problem = wires (pairs of parties, weight 1) + set of cuts (bipartitions). One price d with hubs (o_K, o'_K) gives a piece with
  c_K >= b_K := (L - H_K)/delta_K for all K,  L = sum_e d(e), H_K = sum_e [d(e-, hub of its side) + d(e+, hub of its side)].
Score F = sum_K max(b_K, 0)   (some piece has sum_K c_K >= F).
F_rho: legs+hubs in (Mat_3(F2), sqrt rk) by coordinate hill climbing.  F_E: legs+hubs in R^5 by Nelder-Mead/BFGS restarts.
If F_rho > F_E for a problem, a piece family with sum_K c_K in between proves rho_3 not a price (=> contracting), while
being consistent with the flat hypothesis.  Calibration: crossing (wires 0S, AD; cuts {0,A}|{S,D}, {0,D}|{A,S}) F_E = 2 sqrt2."""
import itertools, numpy as np, sys
from scipy.optimize import minimize

P = ['0', 'S', 'A', 'C', 'D']
mu = 3
mats = np.array(list(itertools.product([0, 1], repeat=mu * mu)), dtype=np.uint8)
def rk(m):
    a = m.reshape(mu, mu).copy(); r = 0
    for c in range(mu):
        piv = next((i for i in range(r, mu) if a[i, c]), None)
        if piv is None: continue
        a[[r, piv]] = a[[piv, r]]
        for i in range(mu):
            if i != r and a[i, c]: a[i] ^= a[r]
        r += 1
    return r
codes = (mats * (1 << np.arange(mu * mu))).sum(1)
RANK = np.zeros(1 << (mu * mu));
for m, c in zip(mats, codes): RANK[c] = rk(m)
DIST = np.sqrt(RANK[np.bitwise_xor.outer(np.arange(512), np.arange(512))])

def score_from_D(Dm, wires, cuts, leg, hub):
    """Dm: distance function on indices. leg[p] index of party p, hub[k] = (o,o')"""
    L = sum(Dm(leg[a], leg[b]) for a, b in wires)
    tot = 0.0
    for k, (side, _) in enumerate(cuts):
        o, o2 = hub[k]
        H = sum(Dm(leg[a], o if a in side else o2) + Dm(leg[b], o if b in side else o2) for a, b in wires)
        dl = Dm(o, o2)
        if dl < 1e-12:
            if L - H > 1e-9: return 1e9
            continue
        tot += max((L - H) / dl, 0.0)
    return tot

def F_rho(wires, cuts, restarts=40, seed=0):
    rng = np.random.default_rng(seed)
    npts = 5 + 2 * len(cuts)
    Dm = lambda i, j: DIST[i, j]
    best = 0
    for r in range(restarts):
        x = list(rng.integers(0, 512, npts))
        def val(x):
            return score_from_D(Dm, wires, cuts, {p: x[i] for i, p in enumerate(P)}, [(x[5 + 2 * k], x[6 + 2 * k]) for k in range(len(cuts))])
        cur = val(x); improved = True
        while improved:
            improved = False
            for i in rng.permutation(npts):
                old = x[i]; bv, bc = cur, old
                for c in range(512):
                    x[i] = c; v = val(x)
                    if v > bv + 1e-12 and v < 1e8: bv, bc = v, c
                x[i] = bc
                if bc != old: cur = bv; improved = True
        best = max(best, cur)
    return best

def F_E(wires, cuts, dim=5, restarts=30, seed=0):
    rng = np.random.default_rng(seed)
    npts = 5 + 2 * len(cuts)
    def f(z):
        X = z.reshape(npts, dim)
        Dm = lambda i, j: np.linalg.norm(X[i] - X[j])
        leg = {p: i for i, p in enumerate(P)}
        hub = [(5 + 2 * k, 6 + 2 * k) for k in range(len(cuts))]
        L = sum(Dm(leg[a], leg[b]) for a, b in wires)
        tot = 0
        for k, (side, _) in enumerate(cuts):
            o, o2 = hub[k]
            H = sum(Dm(leg[a], o if a in side else o2) + Dm(leg[b], o if b in side else o2) for a, b in wires)
            tot += max((L - H) / max(Dm(o, o2), 1e-9), 0)
        return -tot
    best = 0
    for r in range(restarts):
        z0 = rng.normal(size=npts * dim)
        res = minimize(f, z0, method='Nelder-Mead', options={'maxiter': 20000, 'maxfev': 20000, 'xatol': 1e-9, 'fatol': 1e-12})
        res = minimize(f, res.x, method='Powell', options={'maxiter': 20000})
        best = max(best, -res.fun)
    return best

def cut(side):
    s = frozenset(side); return (s, frozenset(P) - s)

if __name__ == '__main__':
    problems = {
        'crossing 0S,AD (calib)': ([('0', 'S'), ('A', 'D')], [cut('0A'), cut('0D')]),
        'two squares, 4 cuts': ([('0', 'S'), ('A', 'D'), ('C', 'D')], [cut('0A'), cut('0D'), cut('0C'), cut(['0', 'D'])]),
        '0S,AD,CD rows/cols with C,A split': ([('0', 'S'), ('A', 'D'), ('C', 'D')], [cut('0AC'), cut('0D'), cut('0A'), cut('0C')]),
        '0S,AD,CD,AC 3 cuts': ([('0', 'S'), ('A', 'D'), ('C', 'D'), ('A', 'C')], [cut('0A'), cut('0C'), cut('0D')]),
        '0S,AD,CD 3 cuts {0A},{0C},{0D}': ([('0', 'S'), ('A', 'D'), ('C', 'D')], [cut('0A'), cut('0C'), cut('0D')]),
    }
    for nm, (w, c) in problems.items():
        fr = F_rho(w, c, restarts=int(sys.argv[1]) if len(sys.argv) > 1 else 15)
        fe = F_E(w, c, restarts=int(sys.argv[2]) if len(sys.argv) > 2 else 15)
        print(f"{nm:40s} F_rho3 = {fr:.4f}   F_E = {fe:.4f}   ratio {fr/fe:.4f}", flush=True)
