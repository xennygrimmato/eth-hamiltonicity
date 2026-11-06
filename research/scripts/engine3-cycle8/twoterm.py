"""twoterm.py -- EXACT necessary conditions on ANY two-term identity f = P1 + P2 (N = 2, one bit per edge, any field), with
true D1 costs restricted to bond dimensions that are powers of 2 (cost vector c(t) = (c_G(t), c_H(t)) integer).
Each piece has a G-network representation (bonds e^G_t) and an H-network representation (bonds e^H_t).  A pair of
single-merge patterns (piece 1 under merge k, piece 2 under merge k') is excluded iff some contraction M has
2^-gap1 + 2^-gap2 < 1 (flatgap.py); this is necessary for each of the four combinations (k,k') in {G,H}^2.
Frontier sets F_kk' = surviving (cost_k(P1), cost_k'(P2)) (monotone: everything above a survivor survives).
Then enumerate all integer cost vectors (c_G(1),c_H(1),c_G(2),c_H(2)) in [0,raw]^4 consistent with all four frontiers and
report the minimum of  min_q max_t <q,c(t)> + log2 2  (the fixed-N0 trade criterion; trade iff < raw)."""
import itertools, numpy as np, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from flatgap import make, gaps, C8, E8_two, E8_all, PR, EPR

def frontier_sets(nodes, edges, merges, raw, emax):
    B = make(nodes, edges, merges)
    U = [np.unique(B[k], axis=0, return_inverse=True) for k in range(2)]
    r = len(merges[0]); pairs = list(itertools.combinations(range(r), 2))
    pats = [p for p in itertools.product(range(emax + 1), repeat=len(pairs)) if sum(p) <= raw]
    cost = np.array([sum(p) for p in pats])
    g = [np.array([gaps(U[k][0], dict(zip(pairs, p))) for p in pats]) for k in range(2)]
    # state-indexed incidence of class
    nS = len(B[0]); inv = [U[k][1].ravel() for k in range(2)]
    surv = {}
    for k1, k2 in itertools.product(range(2), repeat=2):
        Rel = np.zeros((len(U[k1][0]), len(U[k2][0])), np.float32); Rel[inv[k1], inv[k2]] = 1
        A1 = (g[k1] >= 1).astype(np.float32); A2 = (g[k1] >= 2).astype(np.float32)
        C1 = (g[k2] >= 1).astype(np.float32); C2 = (g[k2] >= 2).astype(np.float32)
        X = ((A1 @ Rel) @ C2.T > 0) | ((A2 @ Rel) @ C1.T > 0)
        ok = np.zeros((raw + 1, raw + 1), bool)
        for i, j in zip(*np.nonzero(~X)): ok[cost[i], cost[j]] = True
        # monotone closure (a survivor at (a,b) => all (a',b') >= survive in cost terms: bigger bonds pass more tests)
        for a in range(raw + 1):
            for b in range(raw + 1):
                if ok[a, b]:
                    ok[a:, b:] = True
        surv[(k1, k2)] = ok
        fr = [(a, b) for a in range(raw + 1) for b in range(raw + 1) if ok[a, b] and not (a > 0 and ok[a - 1, b]) and not (b > 0 and ok[a, b - 1])]
        print(f"   frontier piece1 under {'GH'[k1]}, piece2 under {'GH'[k2]}: {fr}", flush=True)
    return surv

def crit(c1, c2):
    qs = np.linspace(0, 1, 2001)
    return float(np.min(np.maximum(qs * c1[0] + (1 - qs) * c1[1], qs * c2[0] + (1 - qs) * c2[1]))) + 1.0

def analyse(nodes, edges, merges, raw, emax, label):
    print(f"[{label}] raw {raw}")
    S = frontier_sets(nodes, edges, merges, raw, emax)
    best = (np.inf, None)
    for a1, h1, a2, h2 in itertools.product(range(raw + 1), repeat=4):
        c1 = (a1, h1); c2 = (a2, h2)
        if S[(0, 0)][a1, a2] and S[(1, 1)][h1, h2] and S[(0, 1)][a1, h2] and S[(1, 0)][h1, a2]:
            v = crit(c1, c2)
            if v < best[0] - 1e-9: best = (v, (c1, c2))
    print(f"[{label}] minimal fixed-N0 criterion over all cost vectors consistent with every flattening test: {best[0]:.4f} at {best[1]}"
          f"  -> {'TRADE NOT EXCLUDED' if best[0] < raw - 1e-9 else 'no two-term trade (power-of-2 bonds)'}", flush=True)

if __name__ == '__main__':
    analyse(list(PR['nodes']), EPR, [PR['G'], PR['H']], 9, 3, "prism")
    analyse(C8['nodes'], E8_two, [C8['G'], C8['H']], 12, 4, "8-cycle two-cell")
