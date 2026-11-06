"""realdims.py -- twoterm.py with bond dimensions NOT restricted to powers of 2 (exact rank inequalities, any field), on a
restricted family: K_4 patterns with all four 'adjacent' bonds of dimension x in {1..4} and the two diagonals y, z in {1..16}
(8-cycle two-cell; raw = (2; 16,16)), resp. K_3 patterns (x,y,z) in {1..8}^3 for the prism (raw (8,8,8)).
Rank of a term under contraction M is <= min_S 2^{|E|-n_S} prod_{delta S} d; pair excluded iff some M has
ratio1 + ratio2 < 1 (ratio = that bound / 2^{|E|}).  Then the four frontier sets (GG, GH, HG, HH) and the criterion
min_q max_t <q,c(t)> + 1 < raw over all pairs of pieces whose patterns come from this family (costs real)."""
import itertools, numpy as np, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from flatgap import make, C8, E8_two, PR, EPR

def ratios(n, pairs, dims):
    r = n.shape[1]; best = np.full(len(n), 1.0)  # S = empty
    for size in range(1, r):
        for S in itertools.combinations(range(r), size):
            cut = sum(np.log2(d) for (i, j), d in zip(pairs, dims) if (i in S) != (j in S))
            best = np.minimum(best, 2.0 ** (cut - n[:, list(S)].sum(1)))
    return best

def run(nodes, edges, merges, raw, family, label):
    B = make(nodes, edges, merges)
    U = [np.unique(B[k], axis=0, return_inverse=True) for k in range(2)]
    inv = [U[k][1].ravel() for k in range(2)]
    r = len(merges[0]); pairs = list(itertools.combinations(range(r), 2))
    pats = [p for p in family if np.log2(np.prod(p)) <= raw + 1e-9]
    cost = np.array([np.log2(np.prod(p)) for p in pats])
    R = [np.array([ratios(U[k][0], pairs, p) for p in pats]) for k in range(2)]  # patterns x classes
    print(f"[{label}] {len(pats)} patterns", flush=True)
    ok = {}
    for k1, k2 in itertools.product(range(2), repeat=2):
        # m[p, j] = min_{i ~ j} R[k1][p, i] over states mapping to class i (merge k1) and j (merge k2)
        m = np.full((len(pats), len(U[k2][0])), np.inf)
        for s0 in range(0, len(inv[0]), 20000):
            ii = inv[k1][s0:s0 + 20000]; jj = inv[k2][s0:s0 + 20000]
            vals = R[k1][:, ii]
            # scatter-min
            np.minimum.at(m.T, jj, vals.T)
        X = np.zeros((len(pats), len(pats)), bool)
        for a in range(len(pats)):
            X[a] = np.min(m[a][None, :] + R[k2], axis=1) < 1 - 1e-12
        ok[(k1, k2)] = ~X
    # frontier summary GH
    for key in ok:
        surv = [(cost[a], cost[b]) for a, b in zip(*np.nonzero(ok[key]))]
        fr = sorted({(round(x, 3), round(y, 3)) for x, y in surv if not any((x2 <= x and y2 <= y and (x2, y2) != (x, y)) for x2, y2 in surv)})
        print(f"   frontier {'GH'[key[0]]}{'GH'[key[1]]}: {fr}", flush=True)
    # criterion: piece t has a G-pattern and an H-pattern (costs g_t, h_t); require all four pair tests to pass.
    lv = np.array(sorted(set(np.round(cost, 9)))); L = len(lv); idx = np.searchsorted(lv, np.round(cost, 9))
    OK = {}
    for key in ok:
        M = np.zeros((L, L), bool)
        a, b = np.nonzero(ok[key]); M[idx[a], idx[b]] = True
        M = np.maximum.accumulate(np.maximum.accumulate(M, 0), 1)   # monotone closure in both costs
        OK[key] = M
    def mmq(a1, b1, a2, b2):   # min_{q in [0,1]} max(q a1 + (1-q) b1, q a2 + (1-q) b2), vectorised
        v0 = np.maximum(b1, b2); v1 = np.maximum(a1, a2)
        den = (a1 - b1) - (a2 - b2)
        with np.errstate(divide='ignore', invalid='ignore'):
            q = np.where(den != 0, (b2 - b1) / den, -1.0)
        vq = np.where((q > 0) & (q < 1), q * a1 + (1 - q) * b1, np.inf)
        return np.minimum(np.minimum(v0, v1), vq)
    best = (np.inf, None)
    for g1 in range(L):
        h1, g2, h2 = np.meshgrid(np.arange(L), np.arange(L), np.arange(L), indexing='ij')
        mask = OK[(0, 0)][g1, g2] & OK[(1, 1)][h1, h2] & OK[(0, 1)][g1, h2] & OK[(1, 0)][h1, g2]
        if not mask.any(): continue
        v = mmq(lv[g1], lv[h1[mask]], lv[g2[mask]], lv[h2[mask]]) + 1
        k = int(np.argmin(v))
        if v[k] < best[0] - 1e-9:
            best = (float(v[k]), ((lv[g1], lv[h1[mask]][k]), (lv[g2[mask]][k], lv[h2[mask]][k])))
    print(f"[{label}] {L} cost levels; minimal criterion (family, real costs): {best[0]:.4f} at {best[1]} (trade iff < {raw})", flush=True)

if __name__ == '__main__':
    famP = list(itertools.product(range(1, 9), repeat=3))
    run(list(PR['nodes']), EPR, [PR['G'], PR['H']], 9, famP, "prism")
    fam8 = [(x, y, x, x, z, x) for x in range(1, 5) for y in range(1, 17) for z in range(1, 17)]  # pairs order (01,02,03,12,13,23)
    run(C8['nodes'], E8_two, [C8['G'], C8['H']], 12, fam8, "8-cycle two-cell")
