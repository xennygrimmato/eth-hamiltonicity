"""lib3m.py -- three-merge (rows r, columns c, diagonals r-c) flattening machinery for Delta_3 at N0 = 2^m0 (m0 = 1, 2).
Orientations at bit level: each edge carries m0 bits, each bit fixed (removed) or split '+' (string at lower node -> X) or
'-'.  Per edge only (p, m) = (#+, #-) matters.  For merge k: x_g, y_g = open legs of group g on side X / Y.
A triangle network under merge k with log-bonds (x01,x02,x12): log2 rank across X|Y <= min_s [sum_g legs of g opposite s_g
+ sum_{s_g != s_h} x_gh] (network min-cut; valid over every field).  With total cost a the best shape gives Phi_{o,k}(a);
the inverse (least total cost reaching log-rank t) is  ginv = max(max_g A_g, sum_g A_g / 2),  A_g = max(0, t - M_g),
M_g = min over the two sides isolating g of the legs (and t <= |o| always).  [verified against an LP in floor_finite.py]"""
import itertools, numpy as np
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
MER = {'r': lambda v: v[0], 'c': lambda v: v[1], 'd': lambda v: (v[0] - v[1]) % 3}
S8 = list(itertools.product((0, 1), repeat=3)); PAIRS = [(0, 1), (0, 2), (1, 2)]
CUT = np.array([[1 if s[g] != s[h] else 0 for (g, h) in PAIRS] for s in S8])

def states(m0):
    return [(p, m) for p in range(m0 + 1) for m in range(m0 + 1 - p)]

def enumerate_orients(m0):
    ST = states(m0)
    idx = np.array(list(itertools.product(range(len(ST)), repeat=9)), dtype=np.int8)
    P = np.array([s[0] for s in ST], np.int16)[idx]; M = np.array([s[1] for s in ST], np.int16)[idx]
    n = idx.shape[0]; X = {}; Y = {}
    for k, gf in MER.items():
        x = np.zeros((n, 3), np.int16); y = np.zeros((n, 3), np.int16)
        for e, (u, v) in enumerate(edges):
            p, m = P[:, e], M[:, e]
            x[:, gf(u)] += p; y[:, gf(v)] += p; x[:, gf(v)] += m; y[:, gf(u)] += m
        X[k] = x; Y[k] = y
    rk = (P + M).sum(1)
    return idx, X, Y, rk

def legs8(x, y):
    return np.stack([sum((y[:, g] if s[g] == 0 else x[:, g]) for g in range(3)) for s in S8], 1)

def Mg(L8):
    # side index of s = (s0,s1,s2) in S8 is 4 s0 + 2 s1 + s2; sides isolating g: g=0 -> (1,0,0),(0,1,1): 4,3; g=1 -> 2,5; g=2 -> 1,6
    return np.stack([np.minimum(L8[:, 4], L8[:, 3]), np.minimum(L8[:, 2], L8[:, 5]), np.minimum(L8[:, 1], L8[:, 6])], 1)

def ginv(M, t):
    A = np.maximum(0.0, t[:, None] - M)
    return np.maximum(A.max(1), A.sum(1) / 2.0)

def logbound(L8, logbonds):
    return np.min(L8 + (CUT @ np.asarray(logbonds, float))[None, :], axis=1)
