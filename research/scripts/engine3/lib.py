"""engine3 lib: exact tensors for crossing / hexagon / 3x3 level / Majdoddin's C, flattening ranks, cost functionals.

Conventions.  A configuration = nodes, edges (each edge = an equality of two strings of lam bits, one copy
("leg") at each end), merges = partitions of the nodes into groups.  Tensors are numpy int64 arrays with one
axis per leg (alphabet size N).  Exact rank: Gaussian elimination mod a prime P (default 2^31-1), which equals
the rational rank except for primes dividing certain minors; we report the mod-P rank and cross-check over R.

Cost functionals for a term T under a merge with groups G_1..G_m (legs grouped by the group of their node):
  c_flat(T) = min sum_{i<j} e_ij  s.t.  sum_{i in S, j notin S} e_ij >= log2 rank(T ; S | rest) for all S
              (LP; for m=2 this is log2 rank across the split; for m=3 it is
               max(max_i r_i, (r_1+r_2+r_3)/2), r_i = log2 rank(G_i | rest)).
              It is a LOWER bound for the bond bits of every network on the groups realising T, and equals the
              (L4) charge for k-local pieces (tensor products of one factor per pair of groups).
  c_net(T)  = sum log2 d_ij of an explicit network found by search (upper bound on the true network cost).
A decomposition sum_t T_t is charged per term its cheapest merge: c(T_t) = min_k c_k(T_t).
"""
import numpy as np, itertools, math
from scipy.optimize import linprog

P = 2147483647

def rank_modp(M, p=P):
    """exact rank of an integer matrix modulo the prime p (vectorised Gaussian elimination)."""
    A = np.array(M, dtype=np.int64) % p
    n, m = A.shape
    if n > m: A = A.T.copy(); n, m = m, n
    r = 0
    for c in range(m):
        if r == n: break
        piv = np.nonzero(A[r:, c])[0]
        if len(piv) == 0: continue
        i = r + piv[0]
        if i != r: A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        rows = np.nonzero(A[:, c])[0]; rows = rows[rows != r]
        if len(rows):
            f = A[rows, c].copy()
            # (f * A[r]) may overflow int64 for p ~ 2^31: split A[r] into 16-bit halves
            lo = A[r] & 0xFFFF; hi = A[r] >> 16
            t = (np.outer(f, hi) % p) * 65536 % p + np.outer(f, lo) % p
            A[rows] = (A[rows] - t) % p
        r += 1
    return r

def flat(T, left):
    """matrix of T with the legs in `left` as rows."""
    left = list(left); right = [i for i in range(T.ndim) if i not in left]
    M = np.transpose(T, left + right)
    return M.reshape(int(np.prod([T.shape[i] for i in left])), -1)

def frank(T, left, exact=True):
    M = flat(T, left)
    return rank_modp(M) if exact else int(np.linalg.matrix_rank(M.astype(float)))

def lp_cost(m, req):
    """min sum_{i<j} e_ij s.t. e(S|rest) >= req[S] (req: dict frozenset(S) -> bits), e >= 0."""
    pairs = list(itertools.combinations(range(m), 2))
    if m == 2: return max(req.get(frozenset([0]), 0), req.get(frozenset([1]), 0))
    A = []; b = []
    for S, v in req.items():
        A.append([-1.0 if ((i in S) != (j in S)) else 0.0 for (i, j) in pairs]); b.append(-v)
    res = linprog(np.ones(len(pairs)), A_ub=A, b_ub=b, bounds=[(0, None)] * len(pairs), method='highs')
    return res.fun

def group_legs(cfg, merge):
    """list of leg-index lists, one per group of merge (a list of node-sets)."""
    return [[l for l, (e, nd) in enumerate(cfg['legs']) if nd in G] for G in merge]

def cut_ranks(cfg, T, merge, exact=True):
    gl = group_legs(cfg, merge); m = len(gl); req = {}
    for r in range(1, m):
        for S in itertools.combinations(range(m), r):
            if 0 not in S and m > 2: continue  # complement symmetry
            if m == 2 and S != (0,): continue
            left = [l for g in S for l in gl[g]]
            rk = frank(T, left, exact)
            req[frozenset(S)] = math.log2(rk) if rk > 0 else -np.inf
            req[frozenset(set(range(m)) - set(S))] = req[frozenset(S)]
    return req

def c_flat(cfg, T, merge, exact=True):
    req = cut_ranks(cfg, T, merge, exact)
    if any(v == -np.inf for v in req.values()): return 0.0  # T = 0
    return lp_cost(len(merge), req)

def cost_vector(cfg, T, exact=True):
    return [c_flat(cfg, T, mg, exact) for mg in cfg['merges']]

# ---------------------------------------------------------------- configurations
def graph_config(nodes, edges, merges, N):
    """legs: one per (edge, end).  Target = product of [leg_e,0 == leg_e,1]."""
    legs = []
    for ei, (p, q) in enumerate(edges):
        legs += [(ei, p), (ei, q)]
    return dict(nodes=nodes, edges=edges, merges=merges, N=N, legs=legs)

def graph_tensor(cfg):
    """the target: product over edges of identities (legs 2e, 2e+1)."""
    N = cfg['N']; E = len(cfg['edges'])
    T = np.ones((1,), dtype=np.int64)
    I = np.eye(N, dtype=np.int64)
    out = I
    for e in range(1, E): out = np.multiply.outer(out, I)
    return out  # axes in order (e0 end0, e0 end1, e1 end0, ...)

def config_C(N):
    """Majdoddin's AG(2,3) configuration: triangles {a_i}, {b_i}; merge k groups {a_i, b_{i+k}}."""
    nodes = [('a', i) for i in range(3)] + [('b', i) for i in range(3)]
    edges = [(('a', i), ('a', j)) for i, j in ((0, 1), (1, 2), (0, 2))] + \
            [(('b', i), ('b', j)) for i, j in ((0, 1), (1, 2), (0, 2))]
    merges = [[{('a', i), ('b', (i + k) % 3)} for i in range(3)] for k in range(3)]
    return graph_config(nodes, edges, merges, N)

def config_hexagon(N):
    """3x2 grid as hexagon 1-2-3-4-5-6-1; rows {1,4},{2,5},{3,6}; columns {1,3,5},{2,4,6}."""
    nodes = list(range(1, 7)); edges = [(i, i % 6 + 1) for i in range(1, 7)]
    merges = [[{1, 4}, {2, 5}, {3, 6}], [{1, 3, 5}, {2, 4, 6}]]
    return graph_config(nodes, edges, merges, N)

def config_crossing(N):
    """crossing [x=v][y=u]: nodes x,y,u,v (one leg each); rows {x,y}|{u,v}, columns {x,u}|{y,v}."""
    nodes = ['x', 'y', 'u', 'v']; edges = [('x', 'v'), ('y', 'u')]
    merges = [[{'x', 'y'}, {'u', 'v'}], [{'x', 'u'}, {'y', 'v'}]]
    return graph_config(nodes, edges, merges, N)

def config_g33(N=None):
    nodes = [(r, c) for r in range(3) for c in range(3)]
    edges = [((r, c), (s, d)) for (r, c) in nodes for (s, d) in nodes if r < s and c != d]
    merges = [[{(r, c) for c in range(3)} for r in range(3)], [{(r, c) for r in range(3)} for c in range(3)]]
    return graph_config(nodes, edges, merges, N)
