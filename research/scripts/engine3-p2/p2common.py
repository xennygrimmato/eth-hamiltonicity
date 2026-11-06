"""P2 common code: instances, exact/modular feasibility of the per-occurrence linear system.

Design (Def. layout / [DL] Def. 5.1(c)) at points t = 1..Q:
  part[t][i]   group of variable i at point t (r groups)
  alpha[t][e]  group assigned to clause e at point t
  rows[t][h]   list of integer rows; each row = dict {var: coeff}, support inside S_{t,h}
Occurrence o = (e, v). Unknown P_o(T) = e_v + sum_{k=1..R} T^k c_k (deg <= R).
Constraint: for every t and h != alpha[t][e]:  P_o(t)|_{S_{t,h}} in span(rows[t][h]).
Given the design, occurrences decouple; the system for o splits into connected components
(coordinates linked by rows at foreign points); only the component of v is inhomogeneous,
all other coordinates can be set to 0.  So R_o = min R making v's component feasible.
"""
import random, itertools
import numpy as np
import networkx as nx

P1 = 2147483629      # primes < 2^31
P2 = 2147483587

# ---------------------------------------------------------------- instances
def linear_3cnf(n, b, seed):
    """random 3-uniform b-regular *linear* hypergraph (no two clauses share 2 vars)."""
    assert (n * b) % 3 == 0
    rng = random.Random(seed)
    for _ in range(100000):
        stubs = [v for v in range(n) for _ in range(b)]
        rng.shuffle(stubs)
        cl = [tuple(sorted(stubs[3*j:3*j+3])) for j in range(len(stubs)//3)]
        if any(len(set(c)) < 3 for c in cl):
            continue
        pairs = set(); ok = True
        for c in cl:
            for pr in itertools.combinations(c, 2):
                if pr in pairs: ok = False; break
                pairs.add(pr)
            if not ok: break
        if ok:
            return cl
    raise RuntimeError("no linear hypergraph found")

def graph_2cnf(n, d, seed):
    """clauses = edges of a random d-regular graph with girth >= 4 (primal graph = that graph)."""
    s = seed
    while True:
        G = nx.random_regular_graph(d, n, seed=s); s += 1000
        if nx.is_connected(G) and sum(nx.triangles(G).values()) == 0:
            return [tuple(sorted(e)) for e in G.edges()]

def make_instance(fam, n, seed):
    if fam == 'L3':  return linear_3cnf(n, 3, seed)      # 3-CNF, each var in 3 clauses
    if fam == 'L4':  return linear_3cnf(n, 4, seed)      # 3-CNF, each var in 4 clauses
    if fam == 'G3':  return graph_2cnf(n, 3, seed)       # primal graph cubic, girth >= 4
    if fam == 'G4':  return graph_2cnf(n, 4, seed)
    raise ValueError(fam)

def primal_tw_upper(n, clauses):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for c in clauses:
        G.add_edges_from(itertools.combinations(c, 2))
    from networkx.algorithms.approximation import treewidth_min_fill_in, treewidth_min_degree
    return min(treewidth_min_fill_in(G)[0], treewidth_min_degree(G)[0])

# ---------------------------------------------------------------- linear algebra
def rank_modp(M, p=P1):
    M = np.array(M, dtype=np.int64) % p
    m, N = M.shape
    r = 0
    for c in range(N):
        if r == m: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        piv = r + nz[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        col = M[:, c].copy(); col[r] = 0
        idx = np.nonzero(col)[0]
        if len(idx):
            M[idx] = (M[idx] - (col[idx, None] * M[r][None, :]) % p) % p
        r += 1
    return r

def consistent_modp(A, b, p=P1):
    """single elimination of [A|b]: True iff b is in the column space of A (mod p)."""
    M = np.array([row + [bb] for row, bb in zip(A, b)], dtype=np.int64) % p
    m, N1 = M.shape
    r = 0
    for c in range(N1):
        if r == m: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        if c == N1 - 1: return False
        piv = r + nz[0]
        if piv != r: M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        idx = np.nonzero(M[r+1:, c])[0] + r + 1
        if len(idx):
            M[idx] = (M[idx] - (M[idx, c][:, None] * M[r][None, :]) % p) % p
        r += 1
    return True

def rank_exact(M):
    from sympy.polys.matrices import DomainMatrix
    from sympy import ZZ, QQ
    if len(M) == 0: return 0
    dm = DomainMatrix([[ZZ(int(x)) for x in row] for row in M], (len(M), len(M[0])), ZZ).convert_to(QQ)
    return dm.rank()

# ---------------------------------------------------------------- per-occurrence system
def occ_system(design, e, v, R):
    """Return (A, b) of the component-of-v system for occurrence (e,v) at degree R,
    or None if v has no foreign point at all (trivially feasible)."""
    part, alpha, rows, Q = design['part'], design['alpha'], design['rows'], design['Q']
    # foreign (t,h) rows; build coupling graph: coord i -- (t,h) row-block
    # coordinate i is constrained at t iff part[t][i] != alpha[t][e]
    # component: start from v; at each foreign point t of coordinate i, block (t, part[t][i])
    # links i to every coordinate in the support of rows[t][h].
    comp = {v}; stack = [v]; blocks = set()
    while stack:
        i = stack.pop()
        for t in range(Q):
            h = part[t][i]
            if h == alpha[t][e]: continue
            rl = rows[t][h]
            if not any(i in row for row in rl):
                continue          # p_i(t) = 0 forced, no coupling
            blocks.add((t, h))
            for row in rl:
                for j in row:
                    if j not in comp:
                        comp.add(j); stack.append(j)
    comp = sorted(comp); ci = {i: k for k, i in enumerate(comp)}
    blocks = sorted(blocks)
    mu = {}
    for (t, h) in blocks:
        for jr in range(len(rows[t][h])):
            mu[(t, h, jr)] = len(mu)
    nC = len(comp) * R
    N = nC + len(mu)
    A = []; bvec = []
    for i in comp:
        for t in range(Q):
            h = part[t][i]
            if h == alpha[t][e]: continue
            row = [0] * N
            tt = t + 1                         # points are 1..Q
            for k in range(1, R + 1):
                row[ci[i] * R + (k - 1)] = tt ** k
            if (t, h) in blocks:
                for jr, rw in enumerate(rows[t][h]):
                    if i in rw:
                        row[nC + mu[(t, h, jr)]] = -rw[i]
            A.append(row); bvec.append(-1 if i == v else 0)
    return A, bvec

def feasible(design, e, v, R, exact=False):
    A, b = occ_system(design, e, v, R)
    if len(A) == 0: return True
    if len(A[0]) == 0:
        return all(x == 0 for x in b)
    Ab = [row + [bb] for row, bb in zip(A, b)]
    if exact:
        return rank_exact(A) == rank_exact(Ab)
    return consistent_modp(A, b)

def foreign_count(design, e, v):
    return sum(1 for t in range(design['Q']) if design['part'][t][v] != design['alpha'][t][e])

def lower_count(design, e, v):
    """#points where v is foreign and no row of its group touches v  (p_v must vanish there)."""
    Q = design['Q']; c = 0
    for t in range(Q):
        h = design['part'][t][v]
        if h != design['alpha'][t][e] and not any(v in rw for rw in design['rows'][t][h]):
            c += 1
    return c

def min_R_occ(design, e, v, exact=False, hint=None):
    lo = lower_count(design, e, v); hi = foreign_count(design, e, v)
    if hint is not None and lo < hint <= hi:
        if feasible(design, e, v, hint, exact=exact):
            R = hint
            while R - 1 >= lo and feasible(design, e, v, R - 1, exact=exact): R -= 1
            return R
        lo = hint + 1
    for R in range(lo, hi + 1):
        if feasible(design, e, v, R, exact=exact):
            return R
    return hi   # p_v = prod over foreign points (1 - T/t) always works

def occurrences(clauses):
    return [(e, v) for e, c in enumerate(clauses) for v in c]

def design_R(design, clauses, exact=False):
    Rs = {}
    for (e, v) in occurrences(clauses):
        Rs[(e, v)] = min_R_occ(design, e, v, exact=exact)
    return max(Rs.values()), Rs

def row_l1(rw): return sum(abs(x) for x in rw.values())
