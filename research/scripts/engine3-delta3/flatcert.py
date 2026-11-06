"""flatcert.py -- what the whole flattening world certifies on small hyperedge configurations.

Model (engine2-decorrelated.md section 8.2, generalised to any configuration and any number of merges):
  a configuration = nodes, crossing edges (each an N x N identity), merges = partitions of the nodes into groups;
  a term under merge k is a network on the groups of P_k with bond exponents e_{GG'} (log_N of bond dims);
  a contraction M = edge-disjoint oriented paths (orientation per edge in {0,+,-}); n_G = sum_{v in G}(out_v - in_v).
  A merge-k term passes every flattening inequality of M iff  sum_{G in S} n_G <= e(S | S^c) for every S subset of P_k.
  Cheapest passing term: d_k(M) = LP min sum e  s.t. the cut constraints.  The method certifies
  cost >= min_k d_k(M) (in units of log N) for some term, and the tailored profile shows nothing more is certified.
  D = max_M min_k d_k(M);  the certified rho is D / (number of crossing edges), since every edge costs 1 under every
  merge in the trivial evaluation (all edges here cross every merge).
Configurations: C = AG(2,3) two anti-diagonal lines (Majdoddin 4.7), 3 merges;  P = prism (K_3 x K_2 = 3x3 level
minus three nodes), 2 merges = the two perfect matchings of the complementary hexagon;  T4 = AG(2,4) translation
matching with slopes 0,1,w as merges (Majdoddin 4.8), 8 edges, 16 nodes, 4 groups per merge.
"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog

def lp_cost(ngroups, n):
    """min sum_{G<G'} e_GG' s.t. for every nonempty proper S: sum_{G in S, G' notin S} e_GG' >= |sum_{G in S} n_G|."""
    pairs = list(itertools.combinations(range(ngroups), 2)); pid = {p: i for i, p in enumerate(pairs)}
    A, b = [], []
    for r in range(1, ngroups // 2 + 1):
        for S in itertools.combinations(range(ngroups), r):
            if r == ngroups / 2 and 0 not in S: continue
            Sset = set(S); row = np.zeros(len(pairs))
            for (G, H) in pairs:
                if (G in Sset) != (H in Sset): row[pid[(G, H)]] = -1
            A.append(row); b.append(-abs(sum(n[G] for G in S)))
    if ngroups == 3:  # closed form check: max |n_G|
        return max(abs(x) for x in n)
    res = linprog(np.ones(len(pairs)), A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, None)] * len(pairs), method='highs')
    return res.fun

def certify(nodes, edges, merges, name):
    E = len(edges)
    best = (-1, None)
    hist = {}
    for orient in itertools.product((0, 1, -1), repeat=E):
        if all(o == 0 for o in orient): continue
        flow = {v: 0 for v in nodes}
        for (u, v), o in zip(edges, orient):
            flow[u] += o; flow[v] -= o
        ds = []
        for groups in merges:
            n = [sum(flow[v] for v in G) for G in groups]
            ds.append(lp_cost(len(groups), n))
        val = min(ds)
        hist[val] = hist.get(val, 0) + 1
        if val > best[0]: best = (val, (orient, ds))
    print(f"{name}: nodes {len(nodes)}, crossing edges {E}, merges {len(merges)} (groups per merge {[len(g) for g in merges]})")
    print(f"  flattening certificate D = {best[0]:.3f} of full {E}  ->  certified rho >= {best[0]/E:.4f}")
    print(f"  attained by orientation {best[1][0]} with per-merge d_k = {[round(x,3) for x in best[1][1]]}")
    return best[0]

# --- C: AG(2,3), a_i = (i,-i), b_i = (i,1-i); merge k pairs a_i with b_{i+k}
A = [('a', i) for i in range(3)]; B = [('b', i) for i in range(3)]
nodesC = A + B
edgesC = [(('a', i), ('a', j)) for i in range(3) for j in range(i + 1, 3)] + [(('b', i), ('b', j)) for i in range(3) for j in range(i + 1, 3)]
mergesC = [[[('a', i), ('b', (i + k) % 3)] for i in range(3)] for k in range(3)]
DC = certify(nodesC, edgesC, mergesC, "C (AG(2,3) two lines)")

# --- prism: nodes of the 3x3 grid (r,c) in {(1,1),(1,2),(2,2),(2,3),(3,3),(3,1)}; edges = different row and column
nodesP = [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 1)]
edgesP = [(u, v) for u, v in itertools.combinations(nodesP, 2) if u[0] != v[0] and u[1] != v[1]]
rows = [[v for v in nodesP if v[0] == r] for r in (1, 2, 3)]
cols = [[v for v in nodesP if v[1] == c] for c in (1, 2, 3)]
DP = certify(nodesP, edgesP, [rows, cols], "P (prism, two orthogonal matchings)")

# --- AG(2,4) translation matching.  F4 = {0,1,2,3} with 2 = w, 3 = w^2; addition = xor.
MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
pts = [(x, y) for x in range(4) for y in range(4)]
edgesT = [((x, c), (x, c ^ 1)) for x in range(4) for c in (0, 2)]
def groups_of_slope(s): return [[(x, y) for (x, y) in pts if (y ^ MUL[s][x]) == c] for c in range(4)]
mergesT = [groups_of_slope(s) for s in (0, 1, 2)]
DT = certify(pts, edgesT, mergesT, "T4 (AG(2,4) translation matching, slopes 0,1,w)")
mergesT4 = [groups_of_slope(s) for s in (0, 1, 2, 3)]
DT4 = certify(pts, edgesT, mergesT4, "T4 with all four non-vertical slopes as merges")

# sanity: the rectangle (single crossing) must certify 1 of 2 (rho >= 1/2)
nodesR = [(1, 1), (1, 2), (2, 1), (2, 2)]
edgesR = [((1, 1), (2, 2)), ((1, 2), (2, 1))]
certify(nodesR, edgesR, [[[(1, 1), (1, 2)], [(2, 1), (2, 2)]], [[(1, 1), (2, 1)], [(1, 2), (2, 2)]]], "rectangle (sanity)")
