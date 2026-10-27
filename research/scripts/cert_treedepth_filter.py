"""Exact #HC filter with q = 1 + (elimination-forest height) colours and vertex weights in Z.

Construction (see certificates.md, section 'Signed colour filter'):
  take an elimination forest F of G - r (every edge of G - r joins an ancestor/descendant pair),
  depth(v) >= 1.  Colours 0..D.  Weights w(v,0) = 1 for all v (root r: colour 0 only).
  For j >= 1:  w(v,j) = 0 if depth(v) < j,  -j if depth(v) == j,  1 if depth(v) > j.
Claim: for every cycle C of G - r, sum_j prod_{v in C} w(v,j) = 0, hence
  sum_{2-factors X} sum_{colourings constant on components, root colour 0} prod_v w(v, col v) = #HC(G).
We check the identity by brute force on small random graphs.
"""
import itertools, random, sys
import networkx as nx

def elimination_forest(G):
    """Greedy elimination forest: pick a max-degree vertex (or separator-ish) as root of each component."""
    depth = {}
    def rec(H, d):
        for comp in nx.connected_components(H):
            S = H.subgraph(comp).copy()
            # choose vertex minimising the largest remaining component
            best = min(S.nodes, key=lambda v: max((len(c) for c in nx.connected_components(S.subgraph(set(S) - {v}))), default=0))
            depth[best] = d
            rec(S.subgraph(set(S) - {best}).copy(), d + 1)
    rec(G, 1)
    return depth

def two_factors(G):
    E = list(G.edges())
    nodes = list(G.nodes())
    inc = {v: [i for i, e in enumerate(E) if v in e] for v in nodes}
    # backtracking over edges
    res = []
    deg = {v: 0 for v in nodes}
    chosen = []
    def bt(i):
        if i == len(E):
            if all(deg[v] == 2 for v in nodes):
                res.append(list(chosen))
            return
        a, b = E[i]
        # prune: remaining edges must be able to fill
        if deg[a] < 2 and deg[b] < 2:
            deg[a] += 1; deg[b] += 1; chosen.append(E[i])
            bt(i + 1)
            deg[a] -= 1; deg[b] -= 1; chosen.pop()
        bt(i + 1)
    bt(0)
    return res

def check(G, r):
    H = G.copy(); H.remove_node(r)
    depth = elimination_forest(H)
    D = max(depth.values()) if depth else 0
    def w(v, j):
        if v == r:
            return 1 if j == 0 else 0
        if j == 0:
            return 1
        d = depth[v]
        return 0 if d < j else (-j if d == j else 1)
    total = 0; hc = 0
    for X in two_factors(G):
        F = nx.Graph(); F.add_nodes_from(G.nodes()); F.add_edges_from(X)
        comps = list(nx.connected_components(F))
        if len(comps) == 1:
            hc += 1
        val = 1
        for C in comps:
            if r in C:
                s = 1
                for v in C: s *= w(v, 0)
            else:
                s = 0
                for j in range(D + 1):
                    p = 1
                    for v in C: p *= w(v, j)
                    s += p
            val *= s
        total += val
    return total, hc, D + 1

if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    for trial in range(30):
        n = random.choice([8, 10, 12, 14])
        d = random.choice([3, 4])
        if n * d % 2: continue
        G = nx.random_regular_graph(d, n, seed=random.randrange(10**6))
        total, hc, q = check(G, 0)
        print(f"n={n} d={d}: signed sum={total}  #HC={hc}  colours q={q}  {'OK' if total == hc else 'MISMATCH'}")
