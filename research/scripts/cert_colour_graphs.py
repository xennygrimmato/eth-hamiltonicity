"""Colour model with vertex-dependent weights on general small graphs.

Constraint system (normalised colour-0 weight = 1 at every vertex, as forced by Hamiltonian cycles):
    for every cycle C of G avoiding the root:   1 + sum_{c=1}^{q-1} prod_{v in C} y[v,c] = 0.
(This is the 'kill every non-root cycle' version; the exact-filter requirement only needs it for
cycles that occur as a component of a 2-factor whose other components can be killed, so this is a
slight over-requirement used for exploration.)  Only the vertex SET of a cycle matters.

Usage: python3 cert_colour_graphs.py complete m      (K_m, root excluded -> all subsets of size>=3 of m-1)
       python3 cert_colour_graphs.py ladder M         (cycles = column intervals of a 2 x M ladder)
       python3 cert_colour_graphs.py random3 n seed   (random cubic graph)
"""
import sys, itertools
import numpy as np
from scipy.optimize import least_squares

def cycles_vertex_sets(n, edges, root):
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    sets = set()
    verts = [v for v in range(n) if v != root]
    for s in verts:  # cycles whose minimum vertex is s
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            for w in adj[v]:
                if w == root or w < s:
                    continue
                if w == s and len(path) >= 3:
                    sets.add(frozenset(path))
                elif w not in path:
                    stack.append((w, path + [w]))
    return [sorted(S) for S in sets]

def residual(z, nv, q, sets):
    k = nv * (q - 1)
    y = (z[:k] + 1j * z[k:]).reshape(nv, q - 1)
    out = []
    for S in sets:
        r = 1 + np.prod(y[S], axis=0).sum()
        out += [r.real, r.imag]
    return np.array(out)

def min_q(nv, sets, qmax=12, tries=40, seed=0):
    rng = np.random.default_rng(seed)
    for q in range(2, qmax + 1):
        best = np.inf
        for _ in range(tries):
            z0 = rng.normal(size=2 * nv * (q - 1))
            meth = "lm" if 2 * len(sets) >= len(z0) else "trf"
            s = least_squares(residual, z0, args=(nv, q, sets), method=meth, max_nfev=3000,
                              xtol=1e-15, ftol=1e-15, gtol=1e-15)
            c = np.sqrt((s.fun ** 2).sum())
            best = min(best, c)
            if c < 1e-9:
                break
        print(f"  q={q}: best residual {best:.2e}", flush=True)
        if best < 1e-9:
            return q
    return None

if __name__ == "__main__":
    kind = sys.argv[1]
    if kind == "complete":
        m = int(sys.argv[2])  # vertices besides root
        sets = [list(S) for r in range(3, m + 1) for S in itertools.combinations(range(m), r)]
        print(f"K_{m+1}: {len(sets)} cycle vertex-sets"); print("min q =", min_q(m, sets))
    elif kind == "ladder":
        M = int(sys.argv[2])
        sets = [list(range(i, j + 1)) for i in range(M) for j in range(i + 1, M)]  # columns as units
        print(f"ladder M={M}"); print("min q =", min_q(M, sets))
    elif kind == "random3":
        n, seed = int(sys.argv[2]), int(sys.argv[3])
        import networkx as nx
        G = nx.random_regular_graph(3, n, seed=seed)
        sets = cycles_vertex_sets(n, list(G.edges()), root=0)
        print(f"random cubic n={n}: {len(sets)} root-avoiding cycle vertex-sets")
        print("min q =", min_q(n, sets))
