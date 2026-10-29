#!/usr/bin/env python3
"""Tiny exact/heuristic study of rho_R(B) = min rank(I - M), supp M in S_R, on the full label
space B = ({0,1}x{0,1})^Q (r = 2), Q = 2,3,4.

  S_R = {(u,w): d_H(d_u, a_w) <= R-1};  outside S_R the entry of I-M is forced to delta_{uw}.

Lower bound: largest "triangular" set U (an ordering with all forced entries above and on the
diagonal, i.e. the allowed digraph induced on U is acyclic and loop-free) -- computed exactly
by an ILP with lazily added cycle constraints (scipy.optimize.milp).  rank >= |U| (Theorem 1).
Also the closed-form potential bound #{u: |d_u| - |a_u| >= R} (Cor. 1.1).
Upper bounds: commutative optimum (exact, from parity_template_bounds.GEN for Q<=4, here
recomputed as D * eps) and a NON-commutative heuristic: alternating least squares for a rank-k
matrix G = X Y^T matching the forced entries; success = forced-entry residual < 1e-10, then
checked again by an independent exact-rank test of the found M (numerical rank via SVD gap).
"""
import numpy as np, itertools, sys
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse.csgraph import connected_components

def labels(Q):
    L = []
    for a in range(2**Q):
        for d in range(2**Q):
            L.append((a, d))
    return L

def ham(x, y):
    return bin(x ^ y).count("1")

def allowed(Q, R):
    L = labels(Q); D = len(L)
    A = np.zeros((D, D), dtype=bool)
    for i, (a, d) in enumerate(L):
        for j, (a2, d2) in enumerate(L):
            A[i, j] = ham(d, a2) <= R - 1
    return L, A

def find_cycle(nodes, A):
    """return a directed cycle in the subgraph induced on nodes (list), or None (DFS)."""
    nodes = list(nodes); S = set(nodes)
    color = {v: 0 for v in nodes}; parent = {}
    adj = {v: [w for w in nodes if A[v, w] and w != v] for v in nodes}
    for s in nodes:
        if color[s]:
            continue
        stack = [(s, iter(adj[s]))]; color[s] = 1
        while stack:
            v, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[v] = 2; stack.pop(); continue
            if color[nxt] == 0:
                color[nxt] = 1; parent[nxt] = v; stack.append((nxt, iter(adj[nxt])))
            elif color[nxt] == 1:
                cyc = [nxt]; x = v
                while x != nxt:
                    cyc.append(x); x = parent[x]
                return cyc
    return None

def max_triangular(A, maxit=4000):
    D = A.shape[0]
    loop = np.diag(A)
    cons_rows = []
    # forbid 2-cycles up front
    for i in range(D):
        for j in range(i + 1, D):
            if A[i, j] and A[j, i]:
                r = np.zeros(D); r[i] = r[j] = 1; cons_rows.append((r, 1))
    for it in range(maxit):
        c = -np.ones(D)
        ub = np.where(loop, 0, 1)
        if cons_rows:
            M = np.array([r for r, _ in cons_rows]); b = np.array([bb for _, bb in cons_rows])
            lc = [LinearConstraint(M, -np.inf, b)]
        else:
            lc = []
        res = milp(c, constraints=lc, integrality=np.ones(D), bounds=Bounds(np.zeros(D), ub))
        x = np.round(res.x).astype(int)
        U = [i for i in range(D) if x[i]]
        cyc = find_cycle(U, A)
        if cyc is None:
            return len(U), U
        r = np.zeros(D); r[cyc] = 1; cons_rows.append((r, len(cyc) - 1))
    raise RuntimeError("no convergence")

def als_rank(A, k, trials=6, iters=600, seed=0):
    """try to find rank-k G with G[forced] = I[forced]; forced = ~A."""
    rng = np.random.default_rng(seed)
    D = A.shape[0]; forced = ~A; I = np.eye(D)
    best = np.inf
    for t in range(trials):
        X = rng.standard_normal((D, k)); Y = rng.standard_normal((D, k))
        for _ in range(iters):
            for i in range(D):
                cols = np.where(forced[i])[0]
                X[i] = np.linalg.lstsq(Y[cols], I[i, cols], rcond=None)[0]
            for j in range(D):
                rows = np.where(forced[:, j])[0]
                Y[j] = np.linalg.lstsq(X[rows], I[rows, j], rcond=None)[0]
            G = X @ Y.T
            res = np.max(np.abs((G - I)[forced]))
            if res < 1e-11:
                break
        best = min(best, res)
        if best < 1e-10:
            return True, best
    return False, best

def main(Qs=(2, 3)):
    # commutative optimum (p=1/4) from exhaustive search, imported lazily
    sys.path.insert(0, __import__('os').path.dirname(__file__))
    from parity_template_bounds import general_opt
    from fractions import Fraction as Fr
    for Q in Qs:
        D = 4**Q
        gen = general_opt(Q, Fr(1, 4), Q)
        for R in range(1, Q + 1):
            L, A = allowed(Q, R)
            pot = sum(1 for (a, d) in L if bin(d).count('1') - bin(a).count('1') >= R)
            tri, U = max_triangular(A)
            comm = int(gen[R][0] * D)
            # non-commutative search for rank < comm
            found = None
            for k in range(tri, comm):
                ok, res = als_rank(A, k)
                if ok:
                    found = k; break
            print(f"Q={Q} R={R} D={D}: potential LB={pot}  exact max-triangular LB={tri}  "
                  f"commutative opt={comm}  ALS rank<comm found: {found}")
            sys.stdout.flush()

if __name__ == "__main__":
    main(tuple(int(x) for x in sys.argv[1:]) or (2, 3))
