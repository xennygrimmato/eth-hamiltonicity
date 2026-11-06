"""code_check.py -- exact check of Q* and the 'all rows full' transfer bound on random linear codes L <= GF(2)^18 (two
coordinates per node of Delta_3): for the code tensor [x in L], log2 rank across S | S^c = dim pi_S(L) + dim pi_{S^c}(L) - dim L
(mutual information of the uniform distribution on L).  Tests: 2 h(R_0) <= sum_c h(col_c) + sum_d h(diag_d);
and h(R_r) = 6 for all r  ==>  sum_c h(col) + sum_d h(diag) >= 18 (i.e. c_c + c_d >= 9).  Also graph tensors of all
9-edge 2-regular multigraphs on the 9 nodes (as codes).  [N]"""
import numpy as np, itertools, sys
rng = np.random.default_rng(0)
nodes = [(r, c) for r in range(3) for c in range(3)]
coord = {v: (2 * i, 2 * i + 1) for i, v in enumerate(nodes)}
def cols_of(S): return [k for v in S for k in coord[v]]
rows = [[(r, c) for c in range(3)] for r in range(3)]
cols = [[(r, c) for r in range(3)] for c in range(3)]
diags = [[(r, c) for r in range(3) for c in range(3) if (r - c) % 3 == d] for d in range(3)]
def rank2(M):
    M = M.copy() % 2; r = 0; rows_, cols_ = M.shape
    for c in range(cols_):
        piv = [i for i in range(r, rows_) if M[i, c]]
        if not piv: continue
        M[[r, piv[0]]] = M[[piv[0], r]]
        for i in range(rows_):
            if i != r and M[i, c]: M[i] ^= M[r]
        r += 1
        if r == rows_: break
    return r
def h(G, S):   # G: generator matrix (dim x 18)
    Sc = [v for v in nodes if v not in S]
    return rank2(G[:, cols_of(S)]) + rank2(G[:, cols_of(Sc)]) - rank2(G)
worst = +np.inf; worst_full = +np.inf; nfull = 0
for t in range(20000):
    k = rng.integers(1, 18)
    G = rng.integers(0, 2, size=(k, 18))
    if rank2(G) == 0: continue
    hR = [h(G, R) for R in rows]; sa = sum(h(G, C) for C in cols) + sum(h(G, D) for D in diags)
    worst = min(worst, sa - 2 * hR[0])
    if all(x == 6 for x in hR):
        nfull += 1; worst_full = min(worst_full, sa)
print(f'random GF(2) codes (20000): min [sum_c h(col) + sum_d h(diag) - 2 h(R_0)] = {worst}  (Q* holds iff >= 0)')
print(f'  codes with all three row cuts full: {nfull}; min sum_c h(col) + sum_d h(diag) among them = {worst_full}  (>= 18 <=> c_c + c_d >= 9)')
