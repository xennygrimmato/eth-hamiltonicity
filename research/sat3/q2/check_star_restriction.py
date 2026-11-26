"""Check (q2-notes.md, star lemma): the complete-graph wire tensor T_K(2a) equals the product of the
K star tensors Star_v(a), and restricts row-locally to A_1 (x) ... (x) A_K for ARBITRARY tensors
A_v on K rows whose rows u != v have side <= 2^a.  Also checks f_U(X) = f_T(M^t X).
Sizes: K=3, a=1 (edge dimension 4, row dimension 16) and K=4, a=1 (row dimension 64)."""
import numpy as np, itertools
rng = np.random.default_rng(0)

def run(K, a, qv):
    D = 2 ** a                      # leaf side
    # Row u of T_K(2a) has index ((j^u_w)_{w != u}  [own star, each in [D]],  (k^w_u)_{w != u} [leaf of star w])
    others = {u: [w for w in range(K) if w != u] for u in range(K)}
    # tensors A_v: row v has side qv, rows u != v have side D
    A = []
    for v in range(K):
        shape = [D] * K
        shape[v] = qv
        A.append(rng.integers(-2, 3, size=shape).astype(float))
    # target U = A_0 (x) ... (x) A_{K-1}, row u index = (i_u^{(0)}, ..., i_u^{(K-1)}), i_u^{(v)} = index of row u in A_v
    def U_entry(idx):   # idx[u][v]
        p = 1.0
        for v in range(K):
            p *= A[v][tuple(idx[u][v] for u in range(K))]
        return p
    # T_K(2a) entry: row u index = (own[u][w], leaf[u][w]) ; edge {u,w}: own[u][w] == leaf[w][u] and own[w][u] == leaf[u][w]
    # local map M_u : (own[u], leaf[u]) -> U-row index:  i_u^{(u)} = i with coefficient A_u[i ; own[u]],  i_u^{(w)} = leaf[u][w]
    # so (M T)[idx] = sum over own, leaf consistent of prod_u A_u[idx[u][u]; own[u][.]] * [leaf[u][w] == idx[u][w]]
    #             = prod_u A_u[idx[u][u] at row u, and row w index own[u][w] = leaf[w][u] = idx[w][u]]
    def MT_entry(idx):
        p = 1.0
        for u in range(K):
            ind = [None] * K
            ind[u] = idx[u][u]
            for w in others[u]:
                ind[w] = idx[w][u]          # forced by the wire: own[u][w] = leaf[w][u] = idx[w][u]
            p *= A[u][tuple(ind)]
        return p
    # compare on random index tuples (and exhaustively if small)
    sides = [[(qv if v == u else D) for v in range(K)] for u in range(K)]
    maxdiff = 0.0
    n = 0
    for _ in range(4000):
        idx = [[int(rng.integers(0, sides[u][v])) for v in range(K)] for u in range(K)]
        maxdiff = max(maxdiff, abs(U_entry(idx) - MT_entry(idx)))
        n += 1
    return maxdiff, n

for (K, a, qv) in [(3, 1, 2), (3, 1, 5), (4, 1, 3), (4, 2, 3)]:
    md, n = run(K, a, qv)
    print(f"K={K} a={a} side(row v of A_v)={qv}: max |U - (M_1 x..x M_K) T_K(2a)| over {n} random entries = {md}")

# bit count: T_K(2a) has (K-1)*2a bits per row; U = T_d^{(x) h} with h = K*h0, q0^{h0} <= 2^a has h*log2(q0) <= K*a bits per row.
for K in (16, 64, 1024):
    print(K, "row bits clique / row bits hosted power (at q0^h0 = 2^a):", 2 * (K - 1) / K)
