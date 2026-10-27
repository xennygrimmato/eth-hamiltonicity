"""Checks behind the 'connectivity = hooks = exterior powers = fermions' remark.

(a) 1_{n-cycle}(s) = (1/n) sum_k (-1)^k chi_{(n-k,1^k)}(s), with chi_{(n-k,1^k)} = chi_{Lambda^k std}
    read off from det(I + t P_s) / (1 + t)  (Lambda^k of the defining rep = Lambda^k std + Lambda^{k-1} std).
(b) equivalently: #cycles(s) = dim ker(I - P_s); and for a 2-factor F on n vertices, the number of
    spanning trees tau(F) = n * [F connected]  (cofactor of the Laplacian).
(c) dims of the hook irreps: sum_k binom(n-1,k)^2 = binom(2n-2,n-1)  (the Raz-Spieker rank).
"""
import itertools, math
import numpy as np
import networkx as nx

def ctype(p):
    n = len(p); seen = [0] * n; c = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = 1; j = p[j]; l += 1
            c.append(l)
    return c

for n in range(2, 8):
    ok = True
    for p in itertools.permutations(range(n)):
        c = ctype(p)
        # det(I + tP) = prod_cycles (1 - (-t)^len)
        poly = np.array([1], dtype=object)
        for l in c:
            f = np.zeros(l + 1, dtype=object); f[0] = 1; f[l] = -((-1) ** l)
            poly = np.convolve(poly, f)
        # divide by (1+t)
        q = []; rem = list(poly)
        for k in range(len(rem) - 1):
            q.append(rem[k]); rem[k + 1] -= rem[k]
        assert rem[-1] == 0
        val = sum((-1) ** k * q[k] for k in range(len(q)))
        if val != (n if len(c) == 1 else 0):
            ok = False
    print(f"n={n}: (a) hook-character formula for the n-cycle indicator: {ok};  "
          f"(c) sum_k C(n-1,k)^2 = {sum(math.comb(n-1,k)**2 for k in range(n))} = C(2n-2,n-1) = {math.comb(2*n-2,n-1)}")

# (b) tau(F) = n [F connected] for 2-factors
for n in range(6, 13):
    good = True
    for parts in [[n], [3, n - 3], [4, n - 4], [3, 3, n - 6] if n >= 9 else [n]]:
        G = nx.disjoint_union_all([nx.cycle_graph(k) for k in parts])
        L = nx.laplacian_matrix(G).toarray().astype(float)
        tau = round(np.linalg.det(L[1:, 1:]))
        good &= (tau == (n if len(parts) == 1 else 0))
    print(f"n={n}: (b) tau(2-factor) = n*[connected]: {good}")
