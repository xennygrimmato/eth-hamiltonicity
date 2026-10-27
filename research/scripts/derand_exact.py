"""E5: what EXACT integer counts F_R(q) = sum_{2-factors X of restriction R} q^{cc(X)-1},
q = 1..Q, add over residues.

Certificate that restriction R (force F, delete D) contains a Hamiltonian cycle:
  (res) F_R(q) mod q != 0 for some 2 <= q <= Q   (F_R(q) = a_1 mod q), or
  (cone) the vector (F_R(1..Q)) is NOT in the cone spanned by (q^{k-1})_{q<=Q}, k >= 2,
         i.e. no a_2..a_K >= 0 explain the data with a_1 = 0 (LP infeasibility).
t_res(G), t_ex(G) = least |F|+|D| of a certified restriction.
Usage: python3 derand_exact.py Q
"""
import itertools
import math
import random
import sys
from collections import Counter

import networkx as nx
import numpy as np
from scipy.optimize import linprog

from derand_core import DIAMOND, necklace, random_regular, normalize


def two_factors(n, edges):
    """List of (mask, #components) for all 2-factors."""
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)
    out = []
    deg = [0] * n
    decided = [None] * len(edges)  # True/False

    def comps(mask):
        G = nx.Graph([edges[i] for i in range(len(edges)) if (mask >> i) & 1])
        return nx.number_connected_components(G)

    def rec(mask):
        # find vertex with deg < 2
        v = next((x for x in range(n) if deg[x] < 2), None)
        if v is None:
            out.append((mask, comps(mask)))
            return
        need = 2 - deg[v]
        free = [i for i in inc[v] if decided[i] is None]
        if len(free) < need:
            return
        for choice in itertools.combinations(free, need):
            ok = True
            chosen = []
            for i in choice:
                u, w = edges[i]
                o = w if u == v else u
                if deg[o] >= 2:
                    ok = False
                    break
            if not ok:
                continue
            rejected = [i for i in free if i not in choice]
            for i in choice:
                decided[i] = True
                u, w = edges[i]
                deg[u] += 1
                deg[w] += 1
            for i in rejected:
                decided[i] = False
            # prune: neighbours that are now dead
            dead = False
            for i in choice + tuple(rejected):
                for x in edges[i]:
                    if deg[x] < 2 and sum(1 for j in inc[x] if decided[j] is None) < 2 - deg[x]:
                        dead = True
            if not dead:
                rec(mask | sum(1 << i for i in choice))
            for i in choice:
                decided[i] = None
                u, w = edges[i]
                deg[u] -= 1
                deg[w] -= 1
            for i in rejected:
                decided[i] = None

    rec(0)
    return out


def in_cone(Fvals, Q, K):
    """Is there b_k >= 0 (k=2..K) with sum_k b_k q^{k-1} = F(q), q=1..Q ?"""
    if all(f == 0 for f in Fvals):
        return True
    A = np.array([[float(q) ** (k - 1) for k in range(2, K + 1)] for q in range(1, Q + 1)])
    b = np.array(Fvals, dtype=float)
    s = A.max(axis=1)
    res = linprog(np.zeros(A.shape[1]), A_eq=A / s[:, None], b_eq=b / s,
                  bounds=[(0, None)] * A.shape[1], method="highs")
    return res.status == 0


def certified(tf, Fm, Dm, Q, K, use_cone):
    hist = Counter(c for m, c in tf if (m & Fm) == Fm and not (m & Dm))
    Fv = [sum(a * q ** (k - 1) for k, a in hist.items()) for q in range(1, Q + 1)]
    if any(Fv[q - 1] % q for q in range(2, Q + 1)):
        return "res"
    if use_cone and Fv[0] > 0 and not in_cone(Fv, Q, K):
        return "cone"
    return None


def t_cert(n, edges, Q, use_cone, smax=3):
    tf = two_factors(n, edges)
    K = n // 3
    N = len(edges)
    for s in range(0, smax + 1):
        for S in itertools.combinations(range(N), s):
            for signs in itertools.product((0, 1), repeat=s):
                Fm = sum(1 << S[j] for j in range(s) if signs[j])
                Dm = sum(1 << S[j] for j in range(s) if not signs[j])
                why = certified(tf, Fm, Dm, Q, K, use_cone)
                if why:
                    return s, why
    return None, None


def main():
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rng = random.Random(9)
    for m in (3, 4, 5):
        n, e = necklace([DIAMOND] * m)
        print(f"diamond necklace n={n}: t_res={t_cert(n, e, Q, False, 6)}  t_ex={t_cert(n, e, Q, True, 6)}")
    for n in (12, 16, 20):
        hist_res, hist_ex = Counter(), Counter()
        for _ in range(15):
            nn, e = random_regular(n, 3, rng)
            tf = two_factors(nn, e)
            if not any(c == 1 for _, c in tf):
                continue
            hist_res[t_cert(nn, e, Q, False)[0]] += 1
            r = t_cert(nn, e, Q, True)
            hist_ex[(r[0], r[1])] += 1
        print(f"random cubic n={n} Q={Q}: t_res hist {dict(hist_res)}  t_ex hist {dict(hist_ex)}")


if __name__ == "__main__":
    main()
