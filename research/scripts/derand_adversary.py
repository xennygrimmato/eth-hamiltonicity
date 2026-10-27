"""E2: adversarial search for cubic graphs with large t_Q (Hamiltonian, but every
restriction of size < t_Q has #HC = 0 mod q for all q in Q).

Simulated annealing over connected cubic graphs on n vertices with double edge swaps.
Objective: t_Q (primary), then -#HC (prefer fewer cycles, i.e. tighter vs Theorem 1).
Usage: python3 derand_adversary.py n mods(comma) iters seed
"""
import math
import random
import sys

import networkx as nx

from derand_core import (DIAMOND, ham_cycles_fast, necklace, normalize,
                         random_regular, t_value)


def score(n, edges, mods, smax):
    hcs = ham_cycles_fast(n, edges)
    if not hcs:
        return (-1, 0), hcs
    t, q, T = t_value(hcs, mods, smax)
    if t is None:
        t = smax + 1
    return (t, -len(hcs)), hcs


def anneal(n, mods, iters, rng, smax=12):
    n, edges = random_regular(n, 3, rng)
    cur, hcs = score(n, edges, mods, smax)
    best = (cur, edges, len(hcs))
    temp = 1.0
    for it in range(iters):
        G = nx.Graph(edges)
        try:
            nx.double_edge_swap(G, nswap=rng.choice([1, 1, 2]), max_tries=200,
                                seed=rng.randrange(1 << 30))
        except nx.NetworkXException:
            continue
        if not nx.is_connected(G):
            continue
        ne = normalize(G.edges())
        sc, h2 = score(n, ne, mods, smax)
        d = (sc[0] - cur[0]) + 0.01 * (sc[1] - cur[1])
        if d >= 0 or rng.random() < math.exp(d / temp):
            edges, cur = ne, sc
            if sc > best[0]:
                best = (sc, ne, len(h2))
        temp = max(0.05, temp * 0.999)
    return best


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    mods = [int(x) for x in (sys.argv[2] if len(sys.argv) > 2 else "2").split(",")]
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 500
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 7)
    best = anneal(n, mods, iters, rng)
    (t, negH), edges, H = best
    print(f"n={n} mods={mods} best t_Q={t} #HC={H} log2#HC={math.log2(max(H,1)):.2f}")
    print("edges", edges)
    if n % 4 == 0:
        nn, ne = necklace([DIAMOND] * (n // 4))
        hc = ham_cycles_fast(nn, ne)
        print("diamond necklace: t_Q =", t_value(hc, mods)[0], "#HC =", len(hc))


if __name__ == "__main__":
    main()
