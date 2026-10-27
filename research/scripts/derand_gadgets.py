"""E3: 2-terminal gadgets for necklace adversaries.

A gadget is a graph on k vertices with terminals a, d of internal degree 2 and all other
vertices of degree 3 (so a necklace of gadgets is cubic).  Its routes are the Hamiltonian
a-d paths.  In a necklace, #HC = prod r_i and t_q(necklace) = sum_i tau_q(gadget_i), where
tau_q is t_q of the gadget's route family.  We search random gadgets for each k and record,
for each modulus set, the best value tau_Q / k (restriction cost per vertex).
Usage: python3 derand_gadgets.py kmax samples seed
"""
import random
import sys
from collections import defaultdict

import networkx as nx

from derand_core import ham_cycles_fast, necklace, normalize, t_per_modulus, t_value


def random_gadget(k, rng):
    # degree sequence: terminals 0 and k-1 have degree 2, others 3
    deg = [2] + [3] * (k - 2) + [2]
    for _ in range(200):
        try:
            G = nx.random_degree_sequence_graph(deg, seed=rng.randrange(1 << 30), tries=20)
        except nx.NetworkXError:
            continue
        if nx.is_connected(G):
            return k, normalize(G.edges()), 0, k - 1
    return None


def routes(gad):
    k, edges, a, d = gad
    z = k
    ext = normalize(edges + [(a, z), (d, z)])
    hcs = ham_cycles_fast(k + 1, ext)
    # map masks back to gadget edge indices
    idx = {e: i for i, e in enumerate(edges)}
    out = []
    for h in hcs:
        m = 0
        for i, e in enumerate(ext):
            if (h >> i) & 1 and e in idx:
                m |= 1 << idx[e]
        out.append(m)
    return out


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    modsets = {"2": [2], "3": [3], "5": [5], "2,3": [2, 3], "2,3,5": [2, 3, 5]}
    best = {name: (0, None) for name in modsets}  # (tau/k, gadget)
    smallest_r_mult = {}
    for k in range(4, kmax + 1, 2):
        rc = defaultdict(int)
        for _ in range(S):
            g = random_gadget(k, rng)
            if g is None:
                continue
            R = routes(g)
            r = len(R)
            rc[r] += 1
            if r == 0:
                continue
            for name, mods in modsets.items():
                t, _, _ = t_value(R, mods)
                if t and t / k > best[name][0]:
                    best[name] = (t / k, (g, r, t))
                for p in mods:
                    if r % p == 0 and (p not in smallest_r_mult or k < smallest_r_mult[p][0]):
                        smallest_r_mult[p] = (k, r)
        print(f"k={k}: route-count histogram {dict(sorted(rc.items()))}")
    for name, (val, info) in best.items():
        if info:
            g, r, t = info
            print(f"mods {name}: best tau/k = {val:.3f} (k={g[0]}, r={r}, tau={t}) edges={g[1]}")
    print("smallest k with r = 0 mod p:", smallest_r_mult)


if __name__ == "__main__":
    main()
