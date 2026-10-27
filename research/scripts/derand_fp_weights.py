"""E4: the randomized F_p-weight test and its Alon-Furedi guarantee.

P_G(w) = sum_{H in HC(G)} prod_{e in H} w_e  (mod p).  For uniform w in F_p^E,
Pr[P_G(w) != 0] >= p^{-n/(p-1)} (Alon-Furedi, P multilinear of degree n, 0/1 coeffs).
We measure the empirical rate on random cubic graphs and on necklace adversaries.
Usage: python3 derand_fp_weights.py
"""
import random

import numpy as np

from derand_core import (DIAMOND, bits, ham_cycles_fast, necklace, random_regular)

G6 = (10, [(0, 5), (0, 6), (1, 3), (1, 5), (1, 7), (2, 3), (2, 8), (2, 9), (3, 4), (4, 5),
           (4, 6), (6, 8), (7, 8), (7, 9)], 0, 9)  # 2-terminal gadget with 6 routes


def rate(n, edges, p, trials, rng, weights=None):
    hcs = ham_cycles_fast(n, edges)
    if not hcs:
        return None, 0
    M = np.array([bits(h) for h in hcs])
    hits = 0
    for _ in range(trials):
        w = np.array([rng.randrange(p) if weights is None else rng.choice(weights)
                      for _ in edges], dtype=np.int64)
        W = w[M]
        acc = np.ones(len(hcs), dtype=np.int64)
        for j in range(W.shape[1]):
            acc = (acc * W[:, j]) % p
        if acc.sum() % p:
            hits += 1
    return hits / trials, len(hcs)


def main():
    rng = random.Random(3)
    print("graph, p, empirical Pr[P(w)!=0], AF bound p^{-n/(p-1)}, #HC")
    for n in (16, 24):
        for p in (2, 3, 5, 7):
            rs = []
            for _ in range(10):
                nn, e = random_regular(n, 3, rng)
                r, H = rate(nn, e, p, 300, rng)
                if r is not None:
                    rs.append(r)
            print(f"random cubic n={n} p={p}: mean {np.mean(rs):.3f} min {min(rs):.3f}  AF {p ** (-n / (p - 1)):.2e}")
    for name, gad, m in (("diamond necklace", DIAMOND, 5), ("6-route necklace", G6, 2)):
        nn, e = necklace([gad] * m)
        for p in (2, 3, 5, 7):
            r, H = rate(nn, e, p, 2000, rng)
            print(f"{name} n={nn} p={p}: {r:.4f}  AF {p ** (-nn / (p - 1)):.2e}  #HC={H}")


if __name__ == "__main__":
    main()
