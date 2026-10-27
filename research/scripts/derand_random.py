"""E1: residues and t_q on random bounded-degree graphs.

For each sample: #HC, Hamiltonian?, #HC mod small q, t_q for q in MODS, log2 #HC,
Smith check (cubic: every edge in an even number of HCs), Theorem-1 check
(t_p <= log2 #HC).
Usage: python3 derand_random.py [family] [n] [samples] [seed]
family in {cubic, quartic, deg3sparse}
"""
import math
import random
import sys
import time

from derand_core import (bits, ham_cycles_fast, random_maxdeg, random_regular,
                         t_per_modulus)

MODS = [2, 3, 4, 5, 7]


def sample(family, n, rng):
    if family == "cubic":
        return random_regular(n, 3, rng)
    if family == "quartic":
        return random_regular(n, 4, rng)
    if family == "deg3sparse":  # max degree 3, about 1.4 n edges
        return random_maxdeg(n, 3, int(1.4 * n), rng)
    raise ValueError(family)


def main():
    family = sys.argv[1] if len(sys.argv) > 1 else "cubic"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 50
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    stats = dict(ham=0, zero2=0, zero6=0, zeroall=0, smith_viol=0, thm1_viol=0)
    tq_hist = {q: {} for q in MODS + ["all"]}
    ratios = []
    t0 = time.time()
    for _ in range(S):
        n_, edges = sample(family, n, rng)
        hcs = ham_cycles_fast(n_, edges)
        H = len(hcs)
        if H == 0:
            continue
        stats["ham"] += 1
        if H % 2 == 0:
            stats["zero2"] += 1
        if H % 6 == 0:
            stats["zero6"] += 1
        if all(H % q == 0 for q in MODS):
            stats["zeroall"] += 1
        if family == "cubic":
            for i in range(len(edges)):
                if sum(1 for h in hcs if (h >> i) & 1) % 2:
                    stats["smith_viol"] += 1
        tq = t_per_modulus(hcs, MODS)
        tall = min(v for v in tq.values() if v is not None)
        for q in MODS:
            tq_hist[q][tq[q]] = tq_hist[q].get(tq[q], 0) + 1
            if tq[q] is not None and tq[q] > math.log2(H) + 1e-9 and q in (2, 3, 5, 7):
                stats["thm1_viol"] += 1
        tq_hist["all"][tall] = tq_hist["all"].get(tall, 0) + 1
        ratios.append((tq[2], math.log2(H)))
    print(f"family={family} n={n} samples={S} time={time.time()-t0:.1f}s")
    print("stats", stats)
    for q in MODS + ["all"]:
        print(f"  t_{q} histogram", dict(sorted(tq_hist[q].items(), key=lambda kv: (kv[0] is None, kv[0]))))
    if ratios:
        mx = max(r[0] for r in ratios)
        print("  max t_2 =", mx, " mean log2#HC = %.2f" % (sum(r[1] for r in ratios) / len(ratios)))


if __name__ == "__main__":
    main()
