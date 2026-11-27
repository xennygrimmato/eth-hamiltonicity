"""Is G(S) = min over S <= S' <= V0 of V1(hull S') a label law on V0 (book T_k x R)?  Many random V0, k = 3,4,5.
Reports the worst violation of monotone / submodular-on-intersecting / flat / hull-invariance, and an example."""
import itertools, math, random, sys
from label_lp import Pt, flat_width, in_hull
from booklaw2 import V1
def envelope(f, n):
    """G(m) = min over supersets, by the standard zeta-type sweep"""
    G = dict(f)
    for i in range(n):
        for m in range((1 << n) - 1, 0, -1):
            if not m >> i & 1: G[m] = min(G[m], G[m | 1 << i])
    return G
if __name__ == "__main__":
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 21)
    worst = {"submod": (-1, None), "flat": (0, None), "hull": (0, None)}
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 100):
        k = random.choice([3, 3, 4, 5]); n = random.choice([6, 7, 8, 9])
        V0 = []
        for j in range(n):
            u = random.random()
            if u < 0.25: V0.append(Pt(None, 0, random.uniform(-1.2, 1.2)))
            else: V0.append(Pt(random.randrange(k), random.uniform(0.05, 1.5), random.uniform(-1.2, 1.2)))
        full = (1 << n) - 1
        f = {m: V1([V0[i] for i in range(n) if m >> i & 1], k) for m in range(1, full + 1)}
        G = envelope(f, n)
        desc = (k, [(p.ray, round(p.r, 3), round(p.y, 3)) for p in V0])
        for m in range(1, full + 1):
            S = [V0[i] for i in range(n) if m >> i & 1]
            w = flat_width(S)
            if w is not None and abs(G[m] - w) > worst["flat"][0]: worst["flat"] = (abs(G[m] - w), (desc, m))
            out = [i for i in range(n) if not m >> i & 1]
            for x in out:
                if len(S) >= 2 and in_hull(V0[x], S, k) and abs(G[m | 1 << x] - G[m]) > worst["hull"][0]:
                    worst["hull"] = (abs(G[m | 1 << x] - G[m]), (desc, m, x))
            for x, y in itertools.combinations(out, 2):
                d = G[m | 1 << x | 1 << y] + G[m] - G[m | 1 << x] - G[m | 1 << y]
                if d > worst["submod"][0]: worst["submod"] = (d, (desc, m, x, y))
    for key, (v, ex) in worst.items(): print(f"{key}: worst violation {v:.3e}" + (f"   at {ex}" if v > 1e-9 else ""))
