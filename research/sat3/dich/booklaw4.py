"""The law  L(S) = min over spine intervals K = [lo, hi] of V1(hull(S u K))  on the book T_k x R (M = 1):
V1(C) = sum_i W(C_i) - (k-1) W(C cap spine).  The objective is convex in (lo, hi) on lo <= J_lo, hi >= J_hi.
Checks on random V0: monotone, submodular on intersecting sets (elemental), flat law, hull invariance,
and L <= LP maximum (label_lp.solve) on a sample; L(tips) against 2 sqrt 2."""
import itertools, math, random, sys
import numpy as np
from scipy.optimize import minimize
from label_lp import Pt, hull_data, flat_width, in_hull, mean_width_planar, solve
def V1_with_K(S, k, lo, hi):
    return __import__("booklaw2").V1(S + [Pt(None, 0, lo), Pt(None, 0, hi)], k)
def L(S, k):
    J, per = hull_data(S, k)
    if J is None:                      # S inside one page (or empty spine part): flat, L = W
        return flat_width(S)
    def obj(p):
        lo = J[0] - p[0] ** 2; hi = J[1] + p[1] ** 2
        return V1_with_K(S, k, lo, hi)
    best = min((minimize(obj, x0, method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-13, "maxiter": 2000})
                for x0 in ([0.0, 0.0], [0.5, 0.5], [0.05, 0.6], [0.6, 0.05])), key=lambda r: r.fun)
    return min(best.fun, obj([0.0, 0.0]))
if __name__ == "__main__":
    a = 1.0
    tips = [Pt(i, a, 0.0) for i in range(3)]
    print("L(3 tips) =", L(tips, 3), "  2 sqrt 2 =", 2 * math.sqrt(2))
    print("L(4 tips) =", L([Pt(i, a, 0.0) for i in range(4)], 4), "  2 sqrt 3 =", 2 * math.sqrt(3))
    bad = [(3, 1.377, 0.116), (0, 1.09, 0.908), (3, 1.475, -0.146), (0, 1.106, 0.234), (1, 0.974, -0.12), (2, 0.696, -0.494), (2, 0.169, -0.159)]
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 33)
    worst = {"mono": (0, None), "submod": (-1, None), "flat": (0, None), "hull": (0, None), "L-U": (-9, None)}
    configs = [(4, [Pt(*p) for p in bad])]
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 30):
        k = random.choice([3, 3, 4, 5]); n = random.choice([6, 7, 7])
        V0 = []
        for j in range(n):
            if random.random() < 0.2: V0.append(Pt(None, 0, random.uniform(-1.2, 1.2)))
            else: V0.append(Pt(random.randrange(k), random.uniform(0.05, 1.5), random.uniform(-1.2, 1.2)))
        configs.append((k, V0))
    for ci, (k, V0) in enumerate(configs):
        n = len(V0); full = (1 << n) - 1
        Lv = {m: L([V0[i] for i in range(n) if m >> i & 1], k) for m in range(1, full + 1)}
        for m in range(1, full + 1):
            S = [V0[i] for i in range(n) if m >> i & 1]
            w = flat_width(S)
            if w is not None and abs(Lv[m] - w) > worst["flat"][0]: worst["flat"] = (abs(Lv[m] - w), ci)
            out = [i for i in range(n) if not m >> i & 1]
            for x in out:
                d = Lv[m] - Lv[m | 1 << x]
                if d > worst["mono"][0]: worst["mono"] = (d, ci)
                if len(S) >= 2 and in_hull(V0[x], S, k) and abs(d) > worst["hull"][0]: worst["hull"] = (abs(d), ci)
            for x, y in itertools.combinations(out, 2):
                d = Lv[m | 1 << x | 1 << y] + Lv[m] - Lv[m | 1 << x] - Lv[m | 1 << y]
                if d > worst["submod"][0]: worst["submod"] = (d, (ci, m, x, y))
        if k == 3 and ci % 5 == 1:
            for m in random.sample([m for m in range(1, full + 1) if bin(m).count("1") >= 3], 6):
                r = solve(V0, k, m, verbose=False)
                if r.status == 0 and Lv[m] + r.fun > worst["L-U"][0]: worst["L-U"] = (Lv[m] + r.fun, ci)
        print(f"config {ci} (k={k}, n={n}) done; worst so far: " + ", ".join(f"{a}={b[0]:.2e}" for a, b in worst.items()), flush=True)
