"""A candidate maximal label law on the open book T_k x R (M = 1) and tests of it.

For a compact set C in the book and a direction (cos th, sin th), th in [-pi/2, pi/2]:
   h_i(th) = max over points (r, y) of C in page i (spine points belong to every page) of  r cos th + y sin th,
   m(th)   = max over all points of C of  -r cos th + y sin th.
   F(C) = integral over th of  m + (1/2) sum_i (h_i - m)_+          (= mean width if C lies in a flat).
Candidate law:  L(Z) = inf { F(C) : C convex, C contains Z }.
Tests on a finite point set V0:  G(S) = min over S <= S' <= V0 of F(hull S')  is compared with the LP maximum U(S)
of delta(S) (label_lp.py), and G is checked against all LP constraints.
"""
import itertools, math, random, sys
import numpy as np
from label_lp import Pt, hull_data, flat_width, in_hull, solve, mask_of

TH = np.linspace(-math.pi / 2, math.pi / 2, 20001)
CT, ST = np.cos(TH), np.sin(TH)
def integ(f): return float(np.sum((f[1:] + f[:-1]) * 0.5) * (TH[1] - TH[0]))

def F_of_points(S, k):
    """F(hull S) for a finite set S of Pt"""
    J, per = hull_data(S, k)
    sp = [(0.0, J[0]), (0.0, J[1])] if J else []
    m = np.full_like(TH, -np.inf); hs = []
    for i in range(k):
        pts = per[i] + sp
        if not pts: hs.append(None); continue
        h = np.full_like(TH, -np.inf)
        for r, y in pts:
            h = np.maximum(h, r * CT + y * ST); m = np.maximum(m, -r * CT + y * ST)
        hs.append(h)
    f = m.copy()
    for h in hs:
        if h is not None: f += 0.5 * np.maximum(h - m, 0.0)
    return integ(f)

def test(V0, k=3, verbose=True, nU=40, seed=0):
    n = len(V0); full = (1 << n) - 1
    Fh = {m: F_of_points([V0[i] for i in range(n) if m >> i & 1], k) for m in range(1, full + 1)}
    G = {}
    for m in range(1, full + 1):
        rest = full & ~m; best = Fh[m]; s = rest
        while s:
            best = min(best, Fh[m | s]); s = (s - 1) & rest
        G[m] = best
    # check the constraints for G
    worst = {"single": 0.0, "mono": 0.0, "submod": 0.0, "flat": 0.0, "hull": 0.0}
    for m in range(1, full + 1):
        S = [V0[i] for i in range(n) if m >> i & 1]
        if len(S) == 1: worst["single"] = max(worst["single"], abs(G[m]))
        w = flat_width(S)
        if w is not None: worst["flat"] = max(worst["flat"], abs(G[m] - w))
        out = [i for i in range(n) if not m >> i & 1]
        for x in out:
            mx = m | 1 << x
            worst["mono"] = max(worst["mono"], G[m] - G[mx])
            if len(S) >= 2 and in_hull(V0[x], S, k): worst["hull"] = max(worst["hull"], abs(G[mx] - G[m]))
        for x, y in itertools.combinations(out, 2):
            mx, my = m | 1 << x, m | 1 << y
            worst["submod"] = max(worst["submod"], G[mx | my] + G[m] - G[mx] - G[my])
    # compare with LP maxima on a sample of subsets
    rng = random.Random(seed); ms = [m for m in range(1, full + 1) if bin(m).count("1") >= 3]
    rng.shuffle(ms); gap = 0.0; gapneg = 0.0
    for m in ms[:nU]:
        r = solve(V0, k, m, verbose=False)
        if r.status != 0: print("LP failed"); continue
        gap = max(gap, -r.fun - G[m]); gapneg = max(gapneg, G[m] + r.fun)
    if verbose:
        print(f"  n={n}: violations of G: " + ", ".join(f"{a}={b:.2e}" for a, b in worst.items()) +
              f";  max(U - G) = {gap:.2e}, max(G - U) = {gapneg:.2e}")
    return worst, gap, gapneg, G

if __name__ == "__main__":
    a = 1.0; H = 1 / (2 * math.sqrt(2))
    V0 = [Pt(i, a, 0.0, f"p{i}") for i in range(3)] + [Pt(None, 0, H, "Q+"), Pt(None, 0, -H, "Q-")]
    print("F(hull(tips + Q+-)) =", F_of_points(V0, 3), " chain 2 sqrt2 =", 2 * math.sqrt(2))
    print("F(hull(tips)) =", F_of_points(V0[:3], 3), "(= 3a: the hub cost)")
    w, gap, gn, G = test(V0)
    print("  G(tips) =", G[0b111])
    random.seed(4)
    tot = {"submod": 0.0, "mono": 0.0, "flat": 0.0, "hull": 0.0, "gap": 0.0, "gapneg": 0.0}
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 12):
        n = random.choice([6, 7, 8])
        V0 = []
        for j in range(n):
            if random.random() < 0.3: V0.append(Pt(None, 0, random.uniform(-1.2, 1.2), f"r{j}"))
            else: V0.append(Pt(j % 3, random.uniform(0.1, 1.5), random.uniform(-1.2, 1.2), f"r{j}"))
        w, gap, gn, G = test(V0, nU=25, seed=trial)
        for key in ("submod", "mono", "flat", "hull"): tot[key] = max(tot[key], w[key])
        tot["gap"] = max(tot["gap"], gap); tot["gapneg"] = max(tot["gapneg"], gn)
    print("worst over all trials:", {a: f"{b:.2e}" for a, b in tot.items()})
