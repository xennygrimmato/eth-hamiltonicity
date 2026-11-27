"""Tests for the valuation form of the candidate law on the book T_k x R (M = 1).
(1) F(hull X) = sum_i W(C_i) - (k-1) W(C cap spine)  (inclusion-exclusion; C_i = page parts of the hull).
(2) f(X) = F(hull X) is submodular on finite sets:  f(S+x) + f(S+y) >= f(S+x+y) + f(S)  for S nonempty.
    (Then G(S) = min_{S' >= S} f(S') is monotone and submodular, cf. booklaw.py.)"""
import itertools, math, random, sys
import numpy as np
from label_lp import Pt, hull_data, mean_width_planar
from booklaw import F_of_points
def V1(S, k):
    J, per = hull_data(S, k)
    sp = [(0.0, J[0]), (0.0, J[1])] if J else []
    tot = 0.0
    for i in range(k):
        pts = per[i] + sp
        if pts: tot += mean_width_planar(pts)
    return tot - (k - 1) * ((J[1] - J[0]) if J else 0.0)
if __name__ == '__main__':
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 8)
    wv = 0.0; ws = -1.0; cnt = 0; tight = 0
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 60):
        k = random.choice([3, 3, 4, 5]); n = random.choice([5, 6, 7, 8])
        V0 = []
        for j in range(n):
            if random.random() < 0.25: V0.append(Pt(None, 0, random.uniform(-1.2, 1.2)))
            else: V0.append(Pt(random.randrange(k), random.uniform(0.05, 1.5), random.uniform(-1.2, 1.2)))
        full = (1 << n) - 1
        f = {m: V1([V0[i] for i in range(n) if m >> i & 1], k) for m in range(1, full + 1)}
        for m in random.sample(range(1, full + 1), 12):
            wv = max(wv, abs(f[m] - F_of_points([V0[i] for i in range(n) if m >> i & 1], k)))
        for m in range(1, full + 1):
            out = [i for i in range(n) if not m >> i & 1]
            for x, y in itertools.combinations(out, 2):
                d = f[m | 1 << x | 1 << y] + f[m] - f[m | 1 << x] - f[m | 1 << y]
                ws = max(ws, d); cnt += 1; tight += abs(d) < 1e-12
    print(f"max |V1 - F| = {wv:.2e};  elemental submodularity of f = V1(hull): max violation = {ws:.2e} over {cnt} inequalities ({tight} tight)")
