"""For finite Z in T_3 x R compare
   U(Z)  = LP upper bound on the label rate delta(Z) (flat law + submodularity + hull invariance, label_lp.py)
   c(Z)  = min total weight of cuts dominating the metric on Z = max_x sum x_ij d_ij / maxcut(x)   (LP duality)
Every spectral point has  sum x_ij d_ij <= rho(x) delta(Z),  rho(x) = asymptotic rank exponent of the graph tensor x,
and rho(x) >= maxcut(x).  So U(Z) < c(Z) would be a violation IF rho(x*) = maxcut(x*) for the optimal x*.
"""
import itertools, math, random
import numpy as np
from scipy.optimize import linprog
from label_lp import *

def cutdom(V0):
    n = len(V0); pairs = list(itertools.combinations(range(n), 2))
    cuts = range(1, 1 << (n - 1))
    A = np.array([[1.0 if ((m >> i) & 1) != ((m >> j) & 1) else 0.0 for m in cuts] for i, j in pairs])
    b = np.array([dist(V0[i], V0[j]) for i, j in pairs])
    r = linprog(np.ones(A.shape[1]), A_ub=-A, b_ub=-b, bounds=[(0, None)] * A.shape[1], method="highs")
    emb = linprog(np.zeros(A.shape[1]), A_eq=A, b_eq=b, bounds=[(0, None)] * A.shape[1], method="highs").status == 0
    # dual solution = optimal graph weights x (normalised to maxcut 1)
    x = -r.ineqlin.marginals
    return r.fun, emb, dict(zip(pairs, np.round(x, 4)))

def U(V0, k=3):
    full = (1 << len(V0)) - 1
    r = solve(V0, k, full, verbose=False)
    return -r.fun if r.status == 0 else None

random.seed(3)
worst = (9, None)
def report(V0, label):
    global worst
    c, emb, x = cutdom(V0); u = U(V0)
    print(f"{label:34s} n={len(V0)} l1={emb!s:5s} c(Z)={c:.5f} U(Z)={u:.5f} U/c={u/c:.5f}")
    if u / c < worst[0]: worst = (u / c, label, {k: v for k, v in x.items() if v > 1e-6})
a = 1.0
tips = [Pt(i, a, 0.0, f"p{i}") for i in range(3)]
report(tips, "3 tips")
report(tips + [Pt(None, 0, 0.35, "Q+"), Pt(None, 0, -0.35, "Q-")], "tips + Q+-(0.35)")
report(tips + [Pt(None, 0, 1.0, "Q+"), Pt(None, 0, -1.0, "Q-")], "tips + Q+-(1)  [Sub(F_2^2)]")
report(tips + [Pt(None, 0, 2.0, "Q+"), Pt(None, 0, -2.0, "Q-")], "tips + Q+-(2)")
report([Pt(i, a, s * 0.7, f"p{i}{s}") for i in range(3) for s in (1, -1)], "prism: tips x {+-0.7}")
report([Pt(i, a, s * 2.0, f"p{i}{s}") for i in range(3) for s in (1, -1)], "prism: tips x {+-2}")
report([Pt(i, a, s * 0.3, f"p{i}{s}") for i in range(3) for s in (1, -1)], "prism: tips x {+-0.3}")
for t in range(40):
    n = random.choice([5, 6, 7, 8])
    V0 = []
    for j in range(n):
        if random.random() < 0.25: V0.append(Pt(None, 0, random.uniform(-1.5, 1.5), f"r{j}"))
        else: V0.append(Pt(j % 3, random.uniform(0.1, 1.5), random.uniform(-1.5, 1.5), f"r{j}"))
    report(V0, f"random #{t}")
print("smallest U/c:", worst)
