"""[N] K_{3,3}: supply the 9 wires u_i v_j; demand the 6 pairs inside the two sides (uniform).
 flow, cut exactly; local minima of the relaxation by the necessary 4-point (box) inequalities; model spaces."""
import itertools, numpy as np, sys
import tensorlab
from twoapex import flow_value, cut_value
n = 6; pr = list(itertools.combinations(range(n), 2))
U = [0, 1, 2]; Vv = [3, 4, 5]
sup = {(i, j): 1.0 for i in U for j in Vv}
dem = {p: 1.0 for p in pr if p not in sup}
print("K33: flow =", flow_value(n, sup, dem), " cut =", cut_value(n, sup, dem))
num = [sup.get(p, 0.0) for p in pr]; den = [dem.get(p, 0.0) for p in pr]
vals = []
for seed in range(1, 3):
    sol = tensorlab.min_ratio(n, num, den, ["triangle", "box"], 120, seed, 120)
    vals += [round(s["value"], 5) for s in sol if s["max_violation"] < 1e-7]
vals = np.array(vals)
u, c = np.unique(vals, return_counts=True)
print("box relaxation, feasible local minima (value: count):", dict(list(zip(u.tolist(), c.tolist()))[:8]), " total", len(vals))
for k in (1, 2, 3):
    res = tensorlab.min_ratio_tree_products(n, k, num, den, 60, 4000, 1, 3)
    print(f"  product of {k} trees: best", [(round(r[0], 6), r[2]) for r in res[:3]])
