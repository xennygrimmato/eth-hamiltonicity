"""Search for configurations in T_3 x R with U(Z) < c(Z) and print the optimal graph weights x*.
A violation needs a proved bound rho(x*) < sum x*_ij d_ij / U(Z)  (rho >= maxcut always; rho(triangle) = omega)."""
import itertools, math, random, sys
import numpy as np
from label_lp import *
from cutdom import cutdom, U
random.seed(11)
found = []
for t in range(int(sys.argv[1]) if len(sys.argv) > 1 else 150):
    n = random.choice([5, 6, 6, 7])
    V0 = []
    for j in range(n):
        if random.random() < 0.3: V0.append(Pt(None, 0, random.uniform(-1.0, 1.0), f"r{j}"))
        else: V0.append(Pt(j % 3, random.uniform(0.2, 1.5), random.uniform(-1.0, 1.0), f"r{j}"))
    c, emb, x = cutdom(V0); u = U(V0)
    if u is None: print("LP infeasible!", [(p.ray, p.r, p.y) for p in V0]); continue
    if u / c < 0.999:
        xs = {k: float(v) for k, v in x.items() if v > 1e-6}
        tri = [T for T in itertools.combinations(range(n), 3) if all(e in xs for e in itertools.combinations(T, 2))]
        found.append((u / c, n, emb, xs, tri, [(p.ray, round(p.r, 3), round(p.y, 3)) for p in V0]))
found.sort(key=lambda z: z[0])
print("configurations with U/c < 0.999:", len(found))
for f in found[:8]:
    print(f"U/c={f[0]:.4f} n={f[1]} l1={f[2]} x*={f[3]}\n    triangles in supp x*: {f[4]}\n    pts={f[5]}")
print("all found have a triangle in the support of x*:", all(len(f[4]) > 0 for f in found))
