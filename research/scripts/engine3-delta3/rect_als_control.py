"""Control for prism_als.py: the rectangle at N = 2, F = R + C with R a row product (rank 1 across rows) and C a column
product; App. H gives [x=v][y=u] = [x=u][y=v] - [x!=y](-1)^x [u!=v](-1)^u, so ALS must reach residual 0."""
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
F = np.zeros((2, 2, 2, 2))  # x y u v
for x in range(2):
    for y in range(2): F[x, y, y, x] = 1
def run(sweeps=200):
    r1 = rng.standard_normal((2, 2)); r2 = rng.standard_normal((2, 2)); c1 = rng.standard_normal((2, 2)); c2 = rng.standard_normal((2, 2))
    for _ in range(sweeps):
        T = F - np.einsum('xu,yv->xyuv', c1, c2)
        # R = r1[x,y] r2[u,v]: solve r1 given r2, then r2
        M = r2.reshape(-1); r1 = (T.reshape(4, 4) @ M / (M @ M)).reshape(2, 2)
        M = r1.reshape(-1); r2 = (M @ T.reshape(4, 4) / (M @ M)).reshape(2, 2)
        T = F - np.einsum('xy,uv->xyuv', r1, r2)
        Tc = T.transpose(0, 2, 1, 3).reshape(4, 4)
        M = c2.reshape(-1); c1 = (Tc @ M / (M @ M)).reshape(2, 2)
        M = c1.reshape(-1); c2 = (M @ Tc / (M @ M)).reshape(2, 2)
    return np.linalg.norm(F - np.einsum('xy,uv->xyuv', r1, r2) - np.einsum('xu,yv->xyuv', c1, c2)) / np.linalg.norm(F)
res = [run() for _ in range(50)]
print('rectangle control: min residual %.2e, median %.3f, #exact(<1e-8) %d of 50' % (min(res), np.median(res), sum(r < 1e-8 for r in res)))
