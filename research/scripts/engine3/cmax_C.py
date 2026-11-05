"""Variant cost c_max(T) = max_g log2 rank(G_g | rest) (coordinator's 'max over the three group-vs-rest flattenings';
a lower bound for c_flat and for every network).  Values for f_C and the two-term decomposition, N = 2, 3."""
import numpy as np, itertools, math
from lib import *; from cpieces import assemble
def c_max(cfg, T, k):
    gl = group_legs(cfg, cfg['merges'][k]); return max(math.log2(frank(T, g)) for g in gl)
for N in (2, 3):
    c = config_C(N); F = np.zeros((N,) * 4, dtype=np.int64); Pp = np.zeros_like(F)
    for x, y, u, v in itertools.product(range(N), repeat=4): F[x, y, u, v] = (x == v) * (y == u); Pp[x, y, u, v] = (x == u) * (y == v)
    for nm, T in (('f_C', graph_tensor(c)), ('P(x)F(x)F', assemble(c, [Pp, F, F])), ('B(x)F(x)F', assemble(c, [F - Pp, F, F])), ('PPP', assemble(c, [Pp] * 3))):
        print(f"N={N} {nm}: c_max per merge (bits) {[round(c_max(c, T, k), 3) for k in range(3)]}", flush=True)
