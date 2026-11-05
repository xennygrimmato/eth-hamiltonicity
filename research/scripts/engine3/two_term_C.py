"""Exact (Q, via mod-p ranks) two-term decompositions f_C = P_1(x)F_2(x)F_3 + B_1(x)F_2(x)F_3 at N = 2, 3, 4 (lam = log2 N),
P = [x=u][y=v], B = F - P on pair 1.  Term 1 under merge 0, term 2 under merge 1.  c_flat computed exactly; the network
costs are explicit (P(x)F(x)F: bonds G0G1 = N, G0G2 = N^3, G1G2 = N under merge 0; B(x)F(x)F: bundle of pair 1 carries
rank_row(B) = N(N-1)/2, the other two bundles N^2 each, under merge 1) and equal c_flat."""
import numpy as np, itertools, math
from lib import *; from cpieces import assemble
for N in (2, 3, 4):
    c = config_C(N)
    F = np.zeros((N,) * 4, dtype=np.int64); Pp = np.zeros_like(F)
    for x, y, u, v in itertools.product(range(N), repeat=4): F[x, y, u, v] = (x == v) * (y == u); Pp[x, y, u, v] = (x == u) * (y == v)
    B = F - Pp
    if N == 4:  # 4^12 = 16.7M entries: only per-pair ranks, costs by multiplicativity of bundle ranks
        rowB = rank_modp(B.reshape(N * N, -1)); print(f"N=4: rank_row(B) = {rowB} = N(N-1)/2; term costs 5*2 = 10 bits and log2({rowB})+8 = {math.log2(rowB)+8:.3f} bits; S = {4**5 + rowB*4**4} vs N^6 = {4**6}")
        continue
    T1 = assemble(c, [Pp, F, F]); T2 = assemble(c, [B, F, F]); assert (T1 + T2 == graph_tensor(c)).all()
    v1 = cost_vector(c, T1); v2 = cost_vector(c, T2)
    print(f"N={N}: P(x)F(x)F c_flat per merge (bits) {[round(x,3) for x in v1]};  B(x)F(x)F {[round(x,3) for x in v2]};  "
          f"S = {2**v1[0] + 2**v2[1]:.0f} vs N^6 = {N**6};  max cost {max(v1[0], v2[1]):.3f} of {6*math.log2(N):.3f} bits", flush=True)
