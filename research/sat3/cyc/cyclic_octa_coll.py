"""Collinear edges in the octahedron arrangement: dim(W_n ^ W_n') = 2 (the common hub only), exactly.
Then a collinear edge gets s = delta in one chosen merge and 0 in the other two (cyclic-cap.md section 4.3)."""
import sys
from cyclic_octa import setup, rho, rank_mod
import math
for g, par in [(5, (1,1,2,3)), (7, (1,1,2,3)), (12, (1,1,2,7)), (19, (1,1,2,3)), (24, (1,1,2,7)), (31, (1,1,2,3)), (40, (1,1,2,3))]:
    q, w, pts, M = setup(g, *par)
    ok = True
    for t in range(1, g):
        for tt in ((0, t), (t, 0), (t, (-t) % g)):
            ok &= rank_mod(M + rho(M, tt, pts, w, q), q) == 8
    print("g = %d params %s: all collinear pairs meet exactly in the common hub: %s ; level value = ((g-2)sqrt(2/5)+1)/(g+1) = %.4f"
          % (g, par, ok, ((g-2)*math.sqrt(0.4)+1)/(g+1)))
