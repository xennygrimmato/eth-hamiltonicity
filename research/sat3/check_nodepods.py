#!/usr/bin/env python3
"""Check by direct evaluation: Delta3 in the product of nine tripods (one per node n0;
the three hubs of n0 sit on the three arms at radius 1, all other hubs at the centre).
Claim: value = 6 per merge (rho = 2/3) > 3*sqrt(3) (flat)."""
import numpy as np, math
from podprod import config, value
p, H, E, groups = config('delta3')
# hub ids: (k,g) -> k*3+g
J = 9
arms = np.zeros((J, H), dtype=int)
rho = np.zeros((J, H))
j = 0
for r in range(3):
    for c in range(3):
        d = (r - c) % 3
        for k, g in enumerate((r, c, d)):
            arms[j, 3 * k + g] = k + 1      # arm k+1; arm 0 unused (centre hubs have rho = 0)
            rho[j, 3 * k + g] = 1.0
        j += 1
v, det = value(arms, rho, p, E, groups, 'avg', detail=True)
print("nine node-tripods: avg b =", v, " b_k =", det['bk'], " delta =", det['delta'])
print("flat 3*sqrt3 =", 3 * math.sqrt(3), " cap 9/sqrt2 =", 9 / math.sqrt(2))
