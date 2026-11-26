"""Independent finite-M check (verify_pf.far_to_finite + exact distances) of the nine node-tripods on Delta3:
factor j = node (r,c); hubs R_r, C_c, D_{r-c} on arms 0,1,2 at radius 1, all other hubs at the centre."""
import sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import verify_pf as v
hubs = [{'arm': [0] * 9, 't': [0.0] * 9, 'x': []} for _ in range(9)]
j = 0
for r in range(3):
    for c in range(3):
        for k, g in enumerate((r, c, (r - c) % 3)):
            hubs[3 * k + g]['arm'][j] = k
            hubs[3 * k + g]['t'][j] = 1.0
        j += 1
J = dict(design='Delta3', space='far', arms=[3] * 9, k=0, value=6.0, S=7, hubs=hubs)
json.dump(J, open(__file__.rsplit('/', 1)[0] + '/data/far_Delta3_ninetripods.json', 'w'))
for M in (1e2, 1e4, 1e6, 1e8):
    des, pts = v.far_to_finite(J, M)
    b = v.bvec(des, pts, v.model_dist)
    print('M=%g  b = %s  value = %.6f' % (M, [round(x, 6) for x in b], sum(max(0, x) for x in b) / 3))
