# Sanity tests: (1) in the plane (L = 2 pi) the axioms must be consistent, and we see how tightly they pin delta
#               (2) a tripod: what range do the axioms leave for the rate of a label shared by the three tips?
import math, numpy as np
from cone import *
pi = math.pi
def ring(L, k, r=1.0, with_tip=True, with_mid=False):
    X = Cone(L); pts = [(r, i*L/k) for i in range(k)]; names = ["p%d" % i for i in range(k)]
    if with_tip: pts.append((0.0, 0.0)); names.append("o")
    if with_mid:
        for i in range(k):
            pts.append(X.geodesic_point(pts[i], pts[(i+1) % k], 0.5)); names.append("m%d" % i)
    return X, pts, names
for L, lab in [(2*pi, "plane"), (3*pi, "cone 3pi")]:
    X, pts, names = ring(L, 6)
    lp = RateLP(X, pts, names, convex_k=3, verbose=True)
    full = lp.mask(range(6))
    print(lab, "six points on the unit circle + tip: range of delta(all six) =", lp.range_of(full),
          " (plane truth: half perimeter of hexagon = 3)" if L == 2*pi else "")
# tripod = cone over three points pairwise at angle >= pi : use L = 3 pi, rays at 0, pi, 2 pi
X = Cone(3*pi); legs = [0, pi, 2*pi]
pts = [(1.0, t) for t in legs] + [(0.0, 0.0)] + [(0.5, t) for t in legs]
names = ["a", "b", "c", "o", "a'", "b'", "c'"]
lp = RateLP(X, pts, names, convex_k=4, verbose=True)
print("tripod with unit arms: range of delta(tips) =", lp.range_of(lp.mask([0, 1, 2])), " (OpenAI: 8/3 = 2.667 is extremal for omega = 9/4; Steiner tree = 3)")
