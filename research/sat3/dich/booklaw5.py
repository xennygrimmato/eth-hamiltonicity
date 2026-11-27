"""Does the law L of booklaw4.py satisfy the tripod inequality L >= D*(a) on triples with one point on each of
three pages of T_3 x R (arbitrary radii and heights)?  And on the H-configurations of T_4 x R (slope of L - Lcross)?"""
import math, random
from label_lp import Pt, dist, dstar
from booklaw4 import L
random.seed(12); worst = (9, None)
for t in range(400):
    S = [Pt(i, random.uniform(0.02, 2.0), random.uniform(-1.5, 1.5)) for i in range(3)]
    d = [dist(S[0], S[1]), dist(S[0], S[2]), dist(S[1], S[2])]
    ds = dstar(*d); hp = sum(d) / 2; l = L(S, 3)
    if l / ds < worst[0]: worst = (l / ds, [(round(p.r, 3), round(p.y, 3)) for p in S], round(l, 5), round(ds, 5), round(hp, 5))
print("400 random triples on three pages: min L/D* =", worst)
for h in (0.2, 0.1, 0.05):
    m = 1.0; S = [Pt(0, h / 2, 0.0), Pt(1, h / 2, 0.0), Pt(2, h / 2, m), Pt(3, h / 2, m)]
    Lc = math.hypot(h, m); l = L(S, 4)
    print(f"H-configuration h={h}: L = {l:.6f}, cross distance {Lc:.6f}, slope (L - Lcross)/h = {(l - Lc) / h:.4f}  (decoder threshold 0.5)")
