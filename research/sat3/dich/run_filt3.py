import math, random, sys, time
from filt_lp import *
sp = Space(3)
a = 1 / math.sqrt(2)
V = sp.V
tip = lambda v: ((1.0, span([v])), (0.0, V))
tips = [tip(1), tip(2), tip(3)]          # three points of the line W = <1,2>
tmask = 0b111
print("check mean_width: unit square", mean_width([(0,0,0),(1,0,0),(1,1,0),(0,1,0)]), " unit cube", mean_width(list(itertools.product((0,1),repeat=3))), "(expected 2 and 3: W is additive over the orthogonal unit segments)")
print("tip distances", sp.dist(tips[0], tips[1]), sp.dist(tips[0], tips[2]), " arm a =", a, " D* = (8/3)a =", 8/3*a, " hub 3a =", 3*a)
def K_poly(m, R, w=4, phase=0.0):
    """m-gon of radius R around the pod centre c = (1/2,1/2,0) in the wall x1 = x2 of the apartment (1,2,w)"""
    out = []
    for j in range(m):
        th = phase + 2 * math.pi * j / m
        s = 0.5 + R * math.cos(th) / math.sqrt(2); y = R * math.sin(th)
        out.append(sp.filt((1, 2, w), (s, s, y)))
    return out
def run(aux, label, **kw):
    t0 = time.time()
    v = solve(sp, tips + aux, tmask, verbose=False, **kw)
    print(f"{label:58s} n={3+len(aux):2d}  max delta(tips)/a = {None if v is None else v/a:.5f}   [{time.time()-t0:.0f}s]", flush=True)
    return v
print("-- product chain T_3 x R^2 inside C_3(2): K = polygon in the wall (M = 2); analytic disk optimum 2.78943 at R = 0.2313 a")
Rs = 0.2313 * a
for m, R in [(2, 0.25), (6, Rs), (8, Rs), (8, 1.05 * Rs), (9, 1.03 * Rs)]:
    run(K_poly(m, R), f"K = {m}-gon, R = {R:.4f}")
print("-- hull invariance switched on (sound closure)")
run(K_poly(6, Rs), "K = 6-gon, hull on", hull=True)
print("-- with the tripod inequality on all non-flat triples: feasibility and minimum")
run(K_poly(6, Rs), "K = 6-gon, tripod on (max)", tripod=True)
run(K_poly(6, Rs), "K = 6-gon, tripod on (min)", tripod=True, sense="min")
print("-- random auxiliary points of C_3(2) (vertices of both types at random scales, two-step flags, spine points)")
random.seed(7)
pts7 = list(range(1, 8)); lines = [b for b in itertools.combinations(pts7, 2)]
def rnd_point():
    b = random.choice(sp.bases); b = list(b); random.shuffle(b)
    kind = random.random()
    if kind < 0.3: lv = (random.uniform(0.2, 1.5), 0, 0)
    elif kind < 0.6: x = random.uniform(0.2, 1.2); lv = (x, x, 0)
    elif kind < 0.8: lv = (random.uniform(0.5, 1.5), random.uniform(0.0, 0.5), random.uniform(-0.5, 0.0))
    else: s = random.uniform(0.2, 0.9); lv = (s, s, random.uniform(-0.5, 0.4)); b = [1, 2, random.choice([4, 5, 6, 7])]
    return sp.filt(tuple(b), lv)
best = 9
for trial in range(25):
    aux = []
    while len(aux) < 7:
        F = rnd_point()
        if F not in aux and F not in tips: aux.append(F)
    v = run(aux, f"random #{trial}")
    if v is not None: best = min(best, v / a)
print("best random value / a:", best, "  (product chains: 2.82843 for M=1, 2.78943 for M=2; D* = 2.66667)")
