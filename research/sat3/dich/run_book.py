import math, random, sys, time
from label_lp import *
a = 1.0
def tips(k=3): return [Pt(i, a, 0.0, f"p{i}") for i in range(k)]
def run(V0, k=3, label="", tripod=False, sense="max"):
    t = mask_of(V0, {f"p{i}" for i in range(k)})
    t0 = time.time()
    r = solve(V0, k, t, sense=sense, tripod=tripod, verbose=False)
    val = None if r.status != 0 else (-r.fun if sense == "max" else r.fun)
    print(f"{label:50s} n={len(V0):2d} status={r.status} {sense} delta(tips)={val}  [{time.time()-t0:.1f}s]", flush=True)
    return val
H0 = 1/(2*math.sqrt(2))
base = tips() + [Pt(None, 0, H0, "Q+"), Pt(None, 0, -H0, "Q-")]
run(base, label="tips + Q+-(H*)")
run(base + [Pt(None, 0, 0.0, "c")], label="+ centre")
run(base + [Pt(None, 0, 0.0, "c"), Pt(None, 0, 1.0, "R+"), Pt(None, 0, -1.0, "R-")], label="+ centre + spine +-1")
run(base + [Pt(None, 0, 0.15, "s+"), Pt(None, 0, -0.15, "s-"), Pt(None, 0, 0.7, "R+"), Pt(None, 0, -0.7, "R-")], label="+ spine +-0.15, +-0.7")
off = [Pt(i, 0.5, s*0.3, f"o{i}{s}") for i in range(3) for s in (1, -1)]
run(base + off, label="+ off-spine (i,0.5,+-0.3)")
off2 = [Pt(i, 1.5, 0.0, f"x{i}") for i in range(3)]
run(base + off2 + [Pt(None, 0, 0.0, "c")], label="+ outer tips r=1.5 + centre")
off3 = [Pt(i, 0.4, 0.0, f"m{i}") for i in range(3)] + [Pt(i, 1.0, 0.5, f"u{i}") for i in range(3)]
run(base + off3, label="+ (i,.4,0), (i,1,.5)")
# feasibility with the tripod inequality on all triples, and the minimum
run(base + off, label="[min] + off-spine", sense="min")
run(base + off, label="[tripod on, max] + off-spine", tripod=True)
run(base + off, label="[tripod on, min] + off-spine", tripod=True, sense="min")
random.seed(1)
best = 9
for trial in range(12):
    aux = []
    for j in range(7):
        if random.random() < 0.4: aux.append(Pt(None, 0, random.uniform(-1.5, 1.5), f"r{j}"))
        else: aux.append(Pt(random.randrange(3), random.uniform(0.05, 2.0), random.uniform(-1.2, 1.2), f"r{j}"))
    v = run(base + aux, label=f"random aux #{trial}")
    if v is not None: best = min(best, v)
print("best random:", best, " chain value 2*sqrt(2) =", 2*math.sqrt(2))
