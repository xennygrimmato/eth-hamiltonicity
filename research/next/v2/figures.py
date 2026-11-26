import math, json, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from cone import Cone
from distortion import kernel
pi = math.pi
fig, ax = plt.subplots(1, 3, figsize=(16.5, 5.4))

# --- panel 1: the cone over a circle of length 3 pi, drawn with angles compressed by 2/3 so that it fits in the page
L = 3*pi; X = Cone(L); sc = 2*pi/L
def xy(p): return p[0]*math.cos(p[1]*sc), p[0]*math.sin(p[1]*sc)
a = ax[0]
for k in range(6):
    t = k*L/6; a.plot([0, 1.25*math.cos(t*sc)], [0, 1.25*math.sin(t*sc)], color="0.75", lw=1)
    a.text(1.36*math.cos(t*sc), 1.36*math.sin(t*sc), "%s" % ["0", "π/2", "π", "3π/2", "2π", "5π/2"][k], ha="center", va="center", fontsize=9, color="0.4")
tt = np.linspace(0, L, 400); a.plot(np.cos(tt*sc), np.sin(tt*sc), color="0.85", lw=1)
pairs = [((1.0, 0.15*pi), (1.0, 0.85*pi), "tab:blue", "angle 0.7π: straight chord"),
         ((1.0, 1.1*pi), (1.0, 2.05*pi), "tab:green", "angle 0.95π: chord"),
         ((1.0, 0.4*pi), (0.9, 1.9*pi), "tab:red", "angle 1.5π ≥ π: through the tip"),
         ((0.8, 2.3*pi), (1.0, 0.75*pi), "tab:orange", "angle 1.45π (the short way round): tip")]
for p, q, col, lab in pairs:
    pts = [X.geodesic_point(p, q, s) for s in np.linspace(0, 1, 120)]
    a.plot([xy(z)[0] for z in pts], [xy(z)[1] for z in pts], color=col, lw=2.2, label="%s, d = %.2f" % (lab, X.dist(p, q)))
    for z in (p, q): a.plot(*xy(z), "o", color=col, ms=6)
a.plot(0, 0, "k*", ms=11); a.set_aspect("equal"); a.axis("off"); a.legend(fontsize=7.6, loc="lower center", bbox_to_anchor=(0.5, -0.2))
a.set_title("Cone with total angle 3π at the tip\n(drawn with angles compressed by 2/3; chords look curved)", fontsize=10)

# --- panel 2: how well a positive-definite kernel can imitate the truncated cosine on the link
a = ax[1]; x = np.linspace(1e-3, 3*pi, 2000)
a.plot(x/pi, 1 - np.cos(np.minimum(x, pi)), "k", lw=2.2, label="cone:  1 − cos(min(angle, π))")
for c, col in [(0.5, "tab:blue"), (0.25, "tab:orange")]:
    a.plot(x/pi, 1 - kernel(400*pi, c, x), color=col, lw=1.8, label="Hilbert image:  1 − exp(−%.2g·angle²)" % c)
a.axhline(1, color="0.8", lw=0.8); a.set_xlabel("angle between two directions (units of π)"); a.set_ylabel("angular part of squared distance, per r·s·2")
a.set_title("Near directions match, far directions lose a factor 2:\nany cone over a circle is within 1.42 of Euclidean", fontsize=10); a.legend(fontsize=8)

# --- panel 3: cones over cages against the Euclidean Poincaré constant of the same graph
a = ax[2]; rows = json.load(open("cages.json")); names = ["%s\n(n=%d, girth %d)" % (r[0], r[1], r[2]) for r in rows]
xs = np.arange(len(rows)); w = 0.38
a.bar(xs - w/2, [r[4] for r in rows], w, color="tab:blue", label="Euclidean placements: 1/(1−λ₂)")
a.bar(xs + w/2, [r[5] for r in rows], w, color="tab:red", label="placement in the cone over the graph itself")
a.set_xticks(xs); a.set_xticklabels(names, fontsize=7.2, rotation=20); a.set_ylabel("mean squared distance, all pairs / edges")
a.set_title("Cones over high-girth cubic graphs break the\ngraph's own Euclidean Poincaré constant", fontsize=10); a.legend(fontsize=8)
plt.tight_layout(); plt.savefig("fig_overview.png", dpi=170); print("saved")
