"""fig_book.png: (a) the book forced around [0, I] by the rank metric on 2x2 binary matrices,
(b) the upper bound on the shared-label rate of its three tips against the spine dimension,
(c) the resulting chain of implications."""
import math, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import FancyBboxPatch
from bookbound import U, F
from scipy import optimize, stats

BLUE, ORANGE, INK, MUTE, GRID = "#257de0", "#f47230", "#191919", "#666666", "#e4e4e4"
plt.rcParams.update({"font.size": 9, "axes.edgecolor": MUTE, "axes.labelcolor": INK, "xtick.color": MUTE, "ytick.color": MUTE,
                     "axes.spines.top": False, "axes.spines.right": False})
fig = plt.figure(figsize=(14.5, 5.3))

# (a) the book
ax = fig.add_subplot(1, 3, 1, projection="3d")
r = 1/math.sqrt(2); zero, one = np.array([0, 0, -r]), np.array([0, 0, r])
dirs = {}                                                   # unfolded picture: tips 1,3,5 at 120 degrees, 2,4,6 between
for j in range(6):
    ang = math.radians(60*j); dirs[j] = np.array([r*math.cos(ang), r*math.sin(ang), 0])
for j in range(6):
    main = j % 2 == 0
    ax.add_collection3d(Poly3DCollection([[zero, one, dirs[j]]], facecolor=BLUE if main else "#c8c8c8",
                                         alpha=0.30 if main else 0.12, edgecolor=BLUE if main else "#aaaaaa", linewidth=0.8))
ax.plot(*zip(zero, one), color=INK, lw=2)
for j in range(6):
    main = j % 2 == 0
    ax.scatter(*dirs[j], color=BLUE if main else "#9a9a9a", s=36 if main else 16, depthshade=False)
for j, lab in zip((0, 2, 4), ("$E_1$", "$E_3$", "$E_5$")): ax.text(*(dirs[j]*1.18), lab, color=INK, ha="center")
ax.scatter(*zero, color=INK, s=22, depthshade=False); ax.scatter(*one, color=INK, s=22, depthshade=False)
ax.text(0, 0, -r - 0.14, "0", color=INK, ha="center"); ax.text(0, 0, r + 0.07, "I", color=INK, ha="center")
for z in (0.25, -0.25): ax.plot([0], [0], [z], marker="o", color=ORANGE, ms=6, zorder=20, linestyle="none")
ax.text(0.55, 0.75, -0.62, "orange: two spine sites", color=INK, fontsize=8, ha="center")
ax.set_xlim(-0.75, 0.75); ax.set_ylim(-0.75, 0.75); ax.set_zlim(-0.75, 0.75); ax.set_axis_off(); ax.view_init(22, 28)
ax.set_title("(a) Forced around the segment [0, I]: six flat pages.\nBlue pages are pairwise flat (a book); tips pairwise $\\sqrt{2}$ apart",
             fontsize=9, color=INK, y=0.93)

# (b) bound against spine dimension
ax = fig.add_subplot(1, 3, 2)
ks = [1, 2, 3, 4, 5, 7, 10, 15, 20, 30, 50, 100]
om = [6/optimize.minimize_scalar(lambda x: U(k, x), bounds=(1e-4, 2), method="bounded").fun for k in ks]
z = stats.norm.ppf(2/3); lim = 2*math.exp(z*z/2)
ax.plot(ks, om, color=BLUE, lw=2, marker="o", ms=4)
ax.set_xscale("log"); ax.set_ylim(1.98, 2.40); ax.set_xlim(0.9, 130)
for y, lab, c in ((2.0, "2  (classical conjecture)", MUTE), (lim, "limit 2.1944", BLUE), (2.25, "9/4  (OpenAI's claimed value)", ORANGE), (2.3713, "2.3713  (best bound before October)", MUTE)):
    ax.axhline(y, color=c, lw=1, ls=(0, (4, 3)) if c != BLUE else (0, (1, 2)))
    ax.text(125, y + 0.006, lab, color=INK, ha="right", fontsize=8)
ax.annotate("3/$\\sqrt{2}$ = 2.1213\n(2 x 2 matrices alone)", (1, om[0]), (1.6, 2.05), color=INK, fontsize=8, arrowprops=dict(arrowstyle="-", color=MUTE, lw=0.7))
ax.set_xlabel("dimension of the spine (rank metric on matrices of size k + 1)"); ax.set_ylabel("lower bound on $\\omega$ if the rank metric is a price")
ax.grid(axis="y", color=GRID, lw=0.6); ax.set_axisbelow(True)
ax.set_title("(b) If the contracting hypothesis fails, $\\omega \\geq 2.194$", fontsize=9, color=INK)

# (c) chain
ax = fig.add_subplot(1, 3, 3); ax.set_axis_off(); ax.set_xlim(0, 1); ax.set_ylim(0, 1)
boxes = [("no ports\n(OpenAI)", 0.90), ("contracting hypothesis fails\n(Anthropic)", 0.71),
         ("rank metrics on $\\mathrm{Mat}_\\mu(\\mathbb{F}_2)$ are prices, all $\\mu$", 0.52),
         ("books $\\times$ cubes are price geometries", 0.33), ("$\\omega \\geq 2e^{z^2/2} = 2.1944$", 0.14)]
notes = ["Thm A: Grassmann gap\n$\\Rightarrow$ port graphs", "Thm D.2 of Anthropic,\nSteps 1-7", "block matrices +\nflat filling", "ball lemma +\nperimeter $\\leq \\omega\\,\\delta$"]
for (t, y) in boxes:
    ax.add_patch(FancyBboxPatch((0.08, y - 0.055), 0.60, 0.11, boxstyle="round,pad=0.01", fc="#f3f7fd", ec=BLUE, lw=1))
    ax.text(0.38, y, t, ha="center", va="center", color=INK, fontsize=8.5)
for (t1, y1), (t2, y2), n in zip(boxes, boxes[1:], notes):
    ax.annotate("", (0.38, y2 + 0.06), (0.38, y1 - 0.06), arrowprops=dict(arrowstyle="-|>", color=INK, lw=1))
    ax.text(0.72, (y1 + y2)/2, n, color=MUTE, fontsize=7.5, va="center")
ax.set_title("(c) Chain of implications (read downwards)", fontsize=9, color=INK)
plt.tight_layout(rect=(0, 0, 1, 0.97)); plt.savefig("fig_book.png", dpi=170, facecolor="white"); print("saved fig_book.png")
