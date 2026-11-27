"""Label LP in T x T' x R (a convex subset of C_4(2): block sum of two lines, one mean level).  Flats are R^3.
Tips of T over the point (centre of T', 0).  The spine of the T-book is the book T' x R: non-flat.
Compare K = octagon-like set in a flat part of the spine (two rays of T') with the same set on all three rays."""
import itertools, math, sys, time
from gen_lp import solve
from filt_lp import mean_width
class P3:
    def __init__(s, i, r, k, t, y):
        if r < 1e-12: i, r = None, 0.0
        if t < 1e-12: k, t = None, 0.0
        s.i, s.r, s.k, s.t, s.y = i, r, k, t, y
def run(pts, target):
    n = len(pts)
    def flatW(m):
        S = [pts[i] for i in range(n) if m >> i & 1]
        I = sorted({p.i for p in S if p.i is not None}); K = sorted({p.k for p in S if p.k is not None})
        if len(I) > 2 or len(K) > 2: return None
        I = I or [0]; K = K or [0]
        return mean_width([(0.0 if p.i is None else (p.r if p.i == I[0] else -p.r),
                            0.0 if p.k is None else (p.t if p.k == K[0] else -p.t), p.y) for p in S])
    return solve(n, flatW, target)[0]
a = 1.0
tips = [P3(i, a, None, 0, 0.0) for i in range(3)]
if __name__ == '__main__':
    for R in (0.25, 0.2747, 0.30):
        ang = [-math.pi / 3, 0.0, math.pi / 3]
        def Kset(rays): return [P3(None, 0, None, 0, R), P3(None, 0, None, 0, -R)] + [P3(None, 0, k, R * math.cos(f), R * math.sin(f)) for k in rays for f in ang]
        for rays, label in (((0, 1), "flat spine part (rays 0,1 of T'): octagon"), ((0, 1, 2), "all three rays of T' (non-flat spine)")):
            t0 = time.time(); v = run(tips + Kset(rays), 0b111)
            print(f"R={R:.4f}  {label:45s} n={3 + len(Kset(rays)):2d}  max delta(tips) = {v:.5f}  [{time.time() - t0:.0f}s]", flush=True)
    print("reference: flat spine R^2 with a disk: 2.78943;  M = infinity: 2.73423;  (8/3) = 2.66667")
