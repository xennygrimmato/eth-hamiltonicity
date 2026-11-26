"""Six pages around a spine: the flat structure forced around the segment [0, I] by the rank metric rho_2.

Pages H_1..H_6 (half-planes along a common spine).  Pages j, k with |j-k| = 2 or 3 (mod 6) form a flat plane; adjacent
pages are perpendicular and pages j-1, j, j+1 lie in a flat 3-space G_j.  A site is (page, t, z): distance t >= 0
from the spine, coordinate z along it.  Only distances and flat sets that are forced are used:
  same page: Euclid;  adjacent pages: sqrt(t^2 + s^2 + dz^2);  non-adjacent: sqrt((t+s)^2 + dz^2).
Flat sets: sites within pages {j-1, j, j+1} (3-dimensional mean width) or within {j, j+3}.
"""
import sys, math, itertools, numpy as np
sys.path.insert(0, "../v2")
from cone import RateLP, half_perimeter
from scipy.spatial import ConvexHull

def mean_width(P):
    """sqrt(2 pi) E max <g, p>: a segment has its length; planar sets half their perimeter"""
    P = np.asarray(P, float); P = P - P.mean(0)
    u, s, vt = np.linalg.svd(P, full_matrices=False)
    r = int((s > 1e-9).sum())
    if r == 0: return 0.0
    if r <= 2:
        Q = P @ vt[:2].T if vt.shape[0] >= 2 else np.c_[P @ vt[0], np.zeros(len(P))]
        return half_perimeter(list(Q))
    Q = P @ vt[:3].T
    hull = ConvexHull(Q)
    edges = {}
    for simplex, eq in zip(hull.simplices, hull.equations):
        for a, b in itertools.combinations(sorted(simplex), 2): edges.setdefault((a, b), []).append(eq[:3])
    tot = 0.0
    for (a, b), ns in edges.items():
        if len(ns) != 2: continue
        c = float(np.clip(np.dot(ns[0], ns[1]), -1, 1))
        tot += np.linalg.norm(Q[a] - Q[b])*math.acos(c)
    return tot/(2*math.pi)

class Hexbook:
    def __init__(self, npages=6): self.n = npages
    def rel(self, a, b):
        d = (a - b) % self.n; d = min(d, self.n - d)
        return d                                       # 0 same, 1 adjacent, >= 2 opposite through the spine
    def dist(self, p, q):
        if p[0] is None or q[0] is None: return 1e9
        (a, t, z), (b, s, w) = p, q
        if t == 0 or s == 0 or a == b: return math.sqrt((t - s)**2 + (z - w)**2)
        if self.rel(a, b) == 1: return math.sqrt(t*t + s*s + (z - w)**2)
        return math.sqrt((t + s)**2 + (z - w)**2)
    def geodesic_point(self, p, q, lam):
        (a, t, z), (b, s, w) = p, q
        if t == 0 or s == 0 or a == b:
            return (a if t > 0 else b, (1-lam)*t + lam*s, (1-lam)*z + lam*w)
        if self.rel(a, b) == 1: return (None, 0, 0)    # leaves the pages; not used
        x = (1-lam)*t - lam*s
        return (a, x, (1-lam)*z + lam*w) if x >= 0 else (b, -x, (1-lam)*z + lam*w)
    def flat_coords(self, pts):
        pages = sorted({a for a, t, z in pts if t > 0})
        if not pages: return [np.array([0.0, z]) for a, t, z in pts]
        n = self.n
        for j in range(n):                             # inside G_j
            if all((a - j) % n in (n-1, 0, 1) for a in pages):
                vec = {(j-1) % n: (1, 0), j: (0, 1), (j+1) % n: (-1, 0)}
                return [np.array([vec[a][0]*t, vec[a][1]*t, z]) if t > 0 else np.array([0.0, 0.0, z]) for a, t, z in pts]
        if len(pages) == 2 and self.rel(*pages) >= 2:
            return [np.array([(t if a == pages[0] else -t), z]) for a, t, z in pts]
        return None

class LP3(RateLP):
    """RateLP with mean widths in dimension up to 3"""
    def _build(self, convex_k, verbose):
        import cone
        old = cone.half_perimeter
        cone.half_perimeter = mean_width               # flat_coords may now return 3-vectors
        try: super()._build(convex_k, verbose)
        finally: cone.half_perimeter = old

def bound(space, pts, target, omega=None, convex_k=2):
    lp = LP3(space, pts, convex_k=convex_k)
    m = lp.mask(target)
    hi = lp.solve([(m, 1.0)], -1)
    return (None if hi.status != 0 else -hi.fun), lp

if __name__ == "__main__":
    r = 1/math.sqrt(2)
    # sanity: unit cube mean width (ours = 2 * 3/2 = 3), unit square 2, segment 1
    cube = list(itertools.product([0, 1], repeat=3))
    print("mean width checks: cube %.6f (3), square %.6f (2), regular tetrahedron side 1: %.6f" % (
        mean_width(cube), mean_width([(0,0,0),(1,0,0),(1,1,0),(0,1,0)]),
        mean_width([(0,0,0),(1,0,0),(.5,math.sqrt(3)/2,0),(.5,math.sqrt(3)/6,math.sqrt(2/3))])))
    print("tips P1, P3, P5 at distance r = 1/sqrt2 from the spine; perimeter 3 sqrt2 = %.4f" % (3*math.sqrt(2)))
    print("%-58s %s" % ("configuration", "max delta(tips)   => omega >="))
    for label, pages in (("three pages (book)", [0, 2, 4]), ("six pages", [0, 1, 2, 3, 4, 5])):
        for ts in ([0.25], [0.25, 0.5], [0.15, 0.3, 0.5]):
            pts = [(a, r, 0.0) for a in pages] + [(0, 0.0, 0.0)] + [(0, 0.0, s*t) for t in ts for s in (1, -1)]
            tgt = [pages.index(a) for a in (0, 2, 4)]
            U, lp = bound(Hexbook(6), pts, tgt)
            print("%-58s %.5f           %.5f" % ("%s, spine points at +-%s" % (label, ts), U, 3*math.sqrt(2)/U))
