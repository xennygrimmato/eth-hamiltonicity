"""Necessary conditions for a nonpositively curved space to carry tensor prices ("spectral space").

For a finite point set V in a space X, a spectral structure gives a number delta(A) for every nonempty A <= V
(the price per bit of a label shared by the sites of A) with, by OpenAI's "Euclidean geometry in the asymptotic
spectrum of tensors" (24 Nov 2026):
  (pair)     delta({a,b}) = d(a,b), delta({a}) = 0
  (mono)     A <= B  =>  delta(A) <= delta(B)
  (submod)   delta(A u B) + delta(A n B) <= delta(A) + delta(B)   when A n B is nonempty          [Prop. "Copying a common label"]
  (flat)     delta(A) = mean width of A when A lies in a convex Euclidean piece of X             [Thm "Mean width"; patch form in the HC paper]
  (convex)   prices are jointly convex when all legs move along geodesics at constant speed       [Prop. "Joint convexity of placement"]
These are linear in delta, so feasibility on a finite V is a linear programme.  Infeasible => X is not spectral.

Model spaces here: the Euclidean cone over a circle of length L (total angle L at the tip; L = 2 pi is the plane),
and stars (cones over finitely many points)."""
import itertools, math, numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

class Cone:
    """Euclidean cone over a circle of circumference L.  Points are (r, theta)."""
    def __init__(self, L): self.L = L
    def ang(self, t1, t2):
        a = abs(t1 - t2) % self.L
        return min(a, self.L - a)
    def dist(self, p, q):
        (r, t), (s, u) = p, q
        if r == 0 or s == 0: return r + s
        a = self.ang(t, u)
        if a >= math.pi - 1e-12: return r + s
        return math.sqrt(max(0.0, r*r + s*s - 2*r*s*math.cos(a)))
    def geodesic_point(self, p, q, lam):
        """point at fraction lam along the geodesic from p to q"""
        (r, t), (s, u) = p, q
        D = self.dist(p, q)
        if D < 1e-14: return p
        if r == 0: return (lam*s, u)
        if s == 0: return ((1-lam)*r, t)
        a = self.ang(t, u)
        if a >= math.pi - 1e-12:                      # through the tip
            x = lam*D
            return (r - x, t) if x <= r else (x - r, u)
        # planar segment inside the sector between the two rays; signed direction from t to u
        diff = (u - t) % self.L
        sgn = 1.0 if diff <= self.L/2 else -1.0
        P = np.array([r, 0.0]); Q = np.array([s*math.cos(a), s*math.sin(a)])
        M = (1-lam)*P + lam*Q
        return (float(np.hypot(*M)), (t + sgn*math.atan2(M[1], M[0])) % self.L)
    def flat_coords(self, pts):
        """planar coordinates if the points lie in a sector of angle <= pi (a convex Euclidean piece), else None"""
        nz = [(r, t) for r, t in pts if r > 0]
        if not nz: return [np.zeros(2) for _ in pts]
        for (_, t0) in nz:                              # try each point's ray as the start of the arc
            offs = [((t - t0) % self.L) for _, t in nz]
            if max(offs) <= math.pi + 1e-9:
                return [np.array([r*math.cos((t - t0) % self.L), r*math.sin((t - t0) % self.L)]) if r > 0 else np.zeros(2) for r, t in pts]
        return None

def half_perimeter(P):
    """mean width of a planar point set, normalised so that a segment has its length = half the hull perimeter"""
    P = [np.asarray(p, float) for p in P]
    uniq = []
    for p in P:
        if not any(np.linalg.norm(p - q) < 1e-10 for q in uniq): uniq.append(p)
    if len(uniq) == 1: return 0.0
    if len(uniq) == 2: return float(np.linalg.norm(uniq[0] - uniq[1]))
    pts = sorted(map(tuple, uniq))
    cross = lambda o, a, b: (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo = []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 1e-12: lo.pop()
        lo.append(p)
    up = []
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 1e-12: up.pop()
        up.append(p)
    hull = lo[:-1] + up[:-1]
    if len(hull) < 2: return float(np.linalg.norm(np.array(pts[0]) - np.array(pts[-1])))
    return sum(np.linalg.norm(np.array(hull[i]) - np.array(hull[(i+1) % len(hull)])) for i in range(len(hull)))/2

class RateLP:
    def __init__(self, space, pts, names=None, convex_k=2, verbose=False):
        self.X, self.pts, self.n = space, pts, len(pts)
        self.names = names or [str(i) for i in range(self.n)]
        n = self.n; self.nv = (1 << n) - 1                       # variable index = mask - 1
        self.D = np.array([[space.dist(p, q) for q in pts] for p in pts])
        self.rows, self.cols, self.vals, self.rhs, self.tags = [], [], [], [], []       # A_ub x <= b
        self.eq = {}                                             # mask -> forced value
        self._build(convex_k, verbose)
    def _add(self, terms, b, tag):
        r = len(self.rhs)
        for m, c in terms: self.rows.append(r); self.cols.append(m - 1); self.vals.append(c)
        self.rhs.append(b); self.tags.append((tag, terms, b))
    def _build(self, convex_k, verbose):
        n, X, pts = self.n, self.X, self.pts
        for m in range(1, 1 << n):
            idx = [i for i in range(n) if m >> i & 1]
            if len(idx) == 1: self.eq[m] = 0.0; continue
            if len(idx) == 2: self.eq[m] = self.D[idx[0], idx[1]]; continue
            fc = X.flat_coords([pts[i] for i in idx])
            if fc is not None: self.eq[m] = half_perimeter(fc)
        self.nflat = len(self.eq)
        for m in range(1, 1 << n):                               # monotone and submodular
            out = [i for i in range(n) if not m >> i & 1]
            for x in out: self._add([(m, 1.0), (m | 1 << x, -1.0)], 0.0, "mono")
            for x, y in itertools.combinations(out, 2):
                self._add([(m | 1 << x | 1 << y, 1.0), (m, 1.0), (m | 1 << x, -1.0), (m | 1 << y, -1.0)], 0.0, "submod")
        # midpoint triples present in V
        self.mids = []
        for i in range(n):
            for j in range(i, n):
                mp = X.geodesic_point(pts[i], pts[j], 0.5)
                for k in range(n):
                    if X.dist(mp, pts[k]) < 1e-9: self.mids.append((i, j, k)); break
        seen = set()
        for k in range(2, convex_k + 1):                         # joint convexity at midpoints, k legs
            for combo in itertools.combinations_with_replacement(self.mids, k):
                a = b = c = 0
                for (i, j, mm) in combo: a |= 1 << i; b |= 1 << j; c |= 1 << mm
                # legs may also be paired the other way round: (i,j) or (j,i) per leg
                for flips in itertools.product([0, 1], repeat=k):
                    a = b = 0
                    for f, (i, j, mm) in zip(flips, combo):
                        a |= 1 << (j if f else i); b |= 1 << (i if f else j)
                    key = (min(a, b), max(a, b), c)
                    if key in seen or c == a or c == b: continue
                    seen.add(key)
                    self._add([(c, 2.0), (a, -1.0), (b, -1.0)], 0.0, "convex")
        if verbose: print("points", n, "variables", self.nv, "forced (flat/pair)", self.nflat, "inequalities", len(self.rhs), "midpoint triples", len(self.mids))
    def solve(self, objective=None, sense=+1):
        A = coo_matrix((self.vals, (self.rows, self.cols)), shape=(len(self.rhs), self.nv)).tocsr()
        c = np.zeros(self.nv)
        if objective is not None:
            for m, w in objective: c[m - 1] += sense*w
        bounds = [(self.eq[m], self.eq[m]) if m in self.eq else (0, None) for m in range(1, self.nv + 1)]
        res = linprog(c, A_ub=A, b_ub=np.array(self.rhs), bounds=bounds, method="highs")
        return res
    def range_of(self, mask):
        lo = self.solve([(mask, 1.0)], +1); hi = self.solve([(mask, 1.0)], -1)
        if lo.status != 0: return None
        return lo.fun, -hi.fun
    def mask(self, idx): return sum(1 << i for i in idx)
