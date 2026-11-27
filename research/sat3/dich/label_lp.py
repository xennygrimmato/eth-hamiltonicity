"""Label-calculus LP on finite configurations in the open book  T_k x R  (k half-planes glued along a spine).

T_k x R is the filtration space C_2(q) for k = q+1 (q1-notes section 1): half-plane i = {(r, y) : r >= 0}, all
glued along the spine r = 0.  Flats: unions of two half-planes (apartments).  Distance: Euclidean inside a flat.

Unknowns: delta(S) for every nonempty subset S of a finite point set V0 (the common-label rate of S in a
hypothetical spectral space containing T_k x R isometrically).  Constraints used (sources in dichotomy-attack.md):
  (L0) delta({x}) = 0
  (L1) monotone:      delta(S + x) >= delta(S)
  (L2) submodular on intersecting sets (EG Prop. 5.2), in elemental form
       delta(S+x) + delta(S+y) >= delta(S+x+y) + delta(S),  S nonempty
  (L3) flat law (EG Thm 5.3):  delta(S) = mean width W(S) = half perimeter of the planar hull, S in one flat
  (L4) hull invariance (first step of the proof of EG Thm 5.3): delta(S + z) = delta(S) if z in closed convex hull of S
  (L5) optional: tripod inequality delta({x,y,z}) >= D*(a) (MM Prop. 8.1) for all triples
Objective: maximise (or minimise) delta(target).  max = the best upper bound derivable from (L0)-(L4) inside V0.
"""
import itertools, math, sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog

TOL = 1e-9

class Pt:
    __slots__ = ("ray", "r", "y", "name")
    def __init__(self, ray, r, y, name=""):
        # ray = None for spine points (r = 0)
        if r < TOL: ray, r = None, 0.0
        self.ray, self.r, self.y, self.name = ray, r, y, name

def dist(p, q):
    if p.ray is None or q.ray is None or p.ray == q.ray:
        return math.hypot(p.r - q.r, p.y - q.y)
    return math.hypot(p.r + q.r, p.y - q.y)

def rays_of(S):
    return sorted({p.ray for p in S if p.ray is not None})

def planar_hull(pts):
    pts = sorted(set((round(x, 12), round(y, 12)) for x, y in pts))
    if len(pts) <= 2: return pts
    def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo = []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 1e-13: lo.pop()
        lo.append(p)
    up = []
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 1e-13: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]

def mean_width_planar(pts):
    h = planar_hull(pts)
    if len(h) <= 1: return 0.0
    if len(h) == 2: return math.dist(h[0], h[1])
    return 0.5 * sum(math.dist(h[i], h[(i+1) % len(h)]) for i in range(len(h)))

def flat_coords(S, ri, rj):
    """signed coordinates in the flat ray ri (r>0) u ray rj (r<0)"""
    out = []
    for p in S:
        if p.ray is None: out.append((0.0, p.y))
        elif p.ray == ri: out.append((p.r, p.y))
        else: out.append((-p.r, p.y))
    return out

def flat_width(S):
    rs = rays_of(S)
    if len(rs) > 2: return None
    ri = rs[0] if rs else 0
    rj = rs[1] if len(rs) > 1 else -1
    return mean_width_planar(flat_coords(S, ri, rj))

def in_hull_planar(z, pts):
    h = planar_hull(pts)
    if not h: return False
    if len(h) == 1: return math.dist(z, h[0]) < 1e-9
    if len(h) == 2:
        d = math.dist(h[0], h[1])
        return abs(math.dist(z, h[0]) + math.dist(z, h[1]) - d) < 1e-9
    for i in range(len(h)):
        a, b = h[i], h[(i+1) % len(h)]
        if (b[0]-a[0])*(z[1]-a[1]) - (b[1]-a[1])*(z[0]-a[0]) < -1e-9: return False
    return True

def hull_data(S, k):
    """closed convex hull of S in T_k x R: returns (J, per-ray point lists) with J = hull cap spine (or None)"""
    spine = [p.y for p in S if p.ray is None]
    per = {i: [(p.r, p.y) for p in S if p.ray == i] for i in range(k)}
    J = [min(spine), max(spine)] if spine else None
    for _ in range(200):
        newJ = list(J) if J else None
        act = [i for i in range(k) if per[i]]
        for i, j in itertools.combinations(act, 2):
            A = per[i] + ([(0.0, J[0]), (0.0, J[1])] if J else [])
            B = per[j] + ([(0.0, J[0]), (0.0, J[1])] if J else [])
            for (r1, y1) in A:
                for (r2, y2) in B:
                    if r1 + r2 < TOL: yc = [y1, y2]
                    else: yc = [y1 + (y2 - y1) * r1 / (r1 + r2)]
                    for y in yc:
                        if newJ is None: newJ = [y, y]
                        else: newJ = [min(newJ[0], y), max(newJ[1], y)]
        if newJ == J or (J and newJ and abs(newJ[0]-J[0]) < 1e-13 and abs(newJ[1]-J[1]) < 1e-13): break
        J = newJ
    return J, per

def in_hull(z, S, k):
    J, per = hull_data(S, k)
    if z.ray is None:
        return J is not None and J[0] - 1e-9 <= z.y <= J[1] + 1e-9
    pts = per[z.ray] + ([(0.0, J[0]), (0.0, J[1])] if J else [])
    return in_hull_planar((z.r, z.y), pts)

def dstar(d12, d13, d23):
    a1 = (d12 + d13 - d23) / 2; a2 = (d12 + d23 - d13) / 2; a3 = (d13 + d23 - d12) / 2
    a = [max(x, 0.0) for x in (a1, a2, a3)]
    if min(a) < 1e-12: return sum(a)
    return sum(a) - 1.0 / sum(1.0 / x for x in a)

def solve(V0, k, target, sense="max", tripod=False, verbose=True, extra_lower=None):
    n = len(V0)
    full = (1 << n) - 1
    nv = full  # variable index = mask - 1
    rows, cols, vals, rhs = [], [], [], []   # A_ub x <= b
    erow, ecol, eval_, erhs = [], [], [], []
    nr = 0; ne = 0
    lb = np.zeros(nv); ub = np.full(nv, np.inf)
    nflat = nhull = 0
    for m in range(1, full + 1):
        S = [V0[i] for i in range(n) if m >> i & 1]
        if len(S) == 1:
            lb[m-1] = ub[m-1] = 0.0; continue
        w = flat_width(S)
        if w is not None:
            lb[m-1] = ub[m-1] = w; nflat += 1
        elif tripod and len(S) == 3:
            lb[m-1] = dstar(dist(S[0], S[1]), dist(S[0], S[2]), dist(S[1], S[2]))
    for m in range(1, full + 1):
        S = [V0[i] for i in range(n) if m >> i & 1]
        out = [i for i in range(n) if not m >> i & 1]
        for x in out:
            mx = m | 1 << x
            if len(S) >= 2 and in_hull(V0[x], S, k):
                erow += [ne, ne]; ecol += [mx-1, m-1]; eval_ += [1.0, -1.0]; erhs.append(0.0); ne += 1; nhull += 1
            else:
                rows += [nr, nr]; cols += [m-1, mx-1]; vals += [1.0, -1.0]; rhs.append(0.0); nr += 1
        for x, y in itertools.combinations(out, 2):
            mx, my = m | 1 << x, m | 1 << y
            rows += [nr]*4; cols += [mx | my, m, mx, my]
            cols[-4:] = [(mx | my) - 1, m - 1, mx - 1, my - 1]
            vals += [1.0, 1.0, -1.0, -1.0]; rhs.append(0.0); nr += 1
    A = coo_matrix((vals, (rows, cols)), shape=(nr, nv)).tocsr()
    Ae = coo_matrix((eval_, (erow, ecol)), shape=(ne, nv)).tocsr() if ne else None
    c = np.zeros(nv); c[target - 1] = -1.0 if sense == "max" else 1.0
    res = linprog(c, A_ub=A, b_ub=np.array(rhs), A_eq=Ae, b_eq=np.array(erhs) if ne else None,
                  bounds=list(zip(lb, ub)), method="highs")
    if verbose:
        print(f"  n={n} vars={nv} ineq={nr} hull-eq={ne} flat sets={nflat}  status={res.status} ({res.message[:40]})")
    return res

def mask_of(V0, names):
    return sum(1 << i for i, p in enumerate(V0) if p.name in names)

if __name__ == "__main__":
    a = 1.0
    print("== T_3 x R, tips at radius a=1, spine points Q+- at height +-H ==")
    for H in [0.2, 1/(2*math.sqrt(2)), 0.5, 1.0]:
        V0 = [Pt(i, a, 0.0, f"p{i}") for i in range(3)] + [Pt(None, 0, H, "Q+"), Pt(None, 0, -H, "Q-")]
        t = mask_of(V0, {"p0", "p1", "p2"})
        r = solve(V0, 3, t)
        print(f"  H={H:.4f}: max delta(tips) = {-r.fun:.6f}   chain formula 3*sqrt(H^2+1)-H = {3*math.hypot(H,1)-H:.6f}   (D*=8/3={8/3:.6f}, hub=3)")
