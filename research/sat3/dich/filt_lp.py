"""Label-calculus LP in the filtration space C_N(2) (real filtrations of F_2^N; q1-notes section 1), N = 3, 4.

Points are filtrations, given as (basis, level vector).  Flat sets = subsets with a common adapted basis; their
label rate is the mean width of the level vectors (EG Thm 5.3).  Other constraints as in label_lp.py:
monotone, submodular on intersecting sets (EG Prop. 5.2), and (optional, sound but incomplete) hull invariance.
"""
import itertools, math, sys, time
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
from scipy.spatial import ConvexHull

def span(vs):
    S = {0}
    for v in vs:
        if v not in S: S |= {s ^ v for s in S}
    return frozenset(S)
def dim(S): return len(S).bit_length() - 1

class Space:
    def __init__(self, N):
        self.N = N
        self.V = frozenset(range(1 << N))
        self.bases = [b for b in itertools.combinations(range(1, 1 << N), N) if len(span(b)) == 1 << N]
    def filt(self, basis, levels):
        """canonical filtration: tuple of (level, subspace), levels decreasing"""
        lv = sorted(set(round(float(x), 12) for x in levels), reverse=True)
        return tuple((s, span([f for f, x in zip(basis, levels) if x >= s - 1e-12])) for s in lv)
    def coords(self, F, b):
        """level vector of F in basis b, or None if b is not adapted"""
        for s, A in F:
            if sum(1 for f in b if f in A) != dim(A): return None
        return tuple(max(s for s, A in F if f in A) for f in b)
    def dist(self, F, G):
        d2 = 0.0; pA = frozenset({0})
        for a, A in F:
            pB = frozenset({0})
            for b, B in G:
                m = dim(A & B) - dim(pA & B) - dim(A & pB) + dim(pA & pB)
                if m: d2 += m * (a - b) ** 2
                pB = B
            pA = A
        return math.sqrt(d2)

def mean_width(P):
    """mean width (segment = its length) of a finite point set in R^d, d <= 3, by the edge formula"""
    P = np.unique(np.round(np.asarray(P, float), 10), axis=0)
    if len(P) == 1: return 0.0
    Q = P - P.mean(0)
    u, s, vt = np.linalg.svd(Q, full_matrices=False)
    r = int((s > 1e-8).sum())
    if r == 1:
        t = Q @ vt[0]; return float(t.max() - t.min())
    if r == 2:
        X = Q @ vt[:2].T
        h = ConvexHull(X); v = X[h.vertices]
        return 0.5 * float(sum(np.linalg.norm(v[i] - v[(i+1) % len(v)]) for i in range(len(v))))
    X = Q @ vt[:3].T
    h = ConvexHull(X)
    # merge coplanar facets: accumulate exterior angles over ridges
    edges = {}
    for simplex, eq in zip(h.simplices, h.equations):
        for i in range(3):
            e = tuple(sorted((simplex[i], simplex[(i+1) % 3])))
            edges.setdefault(e, []).append(eq[:3])
    tot = 0.0
    for (i, j), ns in edges.items():
        c = max(-1.0, min(1.0, float(np.dot(ns[0], ns[1]))))
        tot += np.linalg.norm(X[i] - X[j]) * math.acos(c)
    return tot / (2 * math.pi)

def in_conv(z, T):
    T = np.asarray(T, float); z = np.asarray(z, float)
    m = len(T)
    res = linprog(np.zeros(m), A_eq=np.vstack([T.T, np.ones(m)]), b_eq=np.append(z, 1.0), bounds=[(0, None)] * m,
                  method="highs")
    return res.status == 0

def solve(sp, pts, target_idx, sense="max", hull=False, tripod=False, verbose=True):
    n = len(pts); full = (1 << n) - 1
    co = [[sp.coords(F, b) for F in pts] for b in sp.bases]
    amask = [sum(1 << i for i in range(n) if c[i] is not None) for c in co]
    amask_set = sorted(set(amask), key=lambda m: -bin(m).count("1"))
    def flat_basis(m):
        for bi, am in enumerate(amask):
            if m & ~am == 0: return bi
        return None
    lb = np.zeros(full); ub = np.full(full, np.inf); nflat = 0
    wcache = {}
    for m in range(1, full + 1):
        if m & (m - 1) == 0: ub[m-1] = 0.0; continue
        bi = flat_basis(m)
        if bi is not None:
            w = mean_width([co[bi][i] for i in range(n) if m >> i & 1]); lb[m-1] = ub[m-1] = w; nflat += 1
        elif tripod and bin(m).count("1") == 3:
            i, j, k = [i for i in range(n) if m >> i & 1]
            d = [sp.dist(pts[i], pts[j]), sp.dist(pts[i], pts[k]), sp.dist(pts[j], pts[k])]
            a = [(d[0]+d[1]-d[2])/2, (d[0]+d[2]-d[1])/2, (d[1]+d[2]-d[0])/2]
            lb[m-1] = sum(a) - (1 / sum(1 / x for x in a) if min(a) > 1e-12 else 0.0)
    def closure(m):
        cl = m; changed = True
        while changed:
            changed = False
            for bi, am in enumerate(amask):
                T = cl & am
                if bin(T).count("1") < 2: continue
                for z in range(n):
                    if (am >> z & 1) and not (cl >> z & 1):
                        if in_conv(co[bi][z], [co[bi][i] for i in range(n) if T >> i & 1]):
                            cl |= 1 << z; changed = True
        return cl
    rows, cols, vals = [], [], []; nr = 0; nh = 0
    erow, ecol, evals = [], [], []; ne = 0
    for m in range(1, full + 1):
        out = [i for i in range(n) if not m >> i & 1]
        cl = closure(m) if (hull and m & (m - 1)) else m
        for x in out:
            mx = m | 1 << x
            if cl >> x & 1:
                erow += [ne, ne]; ecol += [mx-1, m-1]; evals += [1.0, -1.0]; ne += 1; nh += 1
            else:
                rows += [nr, nr]; cols += [m-1, mx-1]; vals += [1.0, -1.0]; nr += 1
        for x, y in itertools.combinations(out, 2):
            mx, my = m | 1 << x, m | 1 << y
            rows += [nr] * 4; cols += [(mx | my) - 1, m - 1, mx - 1, my - 1]; vals += [1.0, 1.0, -1.0, -1.0]; nr += 1
    A = coo_matrix((vals, (rows, cols)), shape=(nr, full)).tocsr()
    Ae = coo_matrix((evals, (erow, ecol)), shape=(ne, full)).tocsr() if ne else None
    c = np.zeros(full); c[target_idx - 1] = -1.0 if sense == "max" else 1.0
    res = linprog(c, A_ub=A, b_ub=np.zeros(nr), A_eq=Ae, b_eq=np.zeros(ne) if ne else None,
                  bounds=list(zip(lb, ub)), method="highs")
    val = None if res.status != 0 else (-res.fun if sense == "max" else res.fun)
    if verbose: print(f"    n={n} flat={nflat} hull-eq={nh} status={res.status}", flush=True)
    return val
