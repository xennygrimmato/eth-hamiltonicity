#!/usr/bin/env python3
"""Far-leg price-method value in products of Euclidean cones over metric graphs.

Generalises ../podprod.py. A factor is the Euclidean cone C(G) over a finite metric graph G
whose cycles all have length >= 2*pi (then G is CAT(1) and C(G) is CAT(0)).
  - pod with m arms           = cone over m isolated points (all angles pi)
  - plane                     = cone over a 2*pi-circle
  - m-pod x m-pod             = cone over K_{m,m} with edges pi/2 (spherical join)
  - A2-building-like complex  = cone over the incidence graph of a projective plane, edges pi/3
  - B2-building-like complex  = cone over the incidence graph of a generalised quadrangle, edges pi/4
Points of a factor: (vertex v of G or of a subdivision of G, radius r >= 0).
  d((r,x),(s,y))^2 = r^2 + s^2 - 2 r s cos(min(pi, d_G(x,y))).
Leg directions: points b of G; Busemann saving of a hub (r,x) for a leg to b is r*cos(min(pi,d_G(b,x))).
The two legs of an edge must be at angle >= pi (their union is a geodesic line through the apex).
Space: l2 product of J such cones. Objective as in podprod: b_k = sum_e s^k_e / delta_k.

Usage: coneprod.py CONFIG GRAPH J [restarts] [seed] [subdiv]
GRAPH: k33 | heawood | pg3 | gq22 | pods:M | circle:N | heawood+pods (disjoint union with 3 isolated points)
"""
import sys, itertools, math
import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, __file__.rsplit('/', 2)[0])
from podprod import config  # noqa: E402

PI = math.pi


def apsp(n, edges, length):
    D = np.full((n, n), np.inf)
    np.fill_diagonal(D, 0.0)
    for a, b in edges:
        D[a, b] = D[b, a] = min(D[a, b], length)
    for k in range(n):
        D = np.minimum(D, D[:, [k]] + D[[k], :])
    return D


def subdivide(n, edges, s):
    if s <= 1:
        return n, edges
    out = []
    for a, b in edges:
        prev = a
        for i in range(s - 1):
            out.append((prev, n))
            prev = n
            n += 1
        out.append((prev, b))
    return n, out


def pg(q):
    """incidence graph of PG(2,q), q prime: points and lines = normalised vectors of F_q^3."""
    pts = []
    for v in itertools.product(range(q), repeat=3):
        if any(v):
            f = next(x for x in v if x)
            inv = pow(f, q - 2, q)
            w = tuple((x * inv) % q for x in v)
            if w not in pts:
                pts.append(w)
    n = len(pts)
    edges = [(i, n + j) for i, P in enumerate(pts) for j, L in enumerate(pts)
             if sum(a * b for a, b in zip(P, L)) % q == 0]
    return 2 * n, edges


def gq22():
    """incidence graph of GQ(2,2): points = 2-subsets of {0..5}, lines = perfect matchings."""
    pts = list(itertools.combinations(range(6), 2))
    lines = []
    def rec(rest, cur):
        if not rest:
            lines.append(tuple(cur)); return
        a = rest[0]
        for b in rest[1:]:
            rec([x for x in rest if x not in (a, b)], cur + [(a, b)])
    rec(list(range(6)), [])
    edges = [(pts.index(pr), len(pts) + j) for j, L in enumerate(lines) for pr in L]
    return len(pts) + len(lines), edges


def graph(name, subdiv=1):
    extra = 0
    if name.endswith('+pods'):
        name = name[:-5]
        extra = 3
    if name == 'k33':
        n, edges, L = 6, [(i, 3 + j) for i in range(3) for j in range(3)], PI / 2
    elif name == 'k44':
        n, edges, L = 8, [(i, 4 + j) for i in range(4) for j in range(4)], PI / 2
    elif name == 'heawood':
        n, edges = pg(2); L = PI / 3
    elif name == 'pg3':
        n, edges = pg(3); L = PI / 3
    elif name == 'gq22':
        n, edges = gq22(); L = PI / 4
    elif name.startswith('pods:'):
        n, edges, L = int(name[5:]), [], PI
    elif name.startswith('circle:'):
        n = int(name[7:]); edges = [(i, (i + 1) % n) for i in range(n)]; L = 2 * PI / n
    else:
        raise ValueError(name)
    n, edges = subdivide(n, edges, subdiv)
    D = apsp(n + extra, edges, L / subdiv)
    return np.minimum(D, PI)


def value(vert, rho, D, p, E, groups, detail=False, mode='avg'):
    """vert: int (J,H) graph points of hubs; rho: float (J,H) radii."""
    J, H = vert.shape
    C = np.cos(D)
    opp = D >= PI - 1e-9
    delta = np.zeros(p)
    for k in range(p):
        best = 0.0
        for a, b in itertools.combinations(groups[k], 2):
            ra, rb = rho[:, a], rho[:, b]
            d2 = (ra - rb) ** 2 + 2 * ra * rb * (1.0 - C[vert[:, a], vert[:, b]])
            best = max(best, math.sqrt(max(float(np.sum(d2)), 0.0)))
        delta[k] = best
    if np.min(delta) < 1e-3 * max(1e-9, float(np.max(rho))):
        return (-1e9, None) if detail else -1e9
    lam = 1.0 / delta
    tot = 0.0
    bk = np.zeros(p)
    for (ha, hb) in E:
        cvec = np.zeros(J)
        svec = np.zeros((J, p))
        for j in range(J):
            # A[b,k] = saving of hub ha[k] for a leg towards b
            A = C[:, vert[j, ha]] * rho[j, ha]            # (n, p)
            B = C[:, vert[j, hb]] * rho[j, hb]
            a = A @ lam
            b = B @ lam
            M = np.where(opp, a[:, None] + b[None, :], -1e18)
            i1, i2 = np.unravel_index(int(np.argmax(M)), M.shape)
            cvec[j] = M[i1, i2]
            svec[j] = A[i1] + B[i2]
        pos = np.maximum(cvec, 0.0)
        nrm = math.sqrt(float(np.sum(pos * pos)))
        tot += nrm
        if nrm > 0:
            bk += lam * ((pos / nrm) @ svec)
    # objective: the balanced value min_k b_k (the average can be inflated by unbalanced placements)
    val = float(np.min(bk)) if mode == 'min' else tot / p
    if detail:
        return val, dict(bk=bk, delta=delta)
    return val


def optimise(name, gname, J, restarts=50, seed=0, subdiv=1, verbose=True):
    p, H, E, groups = config(name)
    D = graph(gname, subdiv)
    n = D.shape[0]
    rng = np.random.default_rng(seed)
    best = (-1e9, None, None)
    for it in range(restarts):
        vert = rng.integers(0, n, size=(J, H))
        rho = rng.random((J, H)) * (rng.random((J, H)) < 0.85)

        def f(x, vert=vert):
            return -value(vert, np.abs(x.reshape(J, H)), D, p, E, groups)
        cur = -f(rho.ravel())
        for sweep in range(8):
            res = minimize(f, rho.ravel(), method='Powell', options=dict(maxiter=3000, xtol=1e-6, ftol=1e-9))
            rho = np.abs(res.x.reshape(J, H))
            cur = -res.fun
            improved = False
            for j in range(J):
                for h in range(H):
                    old = vert[j, h]
                    for a in range(n):
                        if a == old:
                            continue
                        vert[j, h] = a
                        v = value(vert, rho, D, p, E, groups)
                        if v > cur + 1e-9:
                            cur, old, improved = v, a, True
                    vert[j, h] = old
            if not improved:
                break
        if cur > best[0] + 1e-9:
            best = (cur, vert.copy(), rho.copy())
            if verbose:
                print(f"restart {it}: {cur:.6f}", flush=True)
    return best, (p, H, E, groups, D)


if __name__ == '__main__':
    name, gname, J = sys.argv[1], sys.argv[2], int(sys.argv[3])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    subdiv = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    (v, vert, rho), (p, H, E, groups, D) = optimise(name, gname, J, restarts, seed, subdiv)
    nE = len(E)
    val, det = value(vert, rho, D, p, E, groups, detail=True)
    print(f"RESULT {name} {gname} J={J} subdiv={subdiv}: per merge {v:.6f}  rho={v/nE:.6f}  "
          f"(flat {1/math.sqrt(p):.4f}, cap {1/math.sqrt(2):.4f})  b_k={np.round(det['bk'],4)}")
    print("vert:\n", vert, "\nrho:\n", np.round(rho, 4))
