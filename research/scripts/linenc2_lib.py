"""Helpers for research/linear-encoding-2.md (drawings, ranks, surfaces, gap gadgets).
Exact integer / GF(2) / GF(3) arithmetic only."""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc_lib import *  # noqa


def orient(p, q, r):
    v = (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])
    return (v > 0) - (v < 0)


def seg_cross(p1, p2, p3, p4):
    """proper crossing of segments with 4 distinct endpoints (general position assumed)."""
    return (orient(p1, p2, p3) * orient(p1, p2, p4) < 0) and (orient(p3, p4, p1) * orient(p3, p4, p2) < 0)


def generic_drawing(n, rng, R=60, edges=None):
    """integer points: distinct x (no vertical edge), no three collinear, and (if edges given)
    no three edges through one interior point."""
    while True:
        xs = rng.sample(range(-R, R), n)
        P = [(xs[i], rng.randrange(-R, R)) for i in range(n)]
        if any(orient(P[a], P[b], P[c]) == 0 for a, b, c in itertools.combinations(range(n), 3)):
            continue
        if edges is not None and not concurrency_free(P, edges):
            continue
        return P


def crossing_point(p1, p2, p3, p4):
    # intersection as exact rational (num_x, num_y, den)
    x1, y1 = p1; x2, y2 = p2; x3, y3 = p3; x4, y4 = p4
    den = (x1-x2)*(y3-y4) - (y1-y2)*(x3-x4)
    a = x1*y2 - y1*x2; b = x3*y4 - y3*x4
    nx = a*(x3-x4) - (x1-x2)*b; ny = a*(y3-y4) - (y1-y2)*b
    if den < 0:
        den, nx, ny = -den, -nx, -ny
    from math import gcd
    g = gcd(gcd(abs(nx), abs(ny)), den)
    return (nx//g, ny//g, den//g)


def concurrency_free(P, edges):
    pts = {}
    for k, l in itertools.combinations(range(len(edges)), 2):
        (a, b), (c, d) = edges[k], edges[l]
        if len({a, b, c, d}) == 4 and seg_cross(P[a], P[b], P[c], P[d]):
            q = crossing_point(P[a], P[b], P[c], P[d])
            if q in pts:
                return False
            pts[q] = 1
    return True


def crossing_matrix(P, edges):
    m = len(edges)
    C = [[0]*m for _ in range(m)]
    for k, l in itertools.combinations(range(m), 2):
        (a, b), (c, d) = edges[k], edges[l]
        if len({a, b, c, d}) == 4 and seg_cross(P[a], P[b], P[c], P[d]):
            C[k][l] = C[l][k] = 1
    return C


def north_bit(P, u, v, w):
    """1 iff the turn (u->v then v->w), taken the short way (|angle|<pi), passes through the
    direction 'north' (0,1).  Needs no vertical edges and u,v,w not collinear."""
    x1 = P[v][0]-P[u][0]; y1 = P[v][1]-P[u][1]
    x2 = P[w][0]-P[v][0]; y2 = P[w][1]-P[v][1]
    cr = x1*y2 - y1*x2
    assert cr != 0 and x1 != 0 and x2 != 0
    return int((cr > 0 and x1 > 0 and x2 < 0) or (cr < 0 and x1 < 0 and x2 > 0))


def north_sum(P, arc_list):
    pred = {b: a for a, b in arc_list}
    succ = dict(arc_list)
    return sum(north_bit(P, pred[v], v, succ[v]) for v in succ) & 1


def mixed_cross_parity(C, edges, mixed_idx):
    t = 0
    for k, l in itertools.combinations(mixed_idx, 2):
        t += C[k][l]
    return t & 1


# ---------------- GF(2) linear algebra on int bitmasks ----------------
def gf2_rank(rows):
    rows = [r for r in rows if r]
    basis = {}
    for r in rows:
        while r:
            h = r.bit_length() - 1
            if h in basis:
                r ^= basis[h]
            else:
                basis[h] = r
                break
    return len(basis)


def mat_to_rows(C):
    return [sum(1 << j for j, x in enumerate(row) if x) for row in C]


def gf2_solve(rows, rhs):
    """rows: list of int bitmasks (equations), rhs: list of bits. Return a solution bitmask or None."""
    piv = []  # (pivot bit, row, rhs)
    for r, b in zip(rows, rhs):
        for (h, pr, pb) in piv:
            if (r >> h) & 1:
                r ^= pr; b ^= pb
        if r == 0:
            if b:
                return None
            continue
        h = r.bit_length() - 1
        # reduce existing pivots
        new = []
        for (h2, pr, pb) in piv:
            if (pr >> h) & 1:
                pr ^= r; pb ^= b
            new.append((h2, pr, pb))
        piv = new + [(h, r, b)]
    sol = 0
    for (h, pr, pb) in piv:
        if pb:
            sol |= 1 << h
    return sol


# ---------------- cycles ----------------
def directed_simple_cycles(n, edges):
    """all directed simple cycles (length >= 3) as vertex lists, each cyclic rotation once
    (start at min vertex), both orientations."""
    adj = [[] for _ in range(n)]
    for i, j in edges:
        adj[i].append(j); adj[j].append(i)
    out = []
    def dfs(s, v, path, seen):
        for w in adj[v]:
            if w == s and len(path) >= 3:
                out.append(list(path))
            elif w > s and not (seen >> w) & 1:
                path.append(w); dfs(s, w, path, seen | (1 << w)); path.pop()
    for s in range(n):
        dfs(s, s, [s], 1 << s)
    return out


def eid_map(edges):
    return {frozenset(e): k for k, e in enumerate(edges)}


def random_regular(n, d, rng):
    while True:
        pts = [v for v in range(n) for _ in range(d)]
        rng.shuffle(pts)
        E = set(); ok = True
        for a, b in zip(pts[::2], pts[1::2]):
            if a == b or (min(a, b), max(a, b)) in E:
                ok = False; break
            E.add((min(a, b), max(a, b)))
        if ok:
            return sorted(E)


# ---------------- turns and local certificates ----------------
def turn_index(n, edges):
    """index of each turn (v, e_in, e_out), e_in != e_out edges at v (edge indices)."""
    inc = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        inc[i].append(k); inc[j].append(k)
    T = {}
    for v in range(n):
        for a in inc[v]:
            for b in inc[v]:
                if a != b:
                    T[(v, a, b)] = len(T)
    return T


def cycle_turns(cyc, E, T):
    L = len(cyc)
    out = []
    for t in range(L):
        u, v, w = cyc[t-1], cyc[t], cyc[(t+1) % L]
        out.append(T[(v, E[frozenset((u, v))], E[frozenset((v, w))])])
    return out


def local_gf2_certificate(n, edges, avoid=None):
    """Is there f: turns -> GF(2) with sum over every directed simple cycle == 1 ?"""
    E = eid_map(edges); T = turn_index(n, edges)
    rows, rhs = [], []
    for cyc in directed_simple_cycles(n, edges):
        if avoid is not None and avoid in cyc:
            continue
        rows.append(sum(1 << t for t in cycle_turns(cyc, E, T))); rhs.append(1)
    return gf2_solve(rows, rhs) is not None


def nowhere_zero_Zp(n, edges, p=3, limit=2*10**6, rng=None):
    """Search t: turns -> Z/p with sum over every directed simple cycle != 0 (mod p).
    Returns (status, t) with status 'found' / 'none' (exhausted) / 'limit'."""
    E = eid_map(edges); T = turn_index(n, edges)
    cons = [cycle_turns(c, E, T) for c in directed_simple_cycles(n, edges)]
    nv = len(T)
    occ = [[] for _ in range(nv)]
    for ci, c in enumerate(cons):
        for t in c:
            occ[t].append(ci)
    order = sorted(range(nv), key=lambda t: -len(occ[t]))
    val = [None]*nv
    unas = [len(c) for c in cons]; ssum = [0]*len(cons)
    nodes = [0]
    def rec(k):
        nodes[0] += 1
        if nodes[0] > limit:
            raise TimeoutError
        if k == nv:
            return True
        t = order[k]
        vals = list(range(p))
        if rng: rng.shuffle(vals)
        for a in vals:
            ok = True
            for ci in occ[t]:
                if unas[ci] == 1 and (ssum[ci] + a) % p == 0:
                    ok = False; break
            if not ok:
                continue
            val[t] = a
            for ci in occ[t]:
                unas[ci] -= 1; ssum[ci] += a
            if rec(k+1):
                return True
            for ci in occ[t]:
                unas[ci] += 1; ssum[ci] -= a
            val[t] = None
        return False
    try:
        r = rec(0)
    except TimeoutError:
        return 'limit', None, T, cons
    return ('found' if r else 'none'), val, T, cons


def nz_local_search(nv, cons, p=3, rng=None, max_flips=200000, restarts=20, init=None):
    """min-conflicts search for t in (Z/p)^nv with sum(t[c]) != 0 mod p for every c in cons
    (a cons entry is a list of turn indices, repetitions allowed)."""
    rng = rng or random.Random(1)
    occ = [[] for _ in range(nv)]
    for ci, c in enumerate(cons):
        for t in c:
            occ[t].append(ci)
    best = None
    for rs in range(restarts):
        val = list(init) if (init is not None and rs == 0) else [rng.randrange(p) for _ in range(nv)]
        ssum = [sum(val[t] for t in c) % p for c in cons]
        bad = set(i for i, s in enumerate(ssum) if s == 0)
        for it in range(max_flips):
            if not bad:
                return val
            ci = rng.choice(tuple(bad))
            # choose turn in this constraint and new value minimising #bad
            bestd, cand = None, []
            for t in set(cons[ci]):
                for a in range(p):
                    if a == val[t]:
                        continue
                    d = a - val[t]
                    delta = 0
                    for cj in occ[t]:
                        s_old = ssum[cj]
                        mult = cons[cj].count(t) if len(cons[cj]) < 0 else 1
                        s_new = (s_old + d*mult) % p
                        delta += (s_new == 0) - (s_old == 0)
                    if bestd is None or delta < bestd:
                        bestd, cand = delta, [(t, a)]
                    elif delta == bestd:
                        cand.append((t, a))
            if bestd > 0 and rng.random() < 0.3:
                t = rng.choice(cons[ci]); a = (val[t] + rng.randrange(1, p)) % p
            else:
                t, a = rng.choice(cand)
            d = a - val[t]; val[t] = a
            for cj in occ[t]:
                ssum[cj] = (ssum[cj] + d) % p
                if ssum[cj] == 0: bad.add(cj)
                else: bad.discard(cj)
        if best is None or len(bad) < best[0]:
            best = (len(bad), val)
    return None
