"""Loophole 1(a,b): GF(2) rank of crossing matrices over drawing families, for random cubic graphs.

For each graph we report, minimised by hill-climbing over each family:
  rank(C_D)            the plain crossing matrix (Q_D = x^T U_D x, polarisation C_D = U_D + U_D^T)
  rank*(C_D)           after the free modifications valid on 2-regular inputs: star moves
                       C += e (x) delta(v) + delta(v) (x) e   (v not on e; Q changes by x_e * sum_{f at v} x_f = 0
                       on valid x) and arbitrary entries on adjacent pairs (local ANDs), greedy.
Families: convex (vertex order), random points, 3x? grid, 2 lines, 3 lines, 2 concentric circles,
'tree' (a BFS spanning tree drawn crossing-free on a convex order by DFS order; chords arbitrary).
PASS conditions (sanity only): star moves preserve Q on all valid x of a test graph; rank* <= rank.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc2_lib import *  # noqa

rng = random.Random(99)


def convex_pts(order, n, R=10**6):
    # exact convex position: points on parabola y = x^2 (strictly convex), x = position
    return [(order[v] * 1000 + 1, (order[v] * 1000 + 1) ** 2) for v in range(n)]


def cross_rows(P, edges):
    return mat_to_rows(crossing_matrix(P, edges))


def rank_of(P, edges):
    return gf2_rank(cross_rows(P, edges))


def star_reduce(rows, edges, n, iters, rng):
    m = len(edges)
    inc = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        inc[i].append(k); inc[j].append(k)
    adjmask = [0] * m
    for k, (i, j) in enumerate(edges):
        for l in inc[i] + inc[j]:
            adjmask[k] |= 1 << l
    rows = rows[:]
    best = gf2_rank(rows)
    moves = [(v, e) for v in range(n) for e in range(m) if v not in edges[e]]
    for it in range(iters):
        if rng.random() < 0.7:
            v, e = rng.choice(moves)
            star = sum(1 << f for f in inc[v])
            new = rows[:]
            new[e] ^= star
            for f in inc[v]:
                new[f] ^= 1 << e
        else:  # flip a free adjacent entry (symmetric)
            e = rng.randrange(m); cand = [f for f in range(m) if (adjmask[e] >> f) & 1 and f != e]
            f = rng.choice(cand); new = rows[:]
            new[e] ^= 1 << f; new[f] ^= 1 << e
        r = gf2_rank(new)
        if r <= best:
            rows, best = new, r
    return best


def hill(gen, mutate, edges, n, iters):
    P = gen(); best = rank_of(P, edges)
    for it in range(iters):
        Q = mutate(P)
        if Q is None: continue
        r = rank_of(Q, edges)
        if r <= best:
            P, best = Q, r
    return best, P


def generic_ok(P, edges):
    n = len(P)
    if len(set(p[0] for p in P)) < n: return False
    for a, b, c in itertools.combinations(range(n), 3):
        if orient(P[a], P[b], P[c]) == 0: return False
    return True


def families(n, edges):
    F = {}
    # convex: order
    def g_conv():
        o = list(range(n)); rng.shuffle(o); return o
    def m_conv(o):
        o = o[:]; i, j = rng.sample(range(n), 2); o[i], o[j] = o[j], o[i]; return o
    F['convex'] = (lambda: g_conv(), m_conv, lambda o: convex_pts(o, n))
    def lines(k):
        def gen():
            return [(rng.randrange(10**4) * 7 + v, (v % k) * 1000 + (rng.randrange(1, 50) if k == 1 else 0)) for v in range(n)]
        return gen
    for k in (2, 3):
        # vertices on k parallel lines y = 0, 1000, ...: points on a line are collinear, so put the
        # lines as very flat convex curves (y = line*H + eps*x^2) to stay in general position
        def gen(k=k):
            xs = rng.sample(range(1, 4 * n + 1), n)
            return [(xs[v], (v % k) * 10**7 + xs[v] ** 2 * (1 if (v % k) % 2 == 0 else -1)) for v in range(n)]
        def mut(P, k=k):
            P = P[:]; v = rng.randrange(n); xs = set(p[0] for p in P)
            x = rng.randrange(1, 4 * n + 1)
            if x in xs: return None
            lay = rng.randrange(k)
            P[v] = (x, lay * 10**7 + x * x * (1 if lay % 2 == 0 else -1)); return P
        F[f'{k}lines'] = (gen, mut, None)
    def g_rand():
        return generic_drawing(n, rng, R=50)
    def m_rand(P):
        P = P[:]; v = rng.randrange(n); P[v] = (rng.randrange(-50, 50), rng.randrange(-50, 50))
        return P if generic_ok(P, edges) else None
    F['random'] = (g_rand, m_rand, None)
    def g_grid():
        while True:
            P = [(rng.randrange(6) * 10 + rng.randrange(3), rng.randrange(6) * 10 + rng.randrange(3)) for v in range(n)]
            if generic_ok(P, edges): return P
    def m_grid(P):
        P = P[:]; v = rng.randrange(n); P[v] = (rng.randrange(6) * 10 + rng.randrange(3), rng.randrange(6) * 10 + rng.randrange(3))
        return P if generic_ok(P, edges) else None
    F['grid'] = (g_grid, m_grid, None)
    def g_circ():
        # two concentric "circles": convex polygons approximated by integer points on two parabolas
        return [((v * 37 % 101) + 1, ((v * 37 % 101) + 1) ** 2 + (10**6 if v % 2 else 0)) for v in range(n)]
    def m_circ(P):
        P = P[:]; v = rng.randrange(n); x = rng.randrange(1, 200)
        if x in set(p[0] for p in P): return None
        P[v] = (x, x * x + (10**6 if rng.random() < 0.5 else 0)); return P
    F['2parab'] = (g_circ, m_circ, None)
    return F


def tree_order(n, edges):
    adj = [[] for _ in range(n)]
    for i, j in edges:
        adj[i].append(j); adj[j].append(i)
    seen = [0] * n; order = []
    def dfs(v):
        seen[v] = 1; order.append(v)
        for w in adj[v]:
            if not seen[w]: dfs(w)
    dfs(0)
    for v in range(n):
        if not seen[v]: dfs(v)
    pos = {v: i for i, v in enumerate(order)}
    return [pos[v] for v in range(n)]


fails = 0
# sanity: star moves keep Q on valid x
n = 7; edges = random_graph(n, 12, rng, min_deg2=True)
P = generic_drawing(n, rng, edges=edges); C = crossing_matrix(P, edges)
labs = valid_labellings(n, edges, 0)
for (v, e) in [(v, e) for v in range(n) for e in range(len(edges)) if v not in edges[e]][:20]:
    C2 = [row[:] for row in C]
    for f, (a, b) in enumerate(edges):
        if v in (a, b):
            C2[e][f] ^= 1; C2[f][e] ^= 1
    for lab in labs:
        mix = mixed_edges(edges, lab)
        if mixed_cross_parity(C, edges, mix) != mixed_cross_parity(C2, edges, mix): fails += 1
print('star-move sanity:', 'PASS' if fails == 0 else 'FAIL')

print('n  m  | ' + ' | '.join(f'{k:>8s}' for k in ['convex', '2lines', '3lines', 'random', 'grid', '2parab', 'DFS-cvx']) + ' | rank*(best) | m/2')
for n in (8, 12, 16, 24, 32, 48):
    for rep in range(2 if n <= 24 else 1):
        edges = random_regular(n, 3, rng); m = len(edges)
        F = families(n, edges); res = {}; bestP = None; bestr = 10**9
        it = 300 if n <= 24 else 120
        for name, (gen, mut, tr) in F.items():
            if tr is not None:
                b, o = hill(lambda: gen(), mut, edges, n, 0) if False else (None, None)
                # convex: hill on orders
                o = gen(); r = rank_of(tr(o), edges)
                for _ in range(it):
                    o2 = mut(o); r2 = rank_of(tr(o2), edges)
                    if r2 <= r: o, r = o2, r2
                res[name] = r; P = tr(o)
            else:
                r, P = hill(gen, mut, edges, n, it); res[name] = r
            if res[name] < bestr: bestr, bestP = res[name], P
        o = tree_order(n, edges); res['DFS-cvx'] = rank_of(convex_pts(o, n), edges)
        rs = star_reduce(cross_rows(bestP, edges), edges, n, 400 if n <= 24 else 150, rng)
        if rs > bestr: fails += 1
        print(f'{n:2d} {m:3d} | ' + ' | '.join(f'{res[k]:8d}' for k in ['convex', '2lines', '3lines', 'random', 'grid', '2parab', 'DFS-cvx']) + f' | {rs:11d} | {m//2}', flush=True)
print('ALL PASS' if fails == 0 else 'SOME FAIL')
