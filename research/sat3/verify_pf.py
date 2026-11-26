"""Independent slow evaluator for the piece-floor objective (spec S3, research/ports/c1d1/notes.md).

Plain Python, no tensorlab: rebuilds the designs from their definitions, recomputes ranks over F_2 by
Gaussian elimination on lists, and recomputes b_m = (L - H_m)/delta_m and value = sum_m b_m^+ / p for
every JSON configuration given on the command line (written by examples/piecefloor.rs).

usage: python3 verify_pf.py research/sat3/data/*.json
"""
import json, math, sys


def design(name):
    if name.startswith('crossing'):
        w = {'crossing': (1, 1), 'crossing-half': (1, .5), 'crossing-tenth': (1, .1)}[name]
        # nodes x,y,u,v = 0..3 ; wires x-v, y-u ; rows {x,y}|{u,v} ; cols {x,u}|{y,v}
        return dict(edges=[(0, 3), (1, 2)], w=list(w), groups=[[0, 0, 1, 1], [0, 1, 0, 1]])
    if name == 'K4':
        edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]
        f = [lambda v: v >> 1, lambda v: v & 1, lambda v: (v >> 1) ^ (v & 1)]
        return dict(edges=edges, w=[1] * 6, groups=[[f[k](v) for v in range(4)] for k in range(3)])
    if name.startswith('Delta3'):
        nodes = [(r, c) for r in range(3) for c in range(3)]
        edges = [(i, j) for i in range(9) for j in range(i + 1, 9)
                 if sum(nodes[i]) % 3 == sum(nodes[j]) % 3]
        mf = [lambda v: v[0], lambda v: v[1], lambda v: (v[0] - v[1]) % 3]
        p = 2 if name == 'Delta3-2merge' else 3
        return dict(edges=edges, w=[1] * 9, groups=[[mf[k](v) for v in nodes] for k in range(p)])
    raise ValueError(name)


def rank_f2(rows):
    rows = [list(r) for r in rows]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                rows[i] = [a ^ b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def parse_mat(s):
    return [[int(ch) for ch in row] for row in s.split('/')]


def mat_dist(a, b):
    return math.sqrt(rank_f2([[x ^ y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]))


def model_dist(p, q):
    s = 0.0
    for a1, t1, a2, t2 in zip(p['arm'], p['t'], q['arm'], q['t']):
        d = abs(t1 - t2) if a1 == a2 else t1 + t2
        s += d * d
    s += sum((x - y) ** 2 for x, y in zip(p['x'], q['x']))
    return math.sqrt(s)


def bvec(des, pts, dist):
    E = len(des['edges'])
    nl = 2 * E
    hub = {}
    o = nl
    for m, g in enumerate(des['groups']):
        for k in range(max(g) + 1):
            hub[(m, k)] = o
            o += 1
    assert o == len(pts), (o, len(pts))
    L = sum(w * dist(pts[2 * e], pts[2 * e + 1]) for e, w in enumerate(des['w']))
    b = []
    for m, g in enumerate(des['groups']):
        H = 0.0
        for e, (u, v) in enumerate(des['edges']):
            H += des['w'][e] * (dist(pts[2 * e], pts[hub[(m, g[u])]]) + dist(pts[2 * e + 1], pts[hub[(m, g[v])]]))
        r = max(g) + 1
        dm = max(dist(pts[hub[(m, i)]], pts[hub[(m, j)]]) for i in range(r) for j in range(i + 1, r))
        b.append(0.0 if dm < 1e-12 else (L - H) / dm)
    return b


def check(path):
    J = json.load(open(path))
    des = design(J['design'])
    if J['space'] == 'mat':
        pts = [parse_mat(s) for s in J['points']]
        dist = mat_dist
    else:
        pts = J['points']
        dist = model_dist
    b = bvec(des, pts, dist)
    val = sum(max(0, x) for x in b) / len(b)
    ok = abs(val - J['value']) < 1e-6
    print('%-60s value(py) = %.6f  value(rust) = %.6f  b = %s  %s' % (
        path.split('/')[-1], val, J['value'], [round(x, 6) for x in b], 'OK' if ok else 'MISMATCH'))
    return ok


if __name__ == '__main__':
    allok = all([check(p) for p in sys.argv[1:]])
    print('ALL OK' if allok else 'SOME MISMATCH')


def far_to_finite(J, M):
    """Build an explicit finite configuration from a far-leg JSON (hubs + merge subset S): every edge's legs
    are put at distance M along the optimal geodesic line (recomputed here from scratch)."""
    des = design(J['design'])
    arms, k, hubs = J['arms'], J['k'], J['hubs']
    E = len(des['edges']); p = len(des['groups']); S = [m for m in range(p) if (J['S'] >> m) & 1]
    off = []; o = 0
    for g in des['groups']:
        off.append(o); o += max(g) + 1
    H = lambda m, g: hubs[off[m] + g]
    inv = []
    for m, g in enumerate(des['groups']):
        r = max(g) + 1
        dm = max(model_dist(H(m, i), H(m, j)) for i in range(r) for j in range(i + 1, r))
        inv.append(1 / dm)
    legs = []
    for e, (u, v) in enumerate(des['edges']):
        coef, choice = [], []
        for f, na in enumerate(arms):
            best = (-1e18, None)
            for a in range(na):
                for a2 in range(na):
                    if a == a2: continue
                    z = 0
                    for m in S:
                        hu, hv = H(m, des['groups'][m][u]), H(m, des['groups'][m][v])
                        z += inv[m] * ((hu['t'][f] if hu['arm'][f] == a else -hu['t'][f]) + (hv['t'][f] if hv['arm'][f] == a2 else -hv['t'][f]))
                    if z > best[0]: best = (z, (a, a2))
            coef.append(max(best[0], 0)); choice.append(best[1])
        B = [sum(inv[m] * (H(m, des['groups'][m][u])['x'][c] - H(m, des['groups'][m][v])['x'][c]) for m in S) for c in range(k)]
        nrm = math.sqrt(sum(x * x for x in coef) + sum(x * x for x in B))
        lu = {'arm': [ch[0] for ch in choice], 't': [M * x / nrm for x in coef], 'x': [M * x / nrm for x in B]}
        lv = {'arm': [ch[1] for ch in choice], 't': [M * x / nrm for x in coef], 'x': [-M * x / nrm for x in B]}
        legs += [lu, lv]
    return des, legs + hubs


def check_far(path, Ms=(1e2, 1e4, 1e6)):
    J = json.load(open(path))
    for M in Ms:
        des, pts = far_to_finite(J, M)
        b = bvec(des, pts, model_dist)
        val = sum(max(0, x) for x in b) / len(b)
        print('%-50s M=%g  value(py, finite) = %.6f  far value(rust) = %.6f  b = %s' % (path.split('/')[-1], M, val, J['value'], [round(x, 6) for x in b]))
    return abs(val - J['value']) < 1e-4


def ag_design(q, p):
    """AG(2,q) with all edges and the first p parallel classes (same conventions as Design::ag)."""
    T4 = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
    add = (lambda a, b: a ^ b) if q == 4 else (lambda a, b: (a + b) % q)
    mul = (lambda a, b: T4[a][b]) if q == 4 else (lambda a, b: (a * b) % q)
    def f(s, v):
        x, y = divmod(v, q)
        return x if s == 0 else y if s == 1 else add(y, mul(s - 1, x))
    edges = [(i, j) for i in range(q * q) for j in range(i + 1, q * q)]
    return dict(edges=edges, w=[1] * len(edges), groups=[[f(s, v) for v in range(q * q)] for s in range(p)])


def check_onetree(path):
    """Recompute Gamma = sum_e s_e^2 / Dbar for a one-tree JSON from scratch (tree distances by DFS,
    savings by brute force over ray-root pairs)."""
    J = json.load(open(path))
    name = J['design']
    if name.startswith('AG2-'):
        _, q, p = name.split('-'); des = ag_design(int(q), int(p[1:]))
    else:
        des = design(name)
    par, ln, hv = J['parent'], J['len'], J['hv']
    n = len(par)
    adj = [[] for _ in range(n)]
    for v in range(1, n):
        adj[v].append((par[v], ln[v])); adj[par[v]].append((v, ln[v]))
    D = [[0.0] * n for _ in range(n)]
    for s in range(n):
        st = [(s, 0.0)]; seen = {s}
        while st:
            v, d = st.pop(); D[s][v] = d
            for w, l in adj[v]:
                if w not in seen: seen.add(w); st.append((w, d + l))
    off = []; o = 0
    for g in des['groups']:
        off.append(o); o += max(g) + 1
    H = lambda m, g: hv[off[m] + g]
    p = len(des['groups'])
    S = 0.0
    for (u, v) in des['edges']:
        best = 0.0
        for a in range(n):
            for b in range(n):
                z = sum(D[a][b] - D[a][H(m, g[u])] - D[b][H(m, g[v])] for m, g in enumerate(des['groups']))
                best = max(best, z)
        S += best * best
    Db = 0.0
    for m, g in enumerate(des['groups']):
        r = max(g) + 1
        prs = [(i, j) for i in range(r) for j in range(i + 1, r)]
        Db += sum(D[H(m, i)][H(m, j)] ** 2 for i, j in prs) / len(prs)
    Db /= p
    G = S / Db
    print('%-50s Gamma(py) = %.6f  Gamma(rust) = %.6f  CS value = %.6f  %s' % (path.split('/')[-1], G, J['gamma'],
          math.sqrt(len(des['edges']) * G) / p, 'OK' if abs(G - J['gamma']) < 1e-6 * max(1, G) else 'MISMATCH'))


def check_cone(path):
    """Recompute Gamma (design) or Phi (limit:Q:p) of a one-cone-factor JSON from scratch: graph distances by
    Floyd-Warshall on the saved (subdivided) edge list, d = min(pi, d_G), savings by brute force over pairs of
    directions at angle >= pi."""
    J = json.load(open(path))
    n = J['graph']['n']; INF = float('inf'); PI = math.pi
    D = [[0.0 if i == j else INF for j in range(n)] for i in range(n)]
    for a, b, l in J['graph']['edges']:
        D[a][b] = D[b][a] = min(D[a][b], l)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if D[i][k] + D[k][j] < D[i][j]: D[i][j] = D[i][k] + D[k][j]
    D = [[min(PI, x) for x in row] for row in D]
    hv, r = J['hv'], J['r']
    d2 = lambda a, b: max(0.0, r[a] ** 2 + r[b] ** 2 - 2 * r[a] * r[b] * math.cos(D[hv[a]][hv[b]]))
    gain = lambda hs, b: sum(r[h] * math.cos(D[hv[h]][b]) for h in hs)
    def sav(hu, hw):
        best = 0.0
        fu = [gain(hu, b) for b in range(n)]; fw = [gain(hw, b) for b in range(n)]
        for b in range(n):
            for c in range(n):
                if D[b][c] >= PI - 1e-9: best = max(best, fu[b] + fw[c])
        return best
    t = J['target']
    if t.startswith('limit:'):
        _, q, p = t.split(':'); p = int(p)
        assert 'x' not in q, 'cyclic Q only in this checker'
        m = int(q); funcs = [(1, 0), (0, 1), (1, -1), (1, 1)][:p]
        nodes = [[k * m + (a * x + b * y) % m for k, (a, b) in enumerate(funcs)] for x in range(m) for y in range(m)]
        Db = sum(d2(k * m + a, k * m + b) for k in range(p) for a in range(m) for b in range(m)) / (p * m * m)
        S = sum(sav(u, w) ** 2 for u in nodes for w in nodes) / len(nodes) ** 2
        val = S / Db; lab = 'Phi'
    else:
        des = design({'delta3': 'Delta3', 'crossing': 'crossing', 'k4': 'K4'}[t])
        off = []; o = 0
        for g in des['groups']:
            off.append(o); o += max(g) + 1
        hs = lambda u: [off[m] + g[u] for m, g in enumerate(des['groups'])]
        S = sum(sav(hs(u), hs(v)) ** 2 for (u, v) in des['edges'])
        p = len(des['groups'])
        Db = 0.0
        for m, g in enumerate(des['groups']):
            R = max(g) + 1; prs = [(i, j) for i in range(R) for j in range(i + 1, R)]
            Db += sum(d2(off[m] + i, off[m] + j) for i, j in prs) / len(prs)
        val = S / (Db / p); lab = 'Gamma'
    print('%-55s %s(py) = %.6f  score(rust) = %.6f  %s' % (path.split('/')[-1], lab, val, J['score'],
          'OK' if abs(val - J['score']) < 1e-6 * max(1, val) else 'MISMATCH'))
