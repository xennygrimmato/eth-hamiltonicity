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
