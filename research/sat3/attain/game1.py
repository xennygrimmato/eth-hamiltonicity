#!/usr/bin/env python3
"""Level-1 crossing-cover game on a net level (attain-notes.md, section 2).

Level tensor: one wire of 1 unit of bits on every edge of a configuration on the nodes G x G of a 3-net
(merges 0: row r, 1: column c, 2: diagonal r - c).  Level-1 covers: every edge's bits are split among
"factors"; a factor is an unordered pair of distinct edges (e, e') with p bits of e = (a,c) and q bits of
e' = (b,d), expanded by the crossing identity into pieces Psi_theta, theta in [0, pi/2], with
    r  = log-rank across ab|cd <= min(R cos(theta), p+q),   r' = across ad|bc <= min(R sin(theta), p+q),
    R = sqrt(2(p^2+q^2)),   third cut ac|bd: trivial bound 2 min(p,q).
A term (one theta per factor) is evaluated under ONE merge k; a piece is realised under merge k as a
two-hub network (Lemma A.3) with hubs at groups of merge k, or with everything gathered at one group:
    c_k = min( S, Ac + r, Ab + r', A3 + 2min(p,q) ),
with S, Ac, Ab, A3 the bits that have to be moved to the hub groups.  Bits left raw cost [e crosses k].

Value for merge weights w in the simplex:   h(w) = min over designs of
    sum_f x_f  max_theta sum_k w_k c_k(f, theta)  +  sum_e raw_e sum_k w_k [e crosses k],
and the level value is min_w h(w) (per term the cheapest merge; the adversary mixes thetas over blocks).
For fixed w this is an LP; we solve its dual
    max sum_e y_e   s.t.  y_e <= raw_w(e),   p y_e + q y_e' <= m_w(e, e'; p, q)   (p + q = 1 on a grid).
"""
import sys, itertools, math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

NTH = 2001
TH = np.linspace(0.0, math.pi / 2, NTH)
COS, SIN = np.cos(TH), np.sin(TH)


def group_ops(name):
    """return list of elements and subtraction table for the additive group 'name' (e.g. '3', '2x2', '4')."""
    dims = [int(t) for t in name.split('x')]
    els = list(itertools.product(*[range(d) for d in dims]))
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    sub = np.zeros((n, n), dtype=int)
    for a in range(n):
        for b in range(n):
            sub[a, b] = idx[tuple((x - y) % d for x, y, d in zip(els[a], els[b], dims))]
    return n, sub


def net(name):
    g, sub = group_ops(name)
    nodes = [(r, c) for r in range(g) for c in range(g)]
    lab = np.array([[r, c, sub[r, c]] for (r, c) in nodes])  # (g^2, 3) group labels per merge
    return g, nodes, lab


def consts(la, lb, lc, ld, p, q):
    """moving costs for the realisations of a 4-leg piece with group labels la..ld (one merge)."""
    labs = {la, lb, lc, ld}
    def mv(o, items):
        return sum(w for (l, w) in items if l != o)
    allit = [(la, p), (lb, q), (lc, p), (ld, q)]
    S = min(mv(o, allit) for o in labs)
    def two(I1, I2):
        best = 1e9
        for o in labs | {-1}:
            for o2 in labs | {-2}:
                if o == o2:
                    continue
                best = min(best, mv(o, I1) + mv(o2, I2))
        return best
    Ac = two([(la, p), (lb, q)], [(lc, p), (ld, q)])
    Ab = two([(la, p), (ld, q)], [(lb, q), (lc, p)])
    A3 = two([(la, p), (lc, p)], [(lb, q), (ld, q)])
    return S, Ac, Ab, A3


_cache = {}


def canon(l4):
    m = {}
    return tuple(m.setdefault(x, len(m)) for x in l4)


def mval(pats, p, q, w, detail=False):
    """exact max over theta of sum_k w_k c_k for the canonical patterns pats (one per merge).
    c_k(theta) = min(K_k, Ac_k + min(R cos, p+q), Ab_k + min(R sin, p+q)) is piecewise of the form
    const / A + R cos / A + R sin, so the maximum is at a breakpoint or at a stationary point
    tan(theta) = b/a of a*cos + b*sin with (a, b) sums of weights."""
    key = (pats, round(p, 9), tuple(np.round(w, 9)))
    if not detail and key in _cache:
        return _cache[key]
    R = math.sqrt(2 * (p * p + q * q))
    r3 = 2 * min(p, q)
    cs = []
    for pat in pats:
        S, Ac, Ab, A3 = consts(*pat, p, q)
        cs.append((min(S, A3 + r3), Ac, Ab))
    cand = {0.0, math.pi / 2, math.pi / 4}
    def addcos(x):
        if 0 <= x <= 1: cand.add(math.acos(x))
    def addsin(x):
        if 0 <= x <= 1: cand.add(math.asin(x))
    addcos((p + q) / R); addsin((p + q) / R)
    for (K, Ac, Ab) in cs:
        addcos((K - Ac) / R); addsin((K - Ab) / R)
        # Ac + R cos = Ab + R sin  ->  cos(theta + pi/4) = (Ab - Ac)/(R sqrt2)
        x = (Ab - Ac) / (R * math.sqrt(2))
        if -1 <= x <= 1:
            th = math.acos(x) - math.pi / 4
            if 0 <= th <= math.pi / 2: cand.add(th)
        # with caps: Ac + (p+q) = Ab + R sin, Ac + R cos = Ab + (p+q)
        addsin((Ac + p + q - Ab) / R); addcos((Ab + p + q - Ac) / R)
    ws = [w[k] for k in range(len(pats))]
    for br in itertools.product((0, 1, 2), repeat=len(pats)):
        a = sum(ws[k] for k in range(len(pats)) if br[k] == 1)
        b = sum(ws[k] for k in range(len(pats)) if br[k] == 2)
        if a > 0 and b > 0: cand.add(math.atan2(b, a))
    th = np.array(sorted(cand))
    r = np.minimum(R * np.cos(th), p + q)
    rp = np.minimum(R * np.sin(th), p + q)
    tot = np.zeros(len(th)); per = []
    for k, (K, Ac, Ab) in enumerate(cs):
        ck = np.minimum(K, np.minimum(Ac + r, Ab + rp))
        per.append(ck); tot += w[k] * ck
    i = int(np.argmax(tot))
    if detail:
        return tot[i], th[i], [c[i] for c in per]
    _cache[key] = tot[i]
    return tot[i]


def solve(lab, edges, w, tgrid, want_primal=False):
    """dual LP. edges: list of (n1, n2) node indices. returns value, y, (active constraints)."""
    E = len(edges)
    w = np.asarray(w, float)
    npm = lab.shape[1]
    raw = np.array([sum(w[k] for k in range(npm) if lab[a, k] != lab[c, k]) for (a, c) in edges])
    rows, cols, vals, rhs, info = [], [], [], [], []
    nr = 0
    for i in range(E):
        a, c = edges[i]
        for j in range(i + 1, E):
            b, d = edges[j]
            pats = tuple(canon((lab[a, k], lab[b, k], lab[c, k], lab[d, k])) for k in range(npm))
            # the other orientation (b <-> d) exchanges the two cuts, i.e. theta <-> pi/2 - theta: same value
            for t in tgrid:
                m = mval(pats, t, 1 - t, w)
                if m >= t * raw[i] + (1 - t) * raw[j] - 1e-12:
                    continue  # implied by y <= raw
                rows += [nr, nr]; cols += [i, j]; vals += [t, 1 - t]; rhs.append(m); info.append((i, j, t, pats))
                nr += 1
    if nr == 0:
        return raw.sum(), raw, []
    A = coo_matrix((vals, (rows, cols)), shape=(nr, E)).tocsr()
    res = linprog(-np.ones(E), A_ub=A, b_ub=np.array(rhs), bounds=[(0, raw[i]) for i in range(E)], method='highs')
    assert res.status == 0, res.message
    y = res.x
    act = []
    if want_primal:
        mu = -res.ineqlin.marginals
        for idx in np.nonzero(mu > 1e-9)[0]:
            act.append((mu[idx],) + info[idx])
    return -res.fun, y, act


def all_edges(nodes):
    n = len(nodes)
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


if __name__ == '__main__':
    name = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 else 'full'
    nt = int(sys.argv[3]) if len(sys.argv) > 3 else 9
    g, nodes, lab = net(name)
    edges = all_edges(nodes)
    if mode == 'generic':   # edges crossing all three merges
        edges = [(a, c) for (a, c) in edges if all(lab[a, k] != lab[c, k] for k in range(3))]
    tgrid = [i / (nt + 1) for i in range(1, nt + 1)]
    E = len(edges)
    print(f"net {name}: g={g}, mode={mode}, E={E}, t-grid {nt}")
    for w in [(0.5, 0.5, 0.0), (1 / 3, 1 / 3, 1 / 3), (0.4, 0.4, 0.2), (0.45, 0.45, 0.1), (0.6, 0.2, 0.2), (1, 0, 0)]:
        v, y, act = solve(lab, edges, w, tgrid)
        rawv = sum(sum(w[k] for k in range(3) if lab[a, k] != lab[c, k]) for (a, c) in edges)
        print(f"  w={tuple(round(x,3) for x in w)}: h={v:.6f}  h/E={v/E:.6f}  raw/E={rawv/E:.6f}")
