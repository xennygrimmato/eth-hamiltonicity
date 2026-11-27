"""Structured search for blocks of the character construction with a relation space of dimension e (section 9).

A pattern: points x_1..x_n of P^{e-1} with some 3-point lines; each point carries a subset of the classes {R,C,D}
(a symbol = one chosen line of the frequency lattice, with vector P = the point).  Wanted incidences: every
coincidence at a point, and every transversal triple (R at x, C at y, D at z) on a 3-point line {x,y,z}.
The labels (beta for R-symbols, alpha for C, s for D) are a generic integer solution of alpha + beta = s on the
wanted triples.  The block is then evaluated from the labels alone (all frequency points on the chosen lines,
column of M = generic element of the annihilator of the P's of the lines through the point).
Reported: blocks with N >= 2w, classes pairwise independent, W_0 ^ rho(t)W_0 = 0 for generic t; ratio = 3w/#symbols.
usage: pattern_search.py CONFIG [maxsym]      CONFIG in line3, line3+1, twolines, triangle, quad, line4, ...
"""
import numpy as np, itertools, sys
from sympy import Matrix
rng = np.random.default_rng(3)

def config(name):
    g = lambda *a: rng.normal(size=a)
    if name == "line3":      # e = 2
        b = np.eye(2); P = [b[0], b[1], b[0]+b[1]*1.7]; lines = [(0, 1, 2)]
    elif name == "line4":
        b = np.eye(2); P = [b[0], b[1], b[0]+b[1]*1.7, b[0]-0.6*b[1]]; lines = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
    elif name == "line3+1":  # e = 3: three collinear points and one generic
        b = np.eye(3); P = [b[0], b[1], b[0]+1.7*b[1], b[2]]; lines = [(0, 1, 2)]
    elif name == "twolines": # lines {0,1,2}, {0,3,4}
        b = np.eye(3); P = [b[0], b[1], b[0]+1.7*b[1], b[2], b[0]-0.8*b[2]]; lines = [(0, 1, 2), (0, 3, 4)]
    elif name == "triangle": # b0,b1,b2 and one point on each side
        b = np.eye(3); P = [b[0], b[1], b[2], b[0]+1.7*b[1], b[1]-0.8*b[2], b[0]+0.6*b[2]]; lines = [(0, 1, 3), (1, 2, 4), (0, 2, 5)]
    elif name == "quad":     # complete quadrilateral: the three side points collinear
        b = np.eye(3); p3 = b[0]+1.7*b[1]; p4 = b[1]-0.8*b[2]
        # p5 on line(b0,b2) and line(p3,p4): p3 + 1.7*p4 = b0 + 3.4 b1 - 1.36 b2 ... solve: p5 = p3 - 1.7*p4 = b0 + 1.36 b2
        p5 = p3 - 1.7*p4; P = [b[0], b[1], b[2], p3, p4, p5]; lines = [(0, 1, 3), (1, 2, 4), (0, 2, 5), (3, 4, 5)]
    elif name == "tri2":     # triangle with two side points only
        b = np.eye(3); P = [b[0], b[1], b[2], b[0]+1.7*b[1], b[1]-0.8*b[2]]; lines = [(0, 1, 3), (1, 2, 4)]
    elif name == "path3":    # e = 4: three lines in a path {0,1,2},{2,3,4},{4,5,6}
        b = np.eye(4); P = [b[0], b[1], b[0]+1.7*b[1], b[2], b[0]+1.7*b[1]-0.8*b[2], b[3], b[0]+1.7*b[1]-0.8*b[2]+0.6*b[3]]
        lines = [(0, 1, 2), (2, 3, 4), (4, 5, 6)]
    elif name == "star3":    # e = 4: three lines through one point
        b = np.eye(4); P = [b[0], b[1], b[0]+1.7*b[1], b[2], b[0]-0.8*b[2], b[3], b[0]+0.6*b[3]]
        lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6)]
    return np.array(P, dtype=float), lines

def evaluate(P, lines, carry, e):
    """carry[x] = string of classes at point x."""
    syms = [(c, x) for c in "RCD" for x in range(len(P)) if c in carry[x]]
    v = len(syms); idx = {s: i for i, s in enumerate(syms)}
    cnt = [sum(1 for s in syms if s[0] == c) for c in "RCD"]; off = [0, cnt[0], cnt[0]+cnt[1], v]
    Pv = np.array([P[x]*rng.uniform(0.5, 2) for c, x in syms])
    for c in range(3):
        if cnt[c] == 0 or np.linalg.matrix_rank(Pv[off[c]:off[c+1]]) < e: return None
    eqs = []
    for L in lines:
        for (x, y, z) in itertools.permutations(L):
            if ('R', x) in idx and ('C', y) in idx and ('D', z) in idx:
                row = [0]*v; row[idx[('R', x)]] = 1; row[idx[('C', y)]] = 1; row[idx[('D', z)]] = -1; eqs.append(row)
    if eqs:
        ns = Matrix(eqs).nullspace()
    else:
        ns = [Matrix([1 if i == j else 0 for i in range(v)]) for j in range(v)]
    if not ns: return None
    lab = np.zeros(v, dtype=object)
    for vec in ns:
        den = 1
        for q in vec: den = np.lcm(den, int(q.q))
        coef = int(rng.integers(1, 40))
        lab = lab + coef*np.array([int(q*den) for q in vec], dtype=object)
    lab = [int(q) for q in lab]
    for c in range(3):
        if len(set(lab[off[c]:off[c+1]])) < cnt[c]: return None
    pts = {}
    for i in range(off[0], off[1]):
        for j in range(off[1], off[2]): pts.setdefault((lab[j], lab[i]), set()).update([i, j])
        for l in range(off[2], off[3]): pts.setdefault((lab[l]-lab[i], lab[i]), set()).update([i, l])
    for j in range(off[1], off[2]):
        for l in range(off[2], off[3]): pts.setdefault((lab[j], lab[l]-lab[j]), set()).update([j, l])
    cols = []; keys = []
    for xi, L in pts.items():
        L = sorted(L); Q = Pv[L]; r = np.linalg.matrix_rank(Q, tol=1e-9)
        if r == len(L): continue
        u, sv, vt = np.linalg.svd(Q.T); null = vt[r:]
        col = np.zeros(v); col[L] = null.T @ rng.normal(size=len(null)); cols.append(col); keys.append(xi)
    N = len(cols)
    if N < 2*(v - e): return ("few", N, v)
    M = np.array(cols).T; w = np.linalg.matrix_rank(M, tol=1e-9)
    if N < 2*w: return ("few", N, v)
    for c in range(3):
        for c2 in range(c+1, 3):
            if np.linalg.matrix_rank(np.vstack([M[off[c]:off[c+1]], M[off[c2]:off[c2+1]]]), tol=1e-9) < (off[c+1]-off[c]) + (off[c2+1]-off[c2]): return ("dep", N, v)
    sc = max(1, max(abs(a) for k in keys for a in k))
    x, y = np.exp(2j*np.pi*rng.random(2)/sc); D = np.array([x**a * y**b for (a, b) in keys])
    r2 = int((np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False) > 1e-8).sum())
    Dg = np.exp(2j*np.pi*rng.random(N))
    rg = int((np.linalg.svd(np.vstack([M, M*Dg[None, :]]), compute_uv=False) > 1e-8).sum())
    return ("ok" if r2 == 2*w else ("torus" if rg == 2*w else "union"), N, v, w, r2, tuple(cnt), tuple(lab))

if __name__ == "__main__":
    name = sys.argv[1]; maxsym = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    P, lines = config(name); e = np.linalg.matrix_rank(P); n = len(P)
    opts = ["R", "C", "D", "RC", "RD", "CD", "RCD"]
    from collections import Counter
    stat = Counter(); best = None
    for carry in itertools.product(opts, repeat=n):
        v = sum(len(c) for c in carry)
        if v > maxsym or v < 3*e: continue
        r = evaluate(P, lines, carry, e)
        if r is None: stat["none"] += 1; continue
        stat[r[0]] += 1
        if r[0] == "ok":
            ratio = 3*r[3]/r[2]
            if best is None or ratio < best[0] - 1e-9:
                best = (ratio, carry, r); print("ratio %.4f carry=%s  N=%d v=%d w=%d dims=%s labels=%s" % (ratio, carry, r[1], r[2], r[3], r[5], r[6])); sys.stdout.flush()
    print(name, "e =", e, "stats:", dict(stat), "best ratio:", None if best is None else round(best[0], 4))
