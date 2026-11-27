"""Randomised version of pattern_search.py: random point configurations in P^{e-1} (points generic, on a line through
two earlier points, or at the intersection of two such lines when e = 3), random placement of symbols (several
symbols of one class at a point allowed), random subsets of the possible transversal triples as wanted incidences.
Reports independent blocks with ratio 3w/v below the threshold.   usage: pattern_random.py e vmin vmax trials seed"""
import numpy as np, itertools, sys
from fractions import Fraction
e, vmin, vmax, trials, seed = map(int, sys.argv[1:6])
rng = np.random.default_rng(seed)

def nullspace_int(rows, n):
    """integer basis of the null space of an integer matrix (fraction Gaussian elimination)."""
    M = [[Fraction(x) for x in r] for r in rows]; piv = []; rk = 0
    for c in range(n):
        p = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]; pv = M[rk][c]; M[rk] = [x/pv for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f*y for x, y in zip(M[i], M[rk])]
        piv.append(c); rk += 1
    free = [c for c in range(n) if c not in piv]; basis = []
    for f in free:
        vec = [Fraction(0)]*n; vec[f] = Fraction(1)
        for i, c in enumerate(piv): vec[c] = -M[i][f]
        den = 1
        for x in vec: den = den*x.denominator // np.gcd(den, x.denominator)
        basis.append([int(x*den) for x in vec])
    return basis

def random_config():
    n = int(rng.integers(e+1, e+5))
    P = [np.eye(e)[i] for i in range(e)]; lines = []
    while len(P) < n:
        u = rng.random()
        if u < 0.7 or len(lines) < 1:
            i, j = sorted(rng.choice(len(P), 2, replace=False))
            if any(i in L and j in L for L in lines): continue
            P.append(rng.uniform(0.5, 2)*P[i] + rng.uniform(0.5, 2)*rng.choice([-1, 1])*P[j]); lines.append((i, j, len(P)-1))
        elif u < 0.85 and e == 3 and len(lines) >= 1:
            # intersection of line(i,j) with an existing line L (not through i or j)
            L = lines[rng.integers(len(lines))]; cand = [x for x in range(len(P)) if x not in L]
            if len(cand) < 2: continue
            i, j = sorted(rng.choice(cand, 2, replace=False))
            if any(i in L2 and j in L2 for L2 in lines): continue
            n1 = np.cross(P[i], P[j]); n2 = np.cross(P[L[0]], P[L[1]]); q = np.cross(n1, n2)
            if np.linalg.norm(q) < 1e-9: continue
            q = q/np.linalg.norm(q)
            if any(abs(np.linalg.det(np.array([q, P[a], P[b]]))) < 1e-9 for (a, b, c) in lines if (a, b) != (L[0], L[1]) and not (a in (i, j) and b in (i, j))): pass
            P.append(q); lines.append((i, j, len(P)-1)); lines.append((L[0], L[1], len(P)-1)) if False else None
            # record the second line as a 3-subset with two points of L
            lines.append((L[0], L[2], len(P)-1))
        else:
            P.append(rng.normal(size=e))
    return np.array(P), lines

def trial():
    P, lines = random_config(); n = len(P)
    v = int(rng.integers(vmin, vmax+1))
    syms = []
    for _ in range(v): syms.append(("RCD"[rng.integers(3)], int(rng.integers(n))))
    syms.sort(key=lambda s: ("RCD".index(s[0]), s[1]))
    cnt = [sum(1 for s in syms if s[0] == c) for c in "RCD"]; off = [0, cnt[0], cnt[0]+cnt[1], v]
    if min(cnt) < e: return None
    Pv = np.array([P[x]*rng.uniform(0.5, 2) for c, x in syms])
    for c in range(3):
        if np.linalg.matrix_rank(Pv[off[c]:off[c+1]]) < e: return None
    # collinear triples of points: from the recorded lines (all 3-subsets of collinear points are found numerically)
    col3 = [T for T in itertools.combinations(range(n), 3) if np.linalg.matrix_rank(P[list(T)], tol=1e-9) == 2]
    eqs = []; usedRC = set()
    cand = []
    for T in col3:
        for (x, y, z) in itertools.permutations(T):
            for i in range(off[0], off[1]):
                if syms[i][1] != x: continue
                for j in range(off[1], off[2]):
                    if syms[j][1] != y: continue
                    for l in range(off[2], off[3]):
                        if syms[l][1] == z: cand.append((i, j, l))
    rng.shuffle(cand)
    usedRD = set(); usedCD = set()
    for (i, j, l) in cand:
        if (i, j) in usedRC or (i, l) in usedRD or (j, l) in usedCD: continue
        if rng.random() < 0.9:
            usedRC.add((i, j)); usedRD.add((i, l)); usedCD.add((j, l))
            row = [0]*v; row[i] = 1; row[j] = 1; row[l] = -1; eqs.append(row)
    ns = nullspace_int(eqs, v) if eqs else [[int(a == b) for a in range(v)] for b in range(v)]
    if not ns: return None
    lab = np.zeros(v, dtype=object)
    for vec in ns: lab = lab + int(rng.integers(1, 60))*np.array(vec, dtype=object)
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
        u_, sv, vt = np.linalg.svd(Q.T); null = vt[r:]
        col = np.zeros(v); col[L] = null.T @ rng.normal(size=len(null)); cols.append(col); keys.append(xi)
    N = len(cols)
    if N < 2*(v - e): return ("few",)
    M = np.array(cols).T; w = np.linalg.matrix_rank(M, tol=1e-9)
    if N < 2*w: return ("few",)
    for c in range(3):
        for c2 in range(c+1, 3):
            if np.linalg.matrix_rank(np.vstack([M[off[c]:off[c+1]], M[off[c2]:off[c2+1]]]), tol=1e-9) < (off[c+1]-off[c]) + (off[c2+1]-off[c2]): return ("dep",)
    sc = max(1, max(abs(a) for k in keys for a in k))
    x, y = np.exp(2j*np.pi*rng.random(2)/sc); D = np.array([x**a * y**b for (a, b) in keys])
    r2 = int((np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False) > 1e-8).sum())
    if r2 < 2*w: return ("union",)
    return ("ok", 3*w/v, w, N, v, tuple(cnt), tuple(syms), tuple(lab), [tuple(np.round(p, 3)) for p in P])

from collections import Counter
stat = Counter(); best = None
for t in range(trials):
    r = trial()
    if r is None: stat["none"] += 1; continue
    stat[r[0]] += 1
    if r[0] == "ok" and (best is None or r[1] < best[1] - 1e-9):
        best = r; print("ratio %.4f w=%d N=%d v=%d dims=%s syms=%s labels=%s" % r[1:8]); sys.stdout.flush()
print("e=%d v in [%d,%d]: %s; best ratio %s" % (e, vmin, vmax, dict(stat), None if best is None else round(best[1], 4)))
