"""Graph blocks for the character construction (classes r, c, r+c; diagonals of the frequency lattice: alpha - beta).
A block = some rows (beta values), columns (alpha values), diagonals (alpha-beta values) of the dual group Z_g^2,
frequencies = their pairwise intersection points (each on exactly two used lines), W = cut space of the
incidence graph.  For each block: the set of non-collinear t with W ^ rho(t)W != 0 (complex SVD)."""
import numpy as np, itertools, sys
def block(g, rows, cols, diags):
    lines = [('R', b % g) for b in rows] + [('C', a % g) for a in cols] + [('D', d % g) for d in diags]
    def on(pt):
        a, b = pt
        return [i for i, (t, v) in enumerate(lines) if (t == 'R' and b == v) or (t == 'C' and a == v) or (t == 'D' and (a-b) % g == v)]
    pts = set()
    for (t1, v1), (t2, v2) in itertools.combinations(lines, 2):
        if t1 == t2: continue
        d = {t1: v1, t2: v2}
        if 'R' in d and 'C' in d: pts.add((d['C'], d['R']))
        elif 'R' in d: pts.add(((d['R'] + d['D']) % g, d['R']))
        else: pts.add((d['C'], (d['C'] - d['D']) % g))
    pts = sorted(pts)
    ne = len(rows)*len(cols) + len(rows)*len(diags) + len(cols)*len(diags)
    if len(pts) != ne or any(len(on(p)) != 2 for p in pts): return None
    M = np.zeros((len(lines), len(pts)))
    for j, p in enumerate(pts):
        i1, i2 = on(p); M[i1, j] = 1; M[i2, j] = -1
    return pts, M
def badset(g, rows, cols, diags):
    r = block(g, rows, cols, diags)
    if r is None: return None
    pts, M = r; w = np.linalg.matrix_rank(M); z = np.exp(2j*np.pi/g); bad = []
    for t1 in range(1, g):
        for t2 in range(1, g):
            if (t1+t2) % g == 0: continue
            D = np.array([z**((a*t1+b*t2) % g) for a, b in pts])
            sv = np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False)
            if (sv > 1e-8).sum() < 2*w: bad.append((t1, t2))
    return w, len(pts), bad
if __name__ == "__main__":
    g = int(sys.argv[1])
    # special differences for classes r, c, r+c: (a,a), (a,-2a), (-2a,a)
    special = set()
    for a in range(1, g):
        for t in ((a, a), (a, (-2*a) % g), ((-2*a) % g, a)):
            if t[0] and t[1] and (t[0]+t[1]) % g: special.add(t)
    best = None
    for b2, a2, d1 in itertools.product(range(1, g), range(1, g), range(g)):
        r = badset(g, (0, b2), (0, a2), (d1,))
        if r is None: continue
        w, N, bad = r
        ns = [t for t in bad if t not in special]
        if best is None or len(ns) < best[0]: best = (len(ns), len(bad), (b2, a2, d1), w, N, ns[:5])
    print("g =", g, "#special", len(special), " K_{2,2,1} block (rows 0,b2; cols 0,a2; diag d1): best (non-special bad, all bad, params, w, N):", best)
