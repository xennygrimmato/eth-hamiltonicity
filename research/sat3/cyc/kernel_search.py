"""Random search for blocks with a relation space of dimension e >= 2 (character construction, section 9 of cyclic-cap.md).

A block: rows B, columns A, diagonals S (integer labels; frequency point (alpha,beta) lies on row beta, column alpha,
diagonal alpha+beta); every line l gets a vector P_l in K^e taken from a small "direction configuration"
(points of P^{e-1} with prescribed collinear triples).  A frequency point on the chosen lines L is used iff the P_l,
l in L, are linearly dependent; its column of M is a generic element of the annihilator.  Then
   rank M = #lines - e  (if the circuits span),  W_0 = row space of M,  graded parts = rows of M by class.
Target: N >= 2 rank M, classes pairwise independent, rank [M; M rho(t)] = 2 rank M for generic t, and
   ratio = 3 rank M / #lines  (w/k after adding the two rotations of the block)  below 7/3.
usage: kernel_search.py e nb na ns trials seed
"""
import numpy as np, itertools, sys
e, nb, na, ns, trials, seed = map(int, sys.argv[1:7])
rng = np.random.default_rng(seed)
v = nb + na + ns; off = [0, nb, nb+na, v]

def directions(nd):
    """nd points of K^e: first e are a basis; the others are generic, or on a line through two earlier points."""
    P = [np.eye(e)[i] for i in range(e)]
    desc = ['b%d' % i for i in range(e)]
    while len(P) < nd:
        if rng.random() < 0.75:
            i, j = rng.choice(len(P), 2, replace=False)
            P.append(rng.normal()*P[i] + rng.normal()*P[j]); desc.append('(%d,%d)' % (min(i, j), max(i, j)))
        else:
            P.append(rng.normal(size=e)); desc.append('g')
    return np.array(P), desc

def trial():
    span = rng.integers(3, 7)
    B = sorted(rng.choice(span, nb, replace=False)); A = sorted(rng.choice(span, na, replace=False))
    S = sorted(rng.choice(2*span-1, ns, replace=False))
    nd = rng.integers(e+1, min(v, e+5)+1)
    Pd, desc = directions(nd)
    dirs = rng.integers(0, nd, size=v)
    P = np.array([Pd[d]*rng.uniform(0.5, 2) for d in dirs])
    for c in range(3):
        if np.linalg.matrix_rank(P[off[c]:off[c+1]]) < e: return None
    pts = {}
    for i, b in enumerate(B):
        for j, a in enumerate(A): pts.setdefault((a, b), set()).update([i, off[1]+j])
        for l, s in enumerate(S): pts.setdefault((s-b, b), set()).update([i, off[2]+l])
    for j, a in enumerate(A):
        for l, s in enumerate(S): pts.setdefault((a, s-a), set()).update([off[1]+j, off[2]+l])
    cols = []; keys = []
    for xi, L in pts.items():
        L = sorted(L); Q = P[L]; r = np.linalg.matrix_rank(Q, tol=1e-9)
        if r == len(L): continue
        u, sv, vt = np.linalg.svd(Q.T); null = vt[r:]
        col = np.zeros(v); col[L] = null.T @ rng.normal(size=len(null))
        cols.append(col); keys.append(xi)
    N = len(cols)
    if N < 2*(v - e): return None
    M = np.array(cols).T; w = np.linalg.matrix_rank(M, tol=1e-9)
    if N < 2*w: return None
    for c in range(3):
        for c2 in range(c+1, 3):
            if np.linalg.matrix_rank(np.vstack([M[off[c]:off[c+1]], M[off[c2]:off[c2+1]]]), tol=1e-9) < (off[c+1]-off[c]) + (off[c2+1]-off[c2]): return None
    x, y = np.exp(2j*np.pi*rng.random(2)); D = np.array([x**a * y**b for (a, b) in keys])
    r2 = int((np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False) > 1e-8).sum())
    if r2 < 2*w: return None
    return (3*w/v, w, N, tuple(B), tuple(A), tuple(S), tuple(int(d) for d in dirs), tuple(desc))

best = None; hits = 0
for t in range(trials):
    r = trial()
    if r is None: continue
    hits += 1
    if best is None or r[0] < best[0] - 1e-12:
        best = r; print("ratio %.4f  w=%d N=%d  B=%s A=%s S=%s dirs=%s  directions=%s" % r); sys.stdout.flush()
print("e=%d dims (%d,%d,%d): trials %d, valid independent blocks %d, best ratio %s" % (e, nb, na, ns, trials, hits, None if best is None else round(best[0], 4)))
