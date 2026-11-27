"""Blocks with a prescribed relation space (left kernel) of dimension e = 2 for the character construction.

Frequency lattice Z^2: rows beta in B, columns alpha in A, diagonals s = alpha + beta in S.
Every line l gets a vector P_l in K^2 (a point of P^1).  A frequency point may be used if
   - it lies on exactly two chosen lines and their P's are parallel (double point), or
   - it lies on three chosen lines and their P's are pairwise non-parallel (triple point).
M (lines x points): column = the (unique up to scale) vector orthogonal to the P's of the lines through the point.
Then the left kernel of M contains {l -> <phi, P_l>}, so rank M <= #lines - 2, and W_0 = row space of M has
graded parts spanned by the rows of M of each class.  Needed: N = #points >= 2 rank M, the three classes
pairwise independent, and W_0 ^ rho(t) W_0 = 0 for generic t.
This script enumerates small label sets and direction patterns and reports blocks with N >= 2w and generic independence.
"""
import numpy as np, itertools, sys
rng = np.random.default_rng(1)

def set_partitions(n, maxblocks):
    def rec(i, part):
        if i == n: yield list(part); return
        for b in range(max(part, default=-1) + 2):
            if b < maxblocks: 
                part.append(b); yield from rec(i+1, part); part.pop()
    yield from rec(0, [])

def analyse(B, A, S, dirs, ndir, trials=2, verbose=False):
    lines = [('R', b) for b in B] + [('C', a) for a in A] + [('D', s) for s in S]
    v = len(lines)
    # classes must span K^2: at least two directions in each class
    off = [0, len(B), len(B)+len(A), v]
    for c in range(3):
        if len(set(dirs[off[c]:off[c+1]])) < 2: return None
    pts = {}
    for i, b in enumerate(B):
        for j, a in enumerate(A): pts.setdefault((a, b), set()).update([i, off[1]+j])
        for l, s in enumerate(S): pts.setdefault((s-b, b), set()).update([i, off[2]+l])
    for j, a in enumerate(A):
        for l, s in enumerate(S): pts.setdefault((a, s-a), set()).update([off[1]+j, off[2]+l])
    good = []
    for xi, L in pts.items():
        L = sorted(L); d = [dirs[i] for i in L]
        if len(L) == 2 and d[0] == d[1]: good.append((xi, L))
        elif len(L) == 3 and len(set(d)) == 3: good.append((xi, L))
        elif len(L) == 3 and len(set(d)) == 1: good.append((xi, L))          # all parallel: generic annihilator
        elif len(L) == 3:                                                     # two parallel: point used by those two only
            pair = [L[i] for i in range(3) if d.count(d[i]) == 2]
            good.append((xi, pair))
    N = len(good); w = v - 2
    if N < 2*w: return (N, w, False)
    best = False
    for _ in range(trials):
        Pd = rng.normal(size=(ndir, 2)); P = np.array([Pd[d]*rng.uniform(0.5, 2)*rng.choice([-1, 1]) for d in dirs])
        M = np.zeros((v, N))
        for c, (xi, L) in enumerate(good):
            Q = P[L]                      # |L| x 2
            u, sv, vt = np.linalg.svd(Q.T)       # null space of Q^T (2 x |L|)
            null = vt[np.linalg.matrix_rank(Q):]
            col = null.T @ rng.normal(size=len(null))
            if np.min(np.abs(col)) < 1e-9: break
            M[L, c] = col
        else:
            rk = np.linalg.matrix_rank(M)
            if rk != w: continue
            # classes pairwise independent
            ok = all(np.linalg.matrix_rank(np.vstack([M[off[c]:off[c+1]], M[off[c2]:off[c2+1]]])) == (off[c+1]-off[c]) + (off[c2+1]-off[c2])
                     for c in range(3) for c2 in range(c+1, 3))
            if not ok: continue
            x, y = np.exp(2j*np.pi*rng.random(2))
            D = np.array([x**a * y**b for (a, b), L in good])
            sv = np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False)
            if (sv > 1e-8).sum() == 2*w: best = True; break
    return (N, w, best)

if __name__ == "__main__":
    nb, na, ns = map(int, sys.argv[1:4]); span = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    v = nb + na + ns; found = []
    seen = 0
    for B in itertools.combinations(range(span), nb):
        if B[0] != 0: continue
        for A in itertools.combinations(range(span), na):
            for S in itertools.combinations(range(2*span-1), ns):
                for dirs in set_partitions(v, 4):
                    nd = max(dirs) + 1
                    if nd < 3: continue
                    r = analyse(B, A, S, dirs, nd)
                    seen += 1
                    if r and r[2]: found.append((B, A, S, tuple(dirs), r[0], r[1]))
    print("dims (%d,%d,%d): w = %d, need N >= %d; configurations tried %d; blocks found %d" % (nb, na, ns, v-2, 2*(v-2), seen, len(found)))
    for f in found[:8]: print("  ", f)
