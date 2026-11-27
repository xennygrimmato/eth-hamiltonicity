import itertools, numpy as np, sys
import kernel_blocks as kb
rng = np.random.default_rng(5)
def build(B, A, S, dirs):
    lines = [('R', b) for b in B] + [('C', a) for a in A] + [('D', s) for s in S]; v = len(lines)
    off = [0, len(B), len(B)+len(A), v]
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
        elif len(L) == 3 and len(set(d)) in (1, 3): good.append((xi, L))
        elif len(L) == 3: good.append((xi, [L[i] for i in range(3) if d.count(d[i]) == 2]))
    nd = max(dirs)+1
    Pd = rng.normal(size=(nd, 2)); P = np.array([Pd[d]*rng.uniform(0.5, 2) for d in dirs])
    M = np.zeros((v, len(good)))
    for c, (xi, L) in enumerate(good):
        Q = P[L]; u, sv, vt = np.linalg.svd(Q.T); null = vt[np.linalg.matrix_rank(Q):]
        M[L, c] = null.T @ rng.normal(size=len(null))
    return M, good, off
def diag(B, A, S, dirs):
    M, good, off = build(B, A, S, dirs); v = M.shape[0]; N = M.shape[1]
    rk = np.linalg.matrix_rank(M)
    pair = [np.linalg.matrix_rank(np.vstack([M[off[c]:off[c+1]], M[off[c2]:off[c2+1]]])) for c in range(3) for c2 in range(c+1, 3)]
    x, y = np.exp(2j*np.pi*rng.random(2)); D = np.array([x**a * y**b for (a, b), L in good])
    r2 = int((np.linalg.svd(np.vstack([M, M*D[None, :]]), compute_uv=False) > 1e-8).sum())
    return N, rk, pair, r2
if __name__ == "__main__":
    nb, na, ns, span = map(int, sys.argv[1:5]); v = nb+na+ns
    from collections import Counter
    C = Counter(); best = None
    for B in itertools.combinations(range(span), nb):
        if B[0] != 0: continue
        for A in itertools.combinations(range(span), na):
            for S in itertools.combinations(range(2*span-1), ns):
                for dirs in kb.set_partitions(v, 4):
                    r = kb.analyse(B, A, S, dirs, max(dirs)+1, trials=0)
                    if r is None or r[0] < 2*r[1]: continue
                    N, rk, pair, r2 = diag(B, A, S, dirs)
                    C[(N, rk, tuple(pair), r2)] += 1
                    # figure of merit: 2*rk == r2 (independent), classes independent, ratio 3*rk/v
                    if r2 == 2*rk and pair == [nb+na, nb+ns, na+ns]:
                        if best is None or rk < best[0]: best = (rk, N, B, A, S, tuple(dirs))
    for kkey, c in sorted(C.items()): print("N, rank, pair ranks, rank[M;M rho] =", kkey, " x", c)
    print("best independent block:", best)
