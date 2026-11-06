"""rank_search.py -- numerical search for RANK counterexamples on the 9 nodes of AG(2,3) (rows r, columns c, diagonals r-c)
to the candidate 0-entropy inequalities (h = log2 flattening rank, over Q):
   Q*  : 2 h(R_0) <= sum_c h(col_c) + sum_d h(diag_d)
   Q** : sum_r h(R_r) <= 2 [sum_c h(col_c) + sum_d h(diag_d)]           (the one that gives rho >= 1/2 on Delta_3, 3 merges)
   N1  : h(v) <= h(col(v)) + h(diag(v))                                   (quantitative Lemma 7.2 at one node)
Tensors: one leg of dimension D per node (D = 2, 3), entries in {-1,0,1}; simulated annealing on the support.
Objective = violation (positive = counterexample).  Also tests a few structured tensors.  [N]"""
import numpy as np, itertools, sys, time
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
D = int(sys.argv[2]) if len(sys.argv) > 2 else 2
nodes = [(r, c) for r in range(3) for c in range(3)]
idx = {v: i for i, v in enumerate(nodes)}
rows = [[idx[(r, c)] for c in range(3)] for r in range(3)]
cols = [[idx[(r, c)] for r in range(3)] for c in range(3)]
diags = [[idx[(r, c)] for r in range(3) for c in range(3) if (r - c) % 3 == d] for d in range(3)]
def h(T, S):
    S = list(S); rest = [i for i in range(9) if i not in S]
    M = np.transpose(T, S + rest).reshape(D ** len(S), -1)
    return np.log2(max(1, np.linalg.matrix_rank(M, tol=1e-9)))
def profile(T):
    return dict(R=[h(T, S) for S in rows], C=[h(T, S) for S in cols], Dg=[h(T, S) for S in diags], v=[h(T, [i]) for i in range(9)])
def viol(T):
    p = profile(T); sa = sum(p['C']) + sum(p['Dg'])
    qs = 2 * p['R'][0] - sa
    qss = sum(p['R']) - 2 * sa
    n1 = max(p['v'][idx[(r, c)]] - p['C'][c] - p['Dg'][(r - c) % 3] for (r, c) in nodes)
    return qs + 0.02 * sum(p['R']), qss + 0.02 * sum(p['R']), n1 + 0.02 * sum(p['R']), p
def report(tag, T):
    qs, qss, n1, p = viol(T)
    print(f'{tag}: Q* viol {qs:+.3f}, Q** viol {qss:+.3f}, N1 viol {n1:+.3f};  rows {np.round(p["R"],2)} cols {np.round(p["C"],2)} diags {np.round(p["Dg"],2)}', flush=True)
    return qs, qss, n1
# structured tests
shape = (D,) * 9
def ghz(S):
    T = np.zeros(shape)
    for a in range(D):
        ix = [0] * 9
        for i in S: ix[i] = a
        T[tuple(ix)] = 1
    return T
def prod(*Ts):
    out = np.ones(shape)
    for T in Ts: out = out * T   # elementwise product of tensors living on disjoint supports is wrong; use kron-style instead
    return out
def tens(parts):   # parts: list of (node set, tensor on those nodes as full 9-tensor with others at index 0); combine by outer product on disjoint node sets
    T = np.zeros(shape)
    for ix in itertools.product(range(D), repeat=9):
        val = 1.0
        for S, P in parts:
            jx = [0] * 9
            for i in S: jx[i] = ix[i]
            val *= P[tuple(jx)]
        T[ix] = val
    return T
report('GHZ on each column (one leg)', tens([(cols[c], ghz(cols[c])) for c in range(3)]))
report('GHZ on each diagonal', tens([(diags[d], ghz(diags[d])) for d in range(3)]))
report('GHZ on each row', tens([(rows[r], ghz(rows[r])) for r in range(3)]))
report('GHZ on each triangle', tens([([idx[(r, c)] for (r, c) in nodes if (r + c) % 3 == s], ghz([idx[(r, c)] for (r, c) in nodes if (r + c) % 3 == s])) for s in range(3)]))
# annealing on random sparse {-1,0,1} tensors
best = (-np.inf, None, None)
t0 = time.time()
for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 6):
    k = rng.integers(6, 40)
    T = np.zeros(shape); pts = rng.integers(0, D, size=(k, 9))
    for p in pts: T[tuple(p)] = rng.choice([-1, 1])
    which = rng.integers(0, 3)    # which objective: 0 Q*, 1 Q**, 2 N1
    cur = viol(T)[which]; temp = 0.3
    for it in range(1500):
        T2 = T.copy()
        mv = rng.integers(0, 3)
        p = tuple(rng.integers(0, D, size=9))
        if mv == 0: T2[p] = rng.choice([-1, 1])
        elif mv == 1: T2[p] = 0
        else:
            nz = np.argwhere(T2 != 0)
            if len(nz) == 0: continue
            q = tuple(nz[rng.integers(0, len(nz))]); T2[q] = 0; T2[p] = rng.choice([-1, 1])
        if not T2.any(): continue
        new = viol(T2)[which]
        if new >= cur or rng.random() < np.exp((new - cur) / temp):
            T, cur = T2, new
        temp *= 0.998
        if cur > best[0]: best = (cur, T.copy(), which)
    print(f'trial {trial} (objective {["Q*","Q**","N1"][which]}): best violation {cur:+.3f}  [{time.time()-t0:.0f}s]', flush=True)
print('\noverall best:'); report(f'best (objective {["Q*","Q**","N1"][best[2]]})', best[1])
