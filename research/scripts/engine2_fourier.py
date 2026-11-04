"""engine2 M2/M4: (i) 'monomial' pieces of the rectangle F=[x=v][y=u] in ANY product basis (Walsh, random unimodular)
have rank_row = rank_col = |S|, so c_row + c_col = 2 log|S| and Sum_s |S_s| = D^2 -> rho -> 1 with 2^{o(lam)} pieces;
(ii) node-local invertible transforms (acting jointly on all legs a node holds, across gadgets) leave every
node-union flattening rank unchanged, so no transform -- within or between levels -- changes any rank-based cost."""
import itertools, random
from engine2_lib import *
random.seed(2)
allok = True

def unimodular(D):
    M = [[int(i == j) for j in range(D)] for i in range(D)]
    Mi = [[int(i == j) for j in range(D)] for i in range(D)]
    for _ in range(3 * D):
        i, j = random.sample(range(D), 2); c = random.choice([-1, 1])
        for k in range(D): M[k][j] += c * M[k][i]          # col op on M: col j += c col i
        for k in range(D): Mi[i][k] -= c * Mi[j][k]         # matching row op on inverse
    return M, Mi

def walsh(lam):
    D = 2 ** lam
    H = [[(-1) ** bin(x & a).count('1') for a in range(D)] for x in range(D)]
    return H, None   # inverse = H^T / D (handled by scaling)

for lam in [2, 3]:
    D = 2 ** lam
    for basis in ['walsh', 'unimodular']:
        if basis == 'walsh':
            M, _ = walsh(lam); Mi = [[M[v][a] for v in range(D)] for a in range(D)]; scale = D * D
        else:
            M, Mi = unimodular(D); scale = 1
        def piece(S):
            # A_S(x,y,u,v) = sum_{(al,be) in S} M[x][al] Mi[al][v] M[y][be] Mi[be][u]
            return {(x, y, u, v): sum(M[x][al] * Mi[al][v] * M[y][be] * Mi[be][u] for al, be in S)
                    for x in range(D) for y in range(D) for u in range(D) for v in range(D)}
        full = piece([(al, be) for al in range(D) for be in range(D)])
        okF = all(full[(x, y, u, v)] == scale * (x == v) * (y == u) for (x, y, u, v) in full)
        allok &= report(f"lam={lam} {basis}: sum of all D^2 monomial pieces = {scale}*[x=v][y=u]", okF)
        good = True; sizes = []
        for trial in range(6):
            k = random.randint(1, D * D)
            S = random.sample([(al, be) for al in range(D) for be in range(D)], k)
            A = piece(S)
            row = [[A[(x, y, u, v)] for u in range(D) for v in range(D)] for x in range(D) for y in range(D)]
            col = [[A[(x, y, u, v)] for y in range(D) for v in range(D)] for x in range(D) for u in range(D)]
            rr, rc = rank_exact(row), rank_exact(col)
            sizes.append((k, rr, rc)); good &= (rr == k == rc)
        allok &= report(f"lam={lam} {basis}: monomial pieces have rank_row = rank_col = |S|  {sizes}", good)

# (ii) two rectangles on the same 4 nodes (distinct legs); node 0 holds one leg of each; apply a random
# invertible map jointly on node 0's two legs; flattening ranks across every node bipartition unchanged.
D = 2
# legs: gadget g in {0,1}, node n in {0..3}: leg (g,n). F_g = [x_{g0}=x_{g3}][x_{g1}=x_{g2}]  (row cut {0,1}|{2,3}, col cut {0,2}|{1,3})
L = [(g, n) for g in range(2) for n in range(4)]
def Ftensor():
    return {xs: int(all(xs[L.index((g, 0))] == xs[L.index((g, 3))] and xs[L.index((g, 1))] == xs[L.index((g, 2))] for g in range(2)))
            for xs in itertools.product(range(D), repeat=8)}
T = Ftensor()
M, Mi = unimodular(D * D)
def transform(T):
    out = {}
    i0, i1 = L.index((0, 0)), L.index((1, 0))
    for xs in itertools.product(range(D), repeat=8):
        s = 0
        for a in range(D):
            for b in range(D):
                ys = list(xs); ys[i0], ys[i1] = a, b
                s += M[xs[i0] * D + xs[i1]][a * D + b] * T[tuple(ys)]
        out[xs] = s
    return out
T2 = transform(T)
def flat_rank(T, side):
    A = [i for i, (g, n) in enumerate(L) if n in side]; B = [i for i in range(8) if i not in A]
    rows = {}
    for xs, v in T.items():
        rows.setdefault(tuple(xs[i] for i in A), {})[tuple(xs[i] for i in B)] = v
    keysB = sorted({k for r in rows.values() for k in r})
    return rank_exact([[rows[ka].get(kb, 0) for kb in keysB] for ka in sorted(rows)])
ok = True; res = []
for side in [{0}, {0, 1}, {0, 2}, {0, 3}, {1}, {1, 2}]:
    r1, r2 = flat_rank(T, side), flat_rank(T2, side); res.append((tuple(sorted(side)), r1, r2)); ok &= r1 == r2
allok &= report(f"(ii) joint transform at node 0 across two gadgets: node-cut ranks unchanged {res}", ok)
print("ALL PASS" if allok else "SOME FAIL")
