"""Route 4: field dependence of the crossing pieces.
(1) Eight-square pieces (Lemma 2 of the ETH paper, N0 = 8): R = [x^y^u^v = 0] s(x,y) s(v,u) with octonion signs s,
    C := 2[x=v][y=u] - R.  Ranks of R, C row-wise (xy|uv) and column-wise (xu|yv) over Q, GF(3), GF(2).
(2) Exhaustive search at N0 = 2 (one bit per leg) for T = 2 and T = 3 piece families sum_j A_j = d [x=v][y=u] over GF(2)
    and GF(3): best rho = (max_x min_k <x, c_k> + log2 T) / (E m0), E m0 = 2, c_k = log2 rank (T = 1 gives rho = 1,
    T >= 4 gives rho >= 1 from naming alone).
"""
import itertools, numpy as np
from math import log2

def rank_mod(M, p):
    M = np.array(M, dtype=np.int64) % p; r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p: piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows: break
    return r

# ---------- octonion signs by Cayley-Dickson ----------
def cd_mult(n):
    """returns sign table s[a][b] with e_a e_b = s e_{a^b} for the 2^n-dim Cayley-Dickson algebra"""
    if n == 0: return [[1]]
    s0 = cd_mult(n - 1); h = 1 << (n - 1)
    conj = lambda a: 1 if a == 0 else -1
    S = [[0] * (2 * h) for _ in range(2 * h)]
    # (a,b)(c,d) = (ac - d* b, d a + b c*) on basis: e_a = (e_a,0), e_{h+a} = (0,e_a)
    for A in range(2 * h):
        for B in range(2 * h):
            a, ha = A % h, A >= h; b, hb = B % h, B >= h
            if not ha and not hb: S[A][B] = s0[a][b]
            elif not ha and hb: S[A][B] = s0[b][a]              # (x,0)(0,d) = (0, d x)
            elif ha and not hb: S[A][B] = s0[a][b] * conj(b)    # (0,y)(c,0) = (0, y c*)
            else: S[A][B] = -conj(b) * s0[b][a]                 # (0,y)(0,d) = (-d* y, 0)
    return S
s = cd_mult(3)
N = 8
R = np.zeros((N,) * 4, dtype=np.int64); F = np.zeros_like(R)
for x, y, u, v in itertools.product(range(N), repeat=4):
    if x ^ y ^ u ^ v == 0: R[x, y, u, v] = s[x][y] * s[v][u]
    F[x, y, u, v] = 1 if (x == v and y == u) else 0
C = 2 * F - R
row = lambda T: T.reshape(N * N, N * N)                       # (x,y) | (u,v)
col = lambda T: T.transpose(0, 2, 1, 3).reshape(N * N, N * N)  # (x,u) | (y,v)
print('eight-square at N0 = 8 (costs = log2 rank)')
print('  entries of C in', sorted(set(C.flatten().tolist())))
for name, T in (('R', R), ('C', C), ('f', F)):
    out = []
    for p in (0, 3, 2):
        if p == 0: rr, rc = np.linalg.matrix_rank(row(T)), np.linalg.matrix_rank(col(T))
        else: rr, rc = rank_mod(row(T), p), rank_mod(col(T), p)
        out.append(f"{'Q' if p == 0 else 'GF(%d)' % p}: row {rr} col {rc} -> ({log2(max(rr,1)):.2f},{log2(max(rc,1)):.2f})")
    print(' ', name, ' | '.join(out))
print('  identity R + C = d f with d = 2: over GF(2) it reads R + C = 0 (no identity).')
print('  C mod 2 == R mod 2:', bool(((C - R) % 2 == 0).all()))

# ---------- exhaustive N0 = 2 ----------
def game(costs, T):
    # max over mixtures x of min over the two merges, by LP-free scan (2 merges: piecewise linear in x)
    cs = np.array(costs, dtype=float)
    if T == 1: return min(cs[0])
    best = -1
    grid = np.linspace(0, 1, 401)
    if T == 2:
        for t in grid:
            x = np.array([t, 1 - t]); best = max(best, min(x @ cs[:, 0], x @ cs[:, 1]))
    else:
        for t1 in grid[::4]:
            for t2 in grid[::4]:
                if t1 + t2 > 1: continue
                x = np.array([t1, t2, 1 - t1 - t2]); best = max(best, min(x @ cs[:, 0], x @ cs[:, 1]))
    return best

def search(p):
    """For rho < 1 every pure strategy must cost < 1 bit, i.e. every piece has rank 1 in some flattening (rank 0 =
    zero piece, droppable).  So enumerate pieces in R1 = {rank-1 in row or col}; T = 2: A in R1, B = d f - A in R1;
    T = 3: A, B in R1, C = d f - A - B in R1.  Exhaustive."""
    rowperm = [8 * x + 4 * y + 2 * u + v for x in range(2) for y in range(2) for u in range(2) for v in range(2)]
    colperm = [8 * x + 4 * y + 2 * u + v for x in range(2) for u in range(2) for y in range(2) for v in range(2)]
    inv = lambda perm: np.argsort(perm)
    vecs = [np.array(w) for w in itertools.product(range(p), repeat=4) if any(w)]
    R1 = {}
    for perm in (rowperm, colperm):
        for a in vecs:
            for b in vecs:
                M = np.outer(a, b) % p
                T = np.zeros(16, dtype=np.int64); T[perm] = M.reshape(-1)
                R1[tuple(T)] = T
    R1 = list(R1.values())
    f = np.zeros(16, dtype=np.int64)
    for x, y in itertools.product(range(2), repeat=2): f[8 * x + 4 * y + 2 * y + x] = 1
    def prof(T): return (rank_mod(T[rowperm].reshape(4, 4), p), rank_mod(T[colperm].reshape(4, 4), p))
    key = {tuple(T): i for i, T in enumerate(R1)}
    profs = [prof(T) for T in R1]
    best = {2: (9, None), 3: (9, None)}
    for d in range(1, p):
        for i, A in enumerate(R1):
            B = tuple((d * f - A) % p)
            if B in key:
                cs = [[log2(r) for r in profs[i]], [log2(r) for r in profs[key[B]]]]
                rho = (game(cs, 2) + 1) / 2
                if rho < best[2][0]: best[2] = (rho, (profs[i], profs[key[B]]))
            for j in range(i, len(R1)):
                Cc = tuple((d * f - A - R1[j]) % p)
                if Cc in key:
                    cs = [[log2(r) for r in profs[k]] for k in (i, j, key[Cc])]
                    rho = (game(cs, 3) + log2(3)) / 2
                    if rho < best[3][0]: best[3] = (rho, (profs[i], profs[j], profs[key[Cc]]))
    return len(R1), best

if __name__ == '__main__':
    import sys
    for p in (2, 3):
        n, b = search(p); print(f'N0 = 2, GF({p}): |R1| = {n}; best rho T=2:', b[2], ' T=3:', b[3], flush=True)
