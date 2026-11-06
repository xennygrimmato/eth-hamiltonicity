"""flat_verify.py -- direct check of the refuting flattening of flat_finite.py:
orientation o* = (1,1,1,1,1,-1,1,1,-1) (all 9 edges split).  Build the 512 x 512 flattening of f_Delta and of random
row/column networks with bonds (2,2,2) (integer entries) and compute exact ranks (mod a large prime and over Q via sympy
for f)."""
from d3lib import *
import numpy as np, itertools
cfg = delta3()
f = cfg.target()                                   # (2,)*18 in row order
o = (1, 1, 1, 1, 1, -1, 1, 1, -1)
nodes = sorted(cfg.nodes)
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
X, Y = [], []
for (u, v), oe in zip(edges, o):
    e = cfg.edges.index(tuple(sorted((u, v))))
    a, b = (u, v) if oe == 1 else (v, u)
    X.append(cfg.sidx[(a, e)]); Y.append(cfg.sidx[(b, e)])
print('X strings', X, 'Y strings', Y)
def flat(T):
    return np.transpose(T.reshape((2,) * 18), X + Y).reshape(512, 512)
P = 2147483629
def rank_mod_p(M, p=P):
    M = (np.array(M, dtype=object) % p).astype(object); M = [list(r) for r in M]
    n, m = len(M), len(M[0]); r = 0
    A = np.array(M, dtype=np.int64) % p
    for c in range(m):
        piv = None
        for i in range(r, n):
            if A[i, c] % p: piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[:, c].copy(); col[r] = 0
        nz = np.nonzero(col)[0]
        for i in nz:
            A[i] = (A[i] - int(col[i]) * A[r]) % p
        r += 1
        if r == n: break
    return r
P = 32749   # keep products < 2^63 in int64 arithmetic
Ff = flat(f)
print('rank of f_Delta across X|Y: (f is a permutation-type 0/1 matrix) rank over Q =', np.linalg.matrix_rank(Ff),
      ', mod', P, '=', rank_mod_p(Ff.astype(np.int64)))
rng = np.random.default_rng(0)
for trial in range(3):
    Wr = [rng.integers(-5, 6, size=(64, 2, 2)) for _ in range(3)]
    Wc = [rng.integers(-5, 6, size=(64, 2, 2)) for _ in range(3)]
    R = np.einsum('axy,bxz,cyz->abc', *Wr).astype(np.int64)
    Cc = np.einsum('axy,bxz,cyz->abc', *Wc).astype(np.int64)
    Cr = cfg.from3_col(Cc.astype(float)).round().astype(np.int64)
    rR = rank_mod_p(flat(R)); rC = rank_mod_p(flat(Cr)); rS = rank_mod_p(flat(R + Cr))
    print(f'random integer R, C (bonds 2,2,2), trial {trial}: rank R = {rR}, rank C = {rC}, rank R+C = {rS}  (mod {P}; bound 128/128/256)')
