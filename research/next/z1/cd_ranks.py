"""Ranks of the Cayley-Dickson composition pieces R = [x^y^u^v=0] s(x,y)s(v,u) (N0 = 2^n, n = 1,2,3) and
C = 2f - R over Q and GF(p); checks the identity holds (C must be a +-1/0 tensor of the same shape) and reports
the tensored rho = (c_row(R) + c_col(R) + 2 log2 T)/(4 n) with T = 2 (Lemma 2 accounting, symmetric R/C)."""
import itertools, numpy as np, sys
from math import log2
sys.path.insert(0, '.')
from f2_pieces import rank_mod, cd_mult
for n in (1, 2, 3):
    s = cd_mult(n); N = 1 << n
    R = np.zeros((N,) * 4, dtype=np.int64); F = np.zeros_like(R)
    for x, y, u, v in itertools.product(range(N), repeat=4):
        if x ^ y ^ u ^ v == 0: R[x, y, u, v] = s[x][y] * s[v][u]
        F[x, y, u, v] = int(x == v and y == u)
    C = 2 * F - R
    col = lambda T: T.transpose(0, 2, 1, 3).reshape(N * N, N * N)
    row = lambda T: T.reshape(N * N, N * N)
    line = [f'N0={N}: C entries {sorted(set(C.flatten().tolist()))}']
    for p in (0, 3, 5, 7, 11, 13):
        rr = np.linalg.matrix_rank(row(R)) if p == 0 else rank_mod(row(R), p)
        rc = np.linalg.matrix_rank(col(R)) if p == 0 else rank_mod(col(R), p)
        cr = np.linalg.matrix_rank(row(C)) if p == 0 else rank_mod(row(C), p)
        cc = np.linalg.matrix_rank(col(C)) if p == 0 else rank_mod(col(C), p)
        rho = (max(log2(rr) + log2(rc), log2(cr) + log2(cc)) + 2) / (4 * n)
        line.append(f"{'Q' if p == 0 else 'GF%d' % p}: R({rr},{rc}) C({cr},{cc}) rho={rho:.4f}")
    print(' | '.join(line))
