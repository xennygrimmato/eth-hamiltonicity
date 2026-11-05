"""Task A checks.  (1) eight-square identity at N=8 (lam=3): R+C = 2F, ranks of R, C row-/column-wise (App. H: 8, 64).
(2) Lemma 2 pieces A_i for t blocks (exact ranks) vs the eigen-count formula of App. H.
(3) single-bit identity F = P + B, pieces A_i of its t-fold power, exact ranks vs formula, and the
    asymptotic per-bit value max_i (log r_row + log r_col)/t -> 2 + log2 3 = log2 12."""
import numpy as np, itertools, math, sys
from lib import rank_modp
def sigma(p, q):
    p1, p2, p3 = p; q1, q2, q3 = q
    ph = sum(p[i] * q[j] for i in range(3) for j in range(i, 3)) + q1 * p2 * p3 + p1 * q2 * p3 + p1 * p2 * q3
    return (-1) ** (ph % 2)
B3 = list(itertools.product(range(2), repeat=3)); ix = {b: i for i, b in enumerate(B3)}
xor = lambda a, b: tuple(i ^ j for i, j in zip(a, b))
N = 8
R = np.zeros((N,) * 4, dtype=np.int64); C = np.zeros_like(R); F = np.zeros_like(R)
for x, y, u, v in itertools.product(B3, repeat=4):
    I = (ix[x], ix[y], ix[u], ix[v])
    R[I] = (xor(x, y) == xor(v, u)) * sigma(x, y) * sigma(v, u)
    C[I] = (xor(x, u) == xor(v, y)) * sigma(x, u) * sigma(v, y)
    F[I] = (x == v) * (y == u)
assert (R + C == 2 * F).all(); print("eight-square: R + C = 2 [x=v][y=u] at all 4096 settings: OK")
row = lambda T: T.reshape(T.shape[0] * T.shape[1], -1)                       # (x,y)|(u,v)
col = lambda T: np.transpose(T, (0, 2, 1, 3)).reshape(T.shape[0] * T.shape[2], -1)  # (x,u)|(y,v)
for nm, T in (('R', R), ('C', C), ('F', F)):
    print(f"  {nm}: rank row-wise {rank_modp(row(T))}, column-wise {rank_modp(col(T))}")
print("  simple count per 3-bit block: log 8 + log 64 + 2 naming bits = 3+6+2 = 11 of 12")

def kron4(A, B):  # tensor product of two 4-leg pieces, blockwise legs
    n = A.shape[0] * B.shape[0]
    return np.einsum('abcd,efgh->aebfcgdh', A, B).reshape(n, n, n, n)
def pieces(R, C, t):
    """A_i = sum_{|Q|=i} prod_s (C if s in Q else R), i = 0..t"""
    out = []
    for i in range(t + 1):
        S = None
        for Q in itertools.combinations(range(t), i):
            T = None
            for s in range(t):
                f = C if s in Q else R
                T = f if T is None else kron4(T, f)
            S = T if S is None else S + T
        out.append(S)
    return out
def formula(N, t, i):  # App. H: rank = sum_{z<=i} C(t,z) (N^2-N)^z N^(t-z)
    return sum(math.comb(t, z) * (N * N - N) ** z * N ** (t - z) for z in range(i + 1))

print("Lemma 2 pieces (eight-square), t blocks, i = #blocks taking C:")
for t in (1, 2):
    for i, A in enumerate(pieces(R, C, t)):
        rr, rc = rank_modp(row(A)), rank_modp(col(A))
        assert rr == formula(8, t, i) and rc == formula(8, t, t - i)
        print(f"  t={t} i={i}: rank row {rr}, col {rc}  (App. H formula: {formula(8, t, i)}, {formula(8, t, t - i)})", flush=True)
print(f"  t->inf, i=t/2: per 3-bit block 2*(1 + (log2 56 + 3)/2) = {2*(1+(math.log2(56)+3)/2):.4f} = 2 + log2 448 = {2+math.log2(448):.4f} of 12 bits")
# single bit
F1 = np.zeros((2,) * 4, dtype=np.int64); P1 = np.zeros_like(F1); B1 = np.zeros_like(F1)
for x, y, u, v in itertools.product(range(2), repeat=4):
    F1[x, y, u, v] = (x == v) * (y == u); P1[x, y, u, v] = (x == u) * (y == v)
    B1[x, y, u, v] = -(x != y) * (u != v) * (-1) ** (x + u)
assert (F1 == P1 + B1).all(); print("single-bit identity [x=v][y=u] = [x=u][y=v] - [x!=y](-1)^x [u!=v](-1)^u: OK")
for nm, T in (('P', P1), ('B', B1)): print(f"  {nm}: rank row {rank_modp(row(T))}, col {rank_modp(col(T))}")
def f1(t, i): return sum(math.comb(t, z) * 3 ** z for z in range(i + 1))
for t in range(1, 6):
    best = 0
    for i, A in enumerate(pieces(B1, P1, t)):   # i = #bits taking P (row-expensive)
        rr, rc = rank_modp(row(A)), rank_modp(col(A))
        assert rr == f1(t, i) and rc == f1(t, t - i), (t, i, rr, rc)
        best = max(best, math.log2(rr) + math.log2(rc))
    print(f"  t={t}: ranks match sum_(z<=i) C(t,z)3^z (row) and same with t-i (col) for all i; worst piece row+col bits per bit = {best/t:.4f}", flush=True)
H = lambda a: 0 if a in (0, 1) else -a * math.log2(a) - (1 - a) * math.log2(1 - a)
print(f"  t->inf: worst piece i=t/2 gives 2*(H(1/2)+log2(3)/2) = {2*(1+math.log2(3)/2):.4f} = log2 12 = {math.log2(12):.4f} of 4 bits")
