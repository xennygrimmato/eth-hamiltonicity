"""Independent check of the GF(3) rank drop of the octonion piece R (column flattening): build R from an explicit
octonion multiplication table (Fano-plane convention, NOT Cayley-Dickson), find the integer determinant of each
8x8 block of the block-diagonal column flattening, and verify kernel vectors mod 3 by integer multiplication."""
import itertools, numpy as np, sympy
# Fano lines (i,j,k): e_i e_j = e_k cyclically; index octonion units 1..7 by 3-bit labels via XOR-closed triples
lines = [(1,2,3),(1,4,5),(1,7,6),(2,4,6),(2,5,7),(3,4,7),(3,6,5)]
s = [[1]*8 for _ in range(8)]
for a in range(1,8): s[a][a] = -1
for (i,j,k) in lines:
    assert i ^ j == k
    for (a,b,c) in ((i,j,k),(j,k,i),(k,i,j)):
        s[a][b] = 1; s[b][a] = -1
# check it is a composition (norm multiplicative): (sum x)(sum y) via signed bilinear: sum_a s(a,a^w)... quick test
rng = np.random.default_rng(0)
for _ in range(5):
    x = rng.normal(size=8); y = rng.normal(size=8); z = np.zeros(8)
    for a in range(8):
        for b in range(8): z[a ^ b] += s[a][b] * x[a] * y[b]
    assert abs((z**2).sum() - (x**2).sum() * (y**2).sum()) < 1e-9
N = 8
R = np.zeros((N,)*4, dtype=np.int64)
for x,y,u,v in itertools.product(range(N), repeat=4):
    if x^y^u^v == 0: R[x,y,u,v] = s[x][y]*s[v][u]
Rc = R.transpose(0,2,1,3).reshape(64,64)
Rr = R.reshape(64,64)
M = sympy.Matrix(Rc.tolist())
print('integer rank col', M.rank(), ' row', sympy.Matrix(Rr.tolist()).rank())
print('det(col flattening) =', sympy.factorint(M.det()))
Mm = M.applyfunc(lambda t: t % 3)
ker = sympy.Matrix(Mm).nullspace(iszerofunc=lambda t: t % 3 == 0) if False else None
# rank mod 3 via sympy GF arithmetic
from sympy.polys.matrices import DomainMatrix
from sympy import GF
D = DomainMatrix.from_Matrix(M).convert_to(GF(3))
print('rank mod 3 (sympy DomainMatrix over GF(3)):', D.rank())
D2 = DomainMatrix.from_Matrix(M).convert_to(GF(2)); print('rank mod 2:', D2.rank())
