"""The (3,3,3) block (cyclic_line3.py, beta = (0,1,3), c = 0): the locus of characters (X,Y) with W_0 ^ rho(t)W_0 != 0.
Convention of cyclic_line3.py: classes r, c, r-c; collinear: X = 1, Y = 1, XY = 1 (t1 = t2 corresponds to ... see below).
rho(t) e_(alpha,beta) = X^alpha Y^beta e, X = zeta^t1, Y = zeta^t2.  Diagonal vectors live on alpha+beta = s, so D_0 is fixed
by rho(t,-t)?  no: X^alpha Y^beta is constant on alpha+beta = s iff X = Y.  Collinear curves: X = 1, Y = 1, X = Y.
Special curves (Prop. 3.2): XY = 1, Y = X^2, X = Y^2."""
import sympy as sp, itertools
from cyclic_line3 import block
X, Y = sp.symbols('X Y')
pts, M = block(10**9, (0, 1, 3), 0)          # integer labels (modulus irrelevant)
pts = [(a if a < 10**8 else a - 10**9, b if b < 10**8 else b - 10**9) for a, b in pts]
M = sp.Matrix(M)
amin = min(p[0] for p in pts); bmin = min(p[1] for p in pts)
D = sp.diag(*[X**(p[0]-amin) * Y**(p[1]-bmin) for p in pts])
# 7 independent rows of M
rows = []
for r in range(9):
    if sp.Matrix([M.row(i) for i in rows + [r]]).rank() == len(rows) + 1: rows.append(r)
Mt = sp.Matrix([M.row(i) for i in rows]).T
A = Mt.row_join(D*Mt)                        # 15 x 14
minors = []
for drop in range(15):
    rr = [i for i in range(15) if i != drop]
    d = sp.factor(A.extract(rr, list(range(14))).det(method='berkowitz'))
    minors.append(d)
    print("minor without row", drop, ":", d); 
G = minors[0]
for m in minors[1:]: G = sp.gcd(G, m)
print("gcd:", sp.factor(G))
