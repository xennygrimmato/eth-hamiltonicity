"""Octahedron arrangement, parameters (a2,b2,g1,g2): for which characters (X,Y) = (zeta^t1, zeta^t2) is W_0 ^ rho(t)W_0 != 0?

A = [Mt | D Mt] (12 x 10), Mt = transpose of M with one row dropped, D = diag(X^alpha Y^beta).
W_0 ^ rho(t)W_0 != 0  iff  rank A < 10  iff  all 10 x 10 minors vanish.  The minors are polynomials in X, Y that do not
depend on g.  We compute them, remove the factors (X-1), (Y-1), (XY-1) (collinear t) and powers of X, Y, and
determine the common zeros of what is left.
"""
import sympy as sp, itertools, sys
X, Y = sp.symbols('X Y')
a2, b2, g1, g2 = (int(x) for x in sys.argv[1:5]) if len(sys.argv) > 4 else (1, 1, 2, 3)
lines = [('R', 0), ('R', b2), ('C', 0), ('C', a2), ('D', g1), ('D', g2)]
pts = set()
for b in (0, b2):
    for a in (0, a2): pts.add((a, b))
    for d in (g1, g2): pts.add((b+d, b))
for a in (0, a2):
    for d in (g1, g2): pts.add((a, a-d))
pts = sorted(pts); assert len(pts) == 12
def on(p): return [i for i, (t, v) in enumerate(lines) if (t == 'R' and p[1] == v) or (t == 'C' and p[0] == v) or (t == 'D' and p[0]-p[1] == v)]
M = sp.zeros(6, 12)
for j, p in enumerate(pts):
    i1, i2 = on(p); M[i1, j] = 1; M[i2, j] = -1
amin = min(p[0] for p in pts); bmin = min(p[1] for p in pts)
D = sp.diag(*[X**(p[0]-amin) * Y**(p[1]-bmin) for p in pts])      # shift exponents to be >= 0 (a global character)
Mt = M[:5, :].T
A = Mt.row_join(D*Mt)
def strip(f):
    f = sp.factor(f)
    for h in (X, Y, X-1, Y-1, X*Y-1):
        while True:
            qq, rr = sp.div(sp.expand(f), h, X, Y)
            if rr != 0: break
            f = qq
    return sp.factor(f)
minors = []
for rows in itertools.combinations(range(12), 10):
    d = A.extract(list(rows), list(range(10))).det(method='berkowitz')
    d = sp.expand(d)
    if d != 0: minors.append(d)
    if len(minors) >= 14: break
G = minors[0]
for m in minors[1:]: G = sp.gcd(G, m)
print("gcd of %d minors:" % len(minors), sp.factor(G))
red = [strip(sp.cancel(m/G)) for m in minors]
red = [r for r in red if r.free_symbols]
print("reduced minors (first three):"); [print("  ", r) for r in red[:3]]
gb = sp.groebner(red, X, Y, order='lex')
print("Groebner basis of the reduced minors:"); [print("  ", sp.factor(p)) for p in gb.exprs]
