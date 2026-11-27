#!/usr/bin/env python3
"""Check (exact, sympy) that the matrix M of [AN] App. B.3 is, up to diagonal signs and class-constant
scalars, the Szego kernel 1/(z - w) of the Riemann sphere expanded in Moebius local coordinates at four
points:  with G_a = 1, G_d = [[1,-1],[y,-1]], G_c = [[0,-1/x],[-x,0]], G_b = [[y,-1],[y,-y]]/((y-1)x)
(acting on (s,1)^t; x = X, y = x^2) the block (P,Q) of M~ has generating function
   sum_{i,j} M~[(P,i),(Q,j)] s^i t^j  =  eps_PQ / omega(G_P (s,1), G_Q (t,1)),   omega(u,v) = u1 v2 - u2 v1,
eps = +1 for P = a and -1 otherwise (P before Q in the order a, d, c, b), M~ antisymmetric.
M~ is M with row (d,i), column (d,j), row (b,i), column (b,j) multiplied by (-1)^i, (-1)^j.
In the coordinate z of a:  a = 0, d = 1, b = 1/y, c = infinity.
"""
import sympy as sp
x, s, t = sp.symbols('x s t')
y = x**2
def Bp(r, n): return sum(sp.binomial(r, k) * sp.binomial(r + n - k, n - k) * (-y)**(n - k) for k in range(0, min(r, n) + 1))
def Cp(r, n): return sum(sp.binomial(r, k) * y**k * sp.binomial(r + n - k, n - k) * (-1)**(n - k) for k in range(0, min(r, n) + 1))
d = lambda i, j: 1 if i == j else 0
ent = {
 ('a','d'): lambda i,j: Cp(i,j)*(-1)**j,
 ('a','c'): lambda i,j: d(i,j)*x**(2*i+1),
 ('a','b'): lambda i,j: (y-1)*x**(2*i+1)*Bp(i,j)*(-1)**j,
 ('d','c'): lambda i,j: x**(2*j+1)*Bp(j,i)*(-1)**i,
 ('d','b'): lambda i,j: -d(i,j)*x**(2*i+1)*(-1)**(i+j),
 ('c','b'): lambda i,j: -(y-1)*Cp(i,j)*(-1)**j,
 ('d','a'): lambda i,j: -Cp(j,i)*(-1)**i,
 ('c','a'): lambda i,j: -d(i,j)*x**(2*i+1),
 ('b','a'): lambda i,j: -(y-1)*x**(2*j+1)*Bp(j,i)*(-1)**i,
 ('c','d'): lambda i,j: -x**(2*i+1)*Bp(i,j)*(-1)**j,
 ('b','d'): lambda i,j: d(i,j)*x**(2*i+1)*(-1)**(i+j),
 ('b','c'): lambda i,j: (y-1)*Cp(j,i)*(-1)**i,
}
G = {'a': sp.eye(2), 'd': sp.Matrix([[1,-1],[y,-1]]), 'c': sp.Matrix([[0,-1/x],[-x,0]]),
     'b': sp.Matrix([[y,-1],[y,-y]])/((y-1)*x)}
order = 'adcb'
n = 6
ok = True
for (P, Q), f in ent.items():
    u = G[P] * sp.Matrix([s, 1]); v = G[Q] * sp.Matrix([t, 1])
    om = sp.simplify(u[0]*v[1] - u[1]*v[0])
    eps = 1 if 'a' in (P, Q) else -1
    if order.index(P) > order.index(Q):
        pass  # antisymmetry is built into omega
    eps = eps if order.index(P) < order.index(Q) else eps
    ker = sp.series(sp.series(sp.simplify(eps/om) if P == 'a' else sp.simplify(eps/om), s, 0, n).removeO(), t, 0, n).removeO()
    # for P = a rows: +1/omega ; rows of other parties against a: by antisymmetry 1/omega(G_P, G_a) = -1/omega(G_a,G_P), sign +
    kerP = sp.Poly(sp.expand(ker), s, t)
    good = all(sp.simplify(kerP.coeff_monomial(s**i * t**j) - f(i, j)) == 0 for i in range(n) for j in range(n))
    print(P, Q, good)
    ok &= good
print("Szego form verified:", ok)
