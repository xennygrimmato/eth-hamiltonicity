# Sanity check of Lemma L (reduced case) on the hypersurface {det X = 0}, n=3 (9 variables),
# NP-verifier: exists w with X w = 0 and c.w = 1. Newton (chord) tracking of the d=3 branches
# t_j(A+TU) of det(A+TU+tB)=0 over C[U][[T]]/T^{d+1}, then det(A+TU) = det(B)*prod(-t_j) mod T^{d+1}.
import sympy as sp, random
random.seed(1)
N=3; d=N
U=sp.Matrix(N,N,lambda i,j: sp.Symbol(f'u{i}{j}')); T=sp.Symbol('T')
rnd=lambda: sp.Rational(random.randint(-9,9),random.randint(1,5))
A=sp.Matrix(N,N,lambda i,j:rnd()); B=sp.Matrix(N,N,lambda i,j:rnd()); c=sp.Matrix([rnd() for _ in range(N)])
def trunc(e): 
    e=sp.expand(e); return sum(e.coeff(T,k)*T**k for k in range(d+1))
# roots of det(A+tB) in t (numeric, high precision)
t=sp.Symbol('t'); roots=sp.Poly((A+t*B).det(),t).nroots(n=40)
prod=sp.Integer(1)
for tj in roots:
    M=(A+tj*B); w0=M.nullspace(simplify=True) if False else None
    # kernel vector numerically: solve M[0:N-1] w = 0 with c.w=1
    Msys=sp.Matrix.vstack(M[0:N-1,:],c.T); rhs=sp.Matrix([0]*(N-1)+[1]); w=Msys.LUsolve(rhs)
    z0=sp.Matrix([tj]+list(w))                      # unknowns (t,w)
    def G(z,X):
        tt=z[0]; ww=sp.Matrix(z[1:]); return sp.Matrix.vstack((X+tt*B)*ww, sp.Matrix([ (c.T*ww)[0]-1 ]))
    zs=sp.Matrix(sp.symbols('z0:%d'%(N+1))); J0=G(zs,A).jacobian(zs).subs(dict(zip(zs,z0))); J0i=J0.inv()
    z=z0; X=A+T*U
    for _ in range(d+1):
        z=(z-J0i*G(z,X)).applyfunc(trunc)
    prod=trunc(prod*(-z[0]))
lhs=trunc((B.det()*prod)); rhs_=trunc((A+T*U).det())
diff=sp.expand(lhs-rhs_)
print('max |coeff| of difference:', max([abs(sp.N(co)) for co in sp.Poly(diff,*(list(U)+[T])).coeffs()] or [0]))
