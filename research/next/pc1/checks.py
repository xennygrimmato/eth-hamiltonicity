# pc1 sanity checks (exact sympy unless noted). Run: python3 -I checks.py
import itertools, random, cmath
import sympy as sp
from math import comb
random.seed(1)

def ryser_roots(n, X):
    R = {}
    for E in itertools.product([0,1], repeat=n):
        s = (-1)**n
        for j in range(n): s *= (1-2*E[j])
        p = s
        for i in range(n): p *= sum(X[i][j]*E[j] for j in range(n))
        R[E] = sp.expand(p)
    return R

# ---- (1) Theorem B, n=2: sum of y-roots of Q = c(x) N_g H  equals per + weighted sum of extra roots
n=2
X = [[sp.Symbol(f'x{i}{j}') for j in range(n)] for i in range(n)]
y = sp.Symbol('y')
R = ryser_roots(n, X)
N = sp.prod([y-r for r in R.values()])
per = X[0][0]*X[1][1]+X[0][1]*X[1][0]
assert sp.expand(sum(R.values())-per)==0
u = X[0][0]*X[1][1]+1           # H has roots +-sqrt(u) (mult 3) and the Ryser root g_(1,0) again (mult 2)
c = X[0][1]**5+X[1][0]+3
H = (y**2-u)**3*(y-R[(1,0)])**2
Q = sp.Poly(sp.expand(c*N*H), y)
co = Q.all_coeffs()
Sigma = sp.simplify(-co[1]/co[0])
assert sp.simplify(Sigma-(per+0+2*R[(1,0)]))==0
print("(1) trace identity Sigma(Q)=per+sum w*rho: OK")

# ---- (2) Buergisser perturbation tracks a root of multiplicity 3 with eps-regular coefficients
z, eps, Y = sp.symbols('z eps Y')
rho = 1+z+2*z**2-z**3           # root function, a=0, y0=1
Qz = (y-rho)**3*(y+2+z)*(y**2+1+z**2)
F = sp.expand(Qz.subs(y, Y+eps) - Qz.subs({y:1+eps, z:0}))
J = sp.diff(F, Y).subs({Y:1, z:0})
cur = sp.Integer(1)
ORD=3
for it in range(ORD+1):          # chord iteration, truncated at z^ORD
    cur = sp.expand(cur - sp.cancel(F.subs(Y, cur)/J))
    cur = sum(sp.cancel(cur.coeff(z,k))*z**k for k in range(ORD+1))
ok=True
for k in range(ORD+1):
    ck = sp.cancel(cur.coeff(z,k))
    lim = sp.limit(ck, eps, 0)
    ok &= (lim == rho.coeff(z,k))
print("(2) perturbed chord iteration -> root coefficients as eps->0:", ok)

# ---- (3) Theorem A numerically: generalized Vandermonde of 2tau-1 Ryser roots has rank tau
import numpy as np
n=3
Xr = [[random.uniform(0.5,1.5)*random.choice([1,-1]) for j in range(n)] for i in range(n)]
vals=[]
for E in itertools.product([0,1], repeat=n):
    if sum(E)==0: continue
    s=(-1)**n
    for j in range(n): s*=(1-2*E[j])
    p=s
    for i in range(n): p*=sum(Xr[i][j]*E[j] for j in range(n))
    vals.append(p)
tau=3; ok=True
for trial in range(200):
    be = random.sample(range(0,40), tau)
    sub = random.sample(vals, 2*tau-1)
    Mx = np.array([[v**b for b in be] for v in sub], dtype=float)
    Mx = Mx/np.abs(Mx).max(axis=0)
    ok &= (np.linalg.matrix_rank(Mx, tol=1e-9)==tau)
print("(3) rank of (g_E^beta_j) on 2tau-1 roots = tau (200 trials, numeric):", ok)

# ---- (4) referee test case: power sums by digit/carry transfer matrices
n=3; M=2**n
xs = sp.symbols('x1:%d'%(n+1))
T = sp.Symbol('T')
Phi = sp.prod([xs[i]+T**(2**i) for i in range(n)])
def pk_direct(k):
    P = sp.Poly(sp.expand(Phi**k), T)
    return M*sum(cf for (e,),cf in P.terms() if e % M==0)
def pk_dp(k):
    # state = carry c; digit a_i in 0..k with (c+a_i) even; new carry (c+a_i)/2
    vec = {0: sp.Integer(1)}
    for i in range(n):
        new={}
        for cc,v in vec.items():
            for a in range(k+1):
                if (cc+a)%2==0:
                    new[(cc+a)//2] = new.get((cc+a)//2,0)+v*comb(k,a)*xs[i]**(k-a)
        vec=new
    return M*sp.expand(sum(vec.values()))
ok = all(sp.expand(pk_direct(k)-pk_dp(k))==0 for k in range(1,6))
print("(4) test-case power sums p_k via carry DP (k<=5, n=3):", ok)
# numeric cross-check that p_k really is the power sum of the roots
pt = {xs[i]: sp.Rational(i+2,3) for i in range(n)}
roots = [complex(sp.N(Phi.subs(pt).subs(T, sp.exp(2*sp.pi*sp.I*j/M)))) for j in range(M)]
ok = all(abs(sum(r**k for r in roots)-complex(pk_dp(k).subs(pt)))<1e-8 for k in range(1,6))
print("    numeric power sums agree:", ok)

# ---- (5) subcube partial Ryser sums project onto per_f  (n=3)
n=3
X = [[sp.Symbol(f'x{i}{j}') for j in range(n)] for i in range(n)]
R = ryser_roots(n, X)
Ysym = [[sp.Symbol(f'Y{i}{j}') for j in range(2)] for i in range(2)]
per2 = Ysym[0][0]*Ysym[1][1]+Ysym[0][1]*Ysym[1][0]
# (i) e_0 = 1 fixed, free F={1,2}: rows 0,1 carry Y on F and 0 on column 0; row 2 = (1,0,0)
S = sum(r for E,r in R.items() if E[0]==1)
sub = {X[2][0]:1, X[2][1]:0, X[2][2]:0}
for i in range(2):
    sub[X[i][0]]=0
    for j in range(2): sub[X[i][j+1]]=Ysym[i][j]
v = sp.expand(S.subs(sub))
print("(5i) subcube e_0=1:", sp.expand(v-per2)==0 or sp.expand(v+per2)==0)
# (ii) e_0 = 0 fixed, free F={1,2}: row 2 = (0,1,0); column 1 of rows 0,1 scaled by zz
zz = sp.Symbol('zz')
S = sum(r for E,r in R.items() if E[0]==0)
sub = {X[2][0]:0, X[2][1]:1, X[2][2]:0}
for i in range(2):
    sub[X[i][0]]=0
    sub[X[i][1]]=zz*Ysym[i][0]; sub[X[i][2]]=Ysym[i][1]
v = sp.expand(S.subs(sub))
d = sp.expand(v.subs(zz,1)-v.subs(zz,0))
print("(5ii) subcube e_0=0:", sp.expand(d-per2)==0 or sp.expand(d+per2)==0)

# ---- (6) hard cyclic norm: sum over mu_M of T^{M-W} prod(1+x_ij T^{w_ij}) = M*per  (n=2)
n=2; B=n+1
w = [[B**i + B**(n+j) for j in range(n)] for i in range(n)]
W = sum(B**i for i in range(2*n)); Mm=1
while Mm <= n*W: Mm*=2
X = [[sp.Symbol(f'x{i}{j}') for j in range(n)] for i in range(n)]
Ph = sp.Poly(sp.expand(T**(Mm-W)*sp.prod([1+X[i][j]*T**w[i][j] for i in range(n) for j in range(n)])), T)
s = Mm*sum(cf for (e,),cf in Ph.terms() if e % Mm==0)
print("(6) trace of weighted cyclic family = M*per_2:", sp.expand(s-Mm*(X[0][0]*X[1][1]+X[0][1]*X[1][0]))==0)
