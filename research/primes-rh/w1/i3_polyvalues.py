# I3: smallest t such that f(t) (cyclotomic-type, O(n) bits) has a prime factor in [x,2x].
import sympy, math, sys, time
from sympy import factorint, cyclotomic_poly, Symbol
X=Symbol('X')
def first_t(x, f, T=400):
    for t in range(2,T):
        v=f(t)
        if v<x: continue
        # pull out a prime factor in [x,2x] via full factorization (sizes kept <= ~1e30)
        F=factorint(v, limit=None)
        for p in F:
            if x<=p<=2*x: return t,p
    return None
res=[]
for x in [10**6,10**8,10**10,10**12]:
    n=math.log(x)
    for m in [5,7,12,13]:
        ph=sympy.totient(m)
        P=sympy.Poly(cyclotomic_poly(m,X),X)
        f=lambda t,P=P:int(P.eval(t))
        t0=time.time(); r=first_t(x,f)
        print(f"x=1e{round(math.log10(x))} Phi_{m}(t): first t={r} (log x={n:.1f}) time {time.time()-t0:.1f}s",flush=True)
