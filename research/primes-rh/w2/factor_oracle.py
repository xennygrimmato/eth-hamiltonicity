# Idea 3: with a factoring engine, it suffices to produce N <= x^C having a prime factor in [x,2x].
# K(x,Y) = min k>=0 such that Y+k has a prime factor in [x,2x]  = min over primes p in [x,2x] of (-Y mod p).
import numpy as np, math
from sieve import seg_isprime
rng=np.random.default_rng(1)
def K(x,Y,ps):
    return int(min((-Y)%int(p) for p in ps)) if len(ps)<50000 else int(np.min([(-Y)%int(p) for p in ps]))
def Kvec(Y,ps):  # Y python int
    r=np.array([(-Y)%int(p) for p in ps],dtype=np.int64); return int(r.min()), int(ps[r.argmin()])
res={}
for x in [10**4,3*10**4,10**5,3*10**5,10**6]:
    ps=np.nonzero(seg_isprime(x,2*x+1))[0]+x
    recipes={'x^2':x*x,'x^2+x':x*x+x,'x^3':x**3,'2^ceil(3log2x)':1<<math.ceil(3*math.log2(x)),
             '(2x)!/(x!)^2 mod?':None,'lcm(1..60)':math.lcm(*range(1,61)),'x^2 rounded to 10^k':None}
    out=[]
    for name,Y in recipes.items():
        if Y is None: continue
        k,p=Kvec(Y,ps); out.append(f"{name}:K={k}")
    # worst case over x' in a window for recipe Y=x'^2 and Y=x'^3
    worst2=0;worst3=0
    for xx in range(x,x+200):
        ps2=ps[ps>=xx]; ps2=ps2[ps2<=2*xx]
        worst2=max(worst2,Kvec(xx*xx,ps2)[0]); worst3=max(worst3,Kvec(xx**3+7,ps2)[0])
    print(f"x={x} logx={math.log(x):.1f} "+" ".join(out)+f" | worst over 200 x' : Y=x'^2 {worst2}, Y=x'^3+7 {worst3}")
