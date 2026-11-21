# Critical roughness exponent u0: with EXACT z-roughness (z=x^{1/u}), certifying weights
#  wA = R*(1 - s),  s = #divisors in [z,sqrt m]       (level 1, cut O(n))
#  wB = R*(1 - w'), w'= #prime divisors in [z,sqrt m]  (level 2: needs primality of divisors)
# Sum over window vs pi. Positive => bisection certifies a prime.
import numpy as np, sympy, sys, math, itertools
x=int(float(sys.argv[1])); W=int(float(sys.argv[2]))
lo=x; hi=x+W
rem=list(range(lo,hi)); fac=[[] for _ in range(W)]
r=math.isqrt(hi)+1
rem=np.arange(lo,hi,dtype=np.int64)
for p in sympy.primerange(2,r+1):
    st=(-lo)%p
    for i in range(st,W,p):
        e=0
        while rem[i]%p==0: rem[i]//=p; e+=1
        fac[i].append((p,e))
for i in range(W):
    if rem[i]>1: fac[i].append((int(rem[i]),1))
pi=sum(1 for f in fac if len(f)==1 and f[0][1]==1)
print("x",x,"W",W,"pi",pi)
def divisors(f):
    ds=[1]
    for p,e in f: ds=[d*p**k for d in ds for k in range(e+1)]
    return ds
for u in [2.5,3,3.5,4,5,6,8]:
    z=x**(1/u); SA=SB=0; nrough=0
    for i,f in enumerate(fac):
        m=lo+i
        if f[0][0]<z: continue
        nrough+=1
        sq=math.isqrt(m)
        s=sum(1 for d in divisors(f) if z<=d<=sq)
        w=sum(1 for p,e in f if p<=sq)
        SA+=1-s; SB+=1-w
    print(f"u={u}: z={z:.0f} rough={nrough} sum wA={SA} sum wB={SB}  (pi={pi})",flush=True)
