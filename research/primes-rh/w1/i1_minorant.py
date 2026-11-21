# I1: certifying-weight bisection. w(m)<=0 on composites, w(p)>0, Sum_I w cheap => bisect.
# Test candidate cheap weights on [x,2x].
import numpy as np, sympy, sys
x=int(sys.argv[1]) if len(sys.argv)>1 else 10**6
N=x; lo,hi=x,2*x
m=np.arange(lo,hi+1,dtype=np.int64)
r=int((2*x)**0.5)+1
t=np.zeros(len(m),dtype=np.int64)       # divisors in [2, sqrt m]
lpf=np.zeros(len(m),dtype=np.int64)
for d in range(2,r+1):
    s=(-lo)%d
    idx=np.arange(s,len(m),d)
    idx=idx[d*d<=m[idx]]
    t[idx]+=1
    z=idx[lpf[idx]==0]; lpf[z]=d
isp=(t==0)
pi=isp.sum()
print("x",x,"pi[x,2x]",pi)
print("w=1-t: sum",(1-t).sum())
primes=list(sympy.primerange(2,r+2))
for z in [10,100,1000,int((2*x)**(1/3))+1]:
    ps=[p for p in primes if p<z]
    om=np.zeros(len(m),dtype=np.int64)
    for p in ps: om[((-lo)%p)::p]+=1
    rough=(om==0)
    # s = divisors in [z, sqrt m]
    s=np.zeros(len(m),dtype=np.int64)
    for d in range(z,r+1):
        st=(-lo)%d; idx=np.arange(st,len(m),d); idx=idx[d*d<=m[idx]]; s[idx]+=1
    # exact rough indicator (NOT cheap unless z tiny) times (1-s)
    w_exact=rough*(1-s)
    # cheap Bonferroni-1 lower bound rho^- = 1-omega_z, rho^+ = 1
    w_cheap=(1-om)-s
    # Bonferroni-2 upper rho^+ = 1-om+C(om,2) (>=1_rough, >=0)
    rp=1-om+om*(om-1)//2
    w_cheap2=(1-om)-rp*s
    print(f"z={z}: rough-composites-with-s>=2: {((rough)&(~isp)&(s>=2)).sum()}  sum rough*(1-s)={w_exact.sum()}  sum[(1-om)-s]={w_cheap.sum()}  sum[(1-om)-rho2*s]={w_cheap2.sum()}")
