# V1: can EXACT divisor-range counts (Type-I/convolution data) predict pi(J) on windows J?
# Features per window J (length h): D_y(J) = #{(d,e): d*e in J, 2<=d<=y, d<=e} for a grid of y up to sqrt,
# and S(J)=sum_{m in J} tau(m). Fit pi(J) by least squares; compare residual to sd of pi(J).
import numpy as np, sys, math
P=np.load(sys.argv[1]).astype(np.int64)
lo=10**8; L=10**7; h=int(sys.argv[2]) if len(sys.argv)>2 else 2000
hi=lo+L; r=math.isqrt(hi)
m=np.arange(lo,hi)
ys=[2,3,5,10,30,100,300,1000,3000,r]
cum=np.zeros((len(ys),L),np.int32); acc=np.zeros(L,np.int32); k=0
tau=np.zeros(L,np.int32)
for d in range(2,r+1):
    st=((lo+d-1)//d)*d
    idx=np.arange(st-lo,L,d)
    e=(idx+lo)//d
    ok=idx[e>=d]; acc[ok]+=1
    tau[idx[e>d]]+=2; tau[idx[e==d]]+=1
    while k<len(ys) and d==ys[k]: cum[k]=acc; k+=1
tau+=2
isP=np.zeros(L,bool); pp=P[(P>=lo)&(P<hi)]-lo; isP[pp]=True
nw=L//h
def wsum(a): return a[:nw*h].reshape(nw,h).sum(1).astype(float)
y=wsum(isP.astype(np.int32))
X=np.column_stack([np.ones(nw)]+[wsum(c) for c in cum]+[wsum(tau)])
tr=np.arange(nw)%2==0
beta,*_=np.linalg.lstsq(X[tr],y[tr],rcond=None)
res=y[~tr]-X[~tr]@beta
print(f"h={h} windows={nw} mean pi={y.mean():.1f} sd(pi)={y.std():.3f} heldout residual sd={res.std():.3f} max|res|={abs(res).max():.2f}")
# sanity identity check: composites count with multiplicity: D_r = sum (#divisors d<=sqrt m, d>=2)
print(" check: windows with D_sqrt==0 (all prime):",int((wsum(cum[-1])==0).sum()))
