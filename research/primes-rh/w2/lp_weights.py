# Idea 7 test: exact additive functionals f(I)=sum_{n in I} w(n) are engine-computable when w is a polynomial
# (degree D = O(1)) in divisor-range counts c_i(n)=#{d|n : d in J_i}. If w<=0 on composites and f([x,2x])>0,
# bisection on f finds a prime (one half always has f>0; length-1 interval with f>0 is a prime).
# LP: maximize sum_n w(n) s.t. w(0-vector)=1 (primes), w(v)<=0 for every composite feature vector v.
import numpy as np, itertools, math, sys
from scipy.optimize import linprog
from sieve import seg_isprime
def features(x,cuts):
    lo,hi=x,2*x+1; U=hi-lo; r=math.isqrt(2*x)
    edges=[2]+[int(round(x**c)) for c in cuts]+[r+1]
    F=np.zeros((U,len(edges)-1),dtype=np.int32)
    for i in range(len(edges)-1):
        for d in range(edges[i],edges[i+1]):
            st=((lo+d-1)//d)*d
            F[st-lo::d,i]+=1
    return F,edges
def run(x,D,cuts=(1/6,1/4,1/3)):
    P=seg_isprime(x,2*x+1); F,edges=features(x,cuts)
    assert np.all(F[P].sum(1)==0) and np.all(F[~P].sum(1)>0)
    comp=F[~P]; vecs,cnt=np.unique(comp,axis=0,return_counts=True)
    k=F.shape[1]; scale=np.maximum(vecs.max(0),1).astype(float)
    mons=[a for d in range(D+1) for a in itertools.product(range(d+1),repeat=k) if sum(a)==d]
    V=vecs/scale
    Phi=np.stack([np.prod(V**np.array(a),axis=1) for a in mons],axis=1)  # rows: composite vectors
    # variables c (len mons); c_0 (all-zero monomial)=1 fixed via equality
    obj=-(cnt@Phi)                # maximize sum over composites (primes add pi*1)
    Aeq=np.zeros((1,len(mons))); Aeq[0,0]=1
    res=linprog(obj,A_ub=Phi,b_ub=np.zeros(len(vecs)),A_eq=Aeq,b_eq=[1],bounds=[(None,None)]*len(mons),method='highs')
    pi=P.sum(); best=pi-res.fun*(-1)*(-1) if False else pi+(cnt@Phi)@res.x
    return pi,len(vecs),len(mons),best,res.status
if __name__=="__main__":
  for x in [10**4,3*10**4,10**5,3*10**5,10**6]:
     line=[]
     for D in [1,2,3,4,5,6]:
         pi,nv,nm,best,st=run(x,D)
         line.append(f"D={D}:{best/pi:+.3f}")
     print(f"x={x} pi={pi} distinct composite vectors={nv}  max f/pi: "+" ".join(line),flush=True)
