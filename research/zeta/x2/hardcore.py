"""Largest lambda* such that bandwidth-1 pair data (DNN: S=|a| on (0,1], S>=0, R2>=0) admit R2 = 0 on (0,lambda):
no distinct pairs closer than lambda.  Pair-only methods therefore cannot prove mu_Dd < lambda* (in the model).
Also report the min simple fraction under the hard-core constraint."""
import numpy as np, sys
from scipy.optimize import linprog
def feas(N,M,lam):
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    ub=list(range(N+1,H+1))
    bounds=[(0,0) if (j>0 and j*N/M<lam) else (0,None) for j in jj]
    r=linprog(-np.eye(H+1)[0],A_ub=-F[ub],b_ub=np.zeros(len(ub)),A_eq=F[eq],b_eq=np.array(beq,float),bounds=bounds,method='highs')
    return (r.status==0), (2-r.x[0]/N if r.status==0 else None)
N=int(sys.argv[1]); M=16*N
lo,hi=0.0,1.5
for _ in range(14):
    mid=(lo+hi)/2; ok,_=feas(N,M,mid)
    lo,hi=(mid,hi) if ok else (lo,mid)
print('N=%d lambda*=%.4f'%(N,lo),flush=True)
for lam in [0.5,0.7,0.8,0.85,0.9]:
    ok,v=feas(N,M,lam); print(' hard core %.2f: feasible=%s min simple=%s'%(lam,ok,None if v is None else round(v,4)),flush=True)
