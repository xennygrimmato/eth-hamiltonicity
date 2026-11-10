"""'Montgomery class' (certificates r>=0 with r^ supported in [-1,1]; = A-F window class by Fejer-Riesz/Krein):
primal drops S>=0 beyond bandwidth.  Row: (1/N) E #{ordered distinct pairs within lambda} >= c."""
import sys, numpy as np
from scipy.optimize import linprog
def lpM(N,M,lam,c):
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    A=[];b=[]
    if c>0:
        row=np.zeros(H+1); sel=(jj>0)&(jj*N/M<lam); row[sel]=-mult[sel]; A.append(row); b.append(-c*N)
    r=linprog(-np.eye(H+1)[0],A_ub=np.array(A) if A else None,b_ub=np.array(b) if b else None,A_eq=F[eq],b_eq=np.array(beq,float),bounds=[(0,None)]*(H+1),method='highs')
    return 2-r.x[0]/N if r.status==0 else np.nan
if __name__=='__main__':
    N=int(sys.argv[1]); M=12*N; base=lpM(N,M,0.5,0)
    print('N=%d Montgomery-class base %.4f'%(N,base),flush=True)
    for lam in [0.3,0.5,0.7,0.9]:
        print('lam=%.1f '%lam+' '.join('c=%.2f:%.4f(+%.4f)'%(c,v,v-base) for c in [0.01,0.02,0.05,0.10] for v in [lpM(N,M,lam,c)]),flush=True)
