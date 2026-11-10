import numpy as np
from scipy.optimize import linprog
def dnn_b(N, M, lo, hi):
    """lo(a), hi(a): bounds on S(a)=nu^(k)/N for k>N (hi=None: none)."""
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    ub=list(range(N+1,H+1))
    A=[];b=[]
    for k in ub:
        a=k/N; l=lo(a); h=hi(a)
        A.append(-F[k]); b.append(-N*l)
        if h is not None: A.append(F[k]); b.append(N*h)
    r=linprog(-np.eye(H+1)[0],A_ub=np.array(A),b_ub=np.array(b),A_eq=F[eq],b_eq=np.array(beq,float),bounds=[(0,None)]*(H+1),method='highs')
    return 2-r.x[0]/N if r.status==0 else np.nan
if __name__=='__main__':
    N=40; M=16*N
    for d in [0.05,0.1,0.25,0.5,1.0]:
        for U in [1.0,1.5,2.0]:
            print('S<=%.1f on (1,1+%.2f]: simple>=%.4f'%(U,d,dnn_b(N,M,lambda a:0,lambda a:U if a<=1+d else None)))
