"""DNN finite model + AVERAGED upper bound on S just above bandwidth 1:  (1/delta) int_1^{1+delta} S <= B."""
import numpy as np, sys
from scipy.optimize import linprog
def dnn_avg(N,M,delta,B):
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    ub=list(range(N+1,H+1)); A=[-F[k] for k in ub]; b=[0.0]*len(ub)
    ks=[k for k in ub if k<=N*(1+delta)]
    if ks: A.append(F[ks].sum(0)); b.append(B*N*len(ks))   # sum_k S(k/N)*N <= B*N*#k
    r=linprog(-np.eye(H+1)[0],A_ub=np.array(A),b_ub=np.array(b),A_eq=F[eq],b_eq=np.array(beq,float),bounds=[(0,None)]*(H+1),method='highs')
    return 2-r.x[0]/N
if __name__=='__main__':
    N=int(sys.argv[1]) if len(sys.argv)>1 else 40; M=16*N
    print('N',N,'none',round(dnn_avg(N,M,0,0),4))
    for d in [0.05,0.1,0.25,0.5]:
        print('delta=%.2f'%d, ' '.join('B=%g:%.4f'%(B,dnn_avg(N,M,d,B)) for B in [1,2,5,10,20]))
