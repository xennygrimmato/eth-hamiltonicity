"""DNN finite model with extra *lower bounds* on S beyond bandwidth 1: S(a) >= L(a) for 1<a<=c2.
GGOS-type (GRH) bound: F(a) >= 3/2 - a on [1,3/2].  Also test 'S >= t' for constant t on (1,1+d]."""
import numpy as np
from scipy.optimize import linprog
def dnn_lb(N, M, L, c2):
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    ub=list(range(N+1,H+1)); lb=np.array([N*L(k/N) if k<=c2*N else 0.0 for k in ub])
    r=linprog(-np.eye(H+1)[0],A_ub=-F[ub],b_ub=-lb,A_eq=F[eq],b_eq=np.array(beq,float),bounds=[(0,None)]*(H+1),method='highs')
    return r.x[0]/N if r.status==0 else np.nan
if __name__=='__main__':
    N=40; M=16*N
    print('none', 2-dnn_lb(N,M,lambda a:0,1))
    print('GGOS 3/2-a on [1,1.5]', 2-dnn_lb(N,M,lambda a:max(1.5-a,0),1.5))
    for d in [0.05,0.1,0.25,0.5]:
        for t in [0.25,0.5,1.0]:
            print('S>=%.2f on (1,1+%.2f]'%(t,d), round(2-dnn_lb(N,M,lambda a:t,1+d),4))
