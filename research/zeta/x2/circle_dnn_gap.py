"""DNN finite model + lower bound on close DISTINCT pairs: (1/N) E #{ordered pairs j!=k distinct points, 0<|x_j-x_k|<g} >= c.
(x in mean-spacing units).  GUE value: int_{-g}^{g} R2 = 2 int_0^g (1 - sinc^2)."""
import numpy as np
from scipy.optimize import linprog
from scipy.integrate import quad
def dnn_gap(N,M,g,c):
    H=M//2; jj=np.arange(H+1); mult=np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    F=np.cos(2*np.pi*np.outer(jj,jj)/M)*mult
    eq=[0]+list(range(1,N+1)); beq=[N**2]+list(range(1,N+1))
    ub=list(range(N+1,H+1)); A=[-F[k] for k in ub]; b=[0.0]*len(ub)
    row=np.zeros(H+1); sel=(jj>0)&(jj*N/M<g); row[sel]=-mult[sel]; A.append(row); b.append(-c*N)
    r=linprog(-np.eye(H+1)[0],A_ub=np.array(A),b_ub=np.array(b),A_eq=F[eq],b_eq=np.array(beq,float),bounds=[(0,None)]*(H+1),method='highs')
    return 2-r.x[0]/N if r.status==0 else np.nan
if __name__=='__main__':
    N=40; M=16*N
    for g in [0.5,0.9]:
        gue=2*quad(lambda x:1-(np.sinc(x))**2,0,g)[0]
        print('g=%.1f GUE mass=%.3f'%(g,gue), ' '.join('c=%.2f:%.4f'%(c,dnn_gap(N,M,g,c)) for c in [0,0.05,0.1,0.2,gue]))
