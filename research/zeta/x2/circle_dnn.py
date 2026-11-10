"""Finite (CUE-like) model of Idea 1. N points on circle (with multiplicity), pair measure nu on Z_M.
Data: E|p_k|^2 = k for 1<=k<=K (CUE value min(k,N)), nu^(0)=N^2.  DNN: nu>=0, nu^(k)>=0.
maximise kappa = nu({0})/N.  simple fraction >= 2-kappa."""
import numpy as np, sys
from scipy.optimize import linprog
def dnn(N, K, M):
    j = np.arange(M)
    # variables nu_0..nu_{M-1} >=0 symmetric: use nu_j for j=0..M//2 with multiplicity
    H = M//2
    jj = np.arange(H+1); mult = np.where((jj==0)|((M%2==0)&(jj==H)),1,2)
    ks = np.arange(H+1)
    F = np.cos(2*np.pi*np.outer(ks, jj)/M)*mult   # nu^(k) = F @ nu
    eq_rows = [0]+list(range(1,K+1)); eq_b = [N**2]+[min(k,N) for k in range(1,K+1)]
    A_eq = F[eq_rows]; b_eq = np.array(eq_b,float)
    ub_rows = list(range(K+1,H+1))
    A_ub = -F[ub_rows] if ub_rows else None; b_ub = np.zeros(len(ub_rows)) if ub_rows else None
    cost = np.zeros(H+1); cost[0] = -1
    r = linprog(cost, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=[(0,None)]*(H+1), method='highs')
    return r.x[0]/N, r
if __name__=='__main__':
    for N in [6,8,10,12,16,20,30,40,60]:
        for fac in [8,16]:
            k,_ = dnn(N,N,fac*N)
            print(N, fac, 'kappa_DNN=%.5f  simple>=%.5f'%(k,2-k))
