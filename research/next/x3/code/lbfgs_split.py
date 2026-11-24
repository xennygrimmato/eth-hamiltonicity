# SWAP_n = sum_b X_b (x) Y_b + sum_c u_c v_c^T, least squares by L-BFGS over factors (real).
import numpy as np, sys
from scipy.optimize import minimize
from swap_split import swap
def solve(n,r,s,restarts=10,seed=0):
    S=swap(n); N=n*n; best=1e9; rng=np.random.default_rng(seed)
    def unpack(z):
        i=0; X=z[i:i+r*N].reshape(r,n,n); i+=r*N; Y=z[i:i+r*N].reshape(r,n,n); i+=r*N
        U=z[i:i+s*N].reshape(s,N); i+=s*N; V=z[i:i+s*N].reshape(s,N); return X,Y,U,V
    def f(z):
        X,Y,U,V=unpack(z)
        R=np.einsum('bij,bkl->ikjl',X,Y).reshape(N,N)
        E=R+U.T@V-S
        gR=E.reshape(n,n,n,n)  # [i,k,j,l]
        gX=2*np.einsum('ikjl,bkl->bij',gR,Y); gY=2*np.einsum('ikjl,bij->bkl',gR,X)
        gU=2*(V@E.T); gV=2*(U@E)
        return (E*E).sum(), np.concatenate([gX.ravel(),gY.ravel(),gU.ravel(),gV.ravel()])
    for _ in range(restarts):
        z=rng.standard_normal(2*r*N+2*s*N)*0.5
        res=minimize(f,z,jac=True,method='L-BFGS-B',options={'maxiter':20000,'ftol':1e-30,'gtol':1e-14})
        best=min(best,np.sqrt(res.fun)/n)
        if best<1e-8: break
    return best
if __name__=="__main__":
    n=int(sys.argv[1])
    for k in map(int,sys.argv[2].split(',')):
        print(f"n={n} r=s={k} res={solve(n,k,k,restarts=int(sys.argv[3])):.2e}",flush=True)
