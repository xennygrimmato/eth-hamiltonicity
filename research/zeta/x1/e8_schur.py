# Idea 4: G_X[m,n] = Lambda(n/m) sqrt(m/n) (n = m k) symmetrised, m,n <= X.  Claim: lambda_max <= log X + O(1)
# (Schur test with p_n = n^{-1/2});  hence  sum_rho w A(rho) conj A(1-conj rho) > 0 for integer Dirichlet
# polynomials of length X <= T^{1-eps}, unconditionally.
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import eigsh
def run(X):
    lam=np.zeros(X+1); sieve=np.ones(X+1,bool)
    for p in range(2,X+1):
        if sieve[p]:
            sieve[2*p::p]=False; q=p
            while q<=X: lam[q]=np.log(p); q*=p
    ks=np.nonzero(lam)[0]; rows=[];cols=[];vals=[]
    for k in ks:
        m=np.arange(1,X//k+1); rows.append(m-1); cols.append(m*k-1); vals.append(np.full(len(m),lam[k]/np.sqrt(k)))
    r=np.concatenate(rows);c=np.concatenate(cols);v=np.concatenate(vals)
    G=sp.coo_matrix((v,(r,c)),shape=(X,X)).tocsr(); G=G+G.T
    p=1/np.sqrt(np.arange(1,X+1)); schur=(G@p/p).max()
    lmax=eigsh(G,k=1,which='LA')[0][0]; lmin=eigsh(G,k=1,which='SA')[0][0]
    print(f"X={X}: lambda_max={lmax:.4f}  log X={np.log(X):.4f}  diff={lmax-np.log(X):.4f}  Schur bound max(Gp/p)={schur:.4f} (diff {schur-np.log(X):.4f})  lambda_min={lmin:.4f}")
for X in [100,1000,10000,100000,400000]: run(X)
