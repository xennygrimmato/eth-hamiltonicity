import numpy as np, itertools, sys
# min rank(Pi_sigma - A x B x C) ?  Pi_sigma cyclic shift of 3 tensor factors of dim N.
def shift(N):
    P=np.zeros((N**3,N**3))
    for i,j,k in itertools.product(range(N),repeat=3):
        P[np.ravel_multi_index((k,i,j),(N,)*3), np.ravel_multi_index((i,j,k),(N,)*3)]=1
    return P
def kron3(A,B,C): return np.kron(np.kron(A,B),C)
def lowrank(M,m):
    U,s,Vt=np.linalg.svd(M); return (U[:,:m]*s[:m])@Vt[:m]
def fitK(T,A,B,C,N):
    # least squares for A given B,C: T ~ A x (B x C): reshape
    def upd(T, X, Y, pos):
        # pos: which factor to solve. Use the identity vec(T)= ... simple: linear LS in entries of the factor.
        n=N*N
        basis=[]
        for p in range(N*N):
            E=np.zeros((N,N)); E.flat[p]=1
            mats=[X,Y]; mats.insert(pos,E)
            basis.append(kron3(*mats).ravel())
        Mb=np.array(basis).T
        coef,*_=np.linalg.lstsq(Mb,T.ravel(),rcond=None)
        return coef.reshape(N,N)
    A=upd(T,B,C,0); B=upd(T,A,C,1); C=upd(T,A,B,2)
    return A,B,C
def run(N,m,restarts=20,iters=400,seed=0):
    rng=np.random.default_rng(seed); P=shift(N); best=np.inf
    for r in range(restarts):
        A,B,C=[rng.standard_normal((N,N)) for _ in range(3)]
        L=np.zeros_like(P)
        for it in range(iters):
            A,B,C=fitK(P-L,A,B,C,N)
            K=kron3(A,B,C); L=lowrank(P-K,m)
            res=np.linalg.norm(P-K-L)/np.linalg.norm(P)
        best=min(best,res)
    return best
for N in (2,3):
    for m in range(0, N**3):
        b=run(N,m,restarts=12 if N==2 else 8,iters=300)
        print(f'N={N} m={m}: min residual {b:.4f}', flush=True)
        if b<1e-6: break
