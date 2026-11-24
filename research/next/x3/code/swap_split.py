# Alternating projections: SWAP_n = R + L, opSR(R) <= r, rank(L) <= s.
import numpy as np, sys
def swap(n):
    S=np.zeros((n*n,n*n))
    for i in range(n):
        for j in range(n): S[i*n+j, j*n+i]=1
    return S
def realign(M,n):  # M[(i,j),(i',j')] -> [(i,i'),(j,j')]
    return M.reshape(n,n,n,n).transpose(0,2,1,3).reshape(n*n,n*n)
def trunc(M,k):
    U,s,Vt=np.linalg.svd(M); return (U[:,:k]*s[:k])@Vt[:k]
def run(n,r,s,iters=3000,restarts=20,seed=0,cplx=False):
    rng=np.random.default_rng(seed); S=swap(n).astype(complex if cplx else float); best=1e9
    for _ in range(restarts):
        L=rng.standard_normal(S.shape)+(1j*rng.standard_normal(S.shape) if cplx else 0); L=trunc(L,s)
        for it in range(iters):
            R=realign(trunc(realign(S-L,n),r),n)   # realign is an involution
            L=trunc(S-R,s)
        res=np.linalg.norm(S-R-L)/np.linalg.norm(S); best=min(best,res)
    return best
if __name__=="__main__":
    n=int(sys.argv[1]); cp=len(sys.argv)>2
    for r in range(1,n*n+1):
        for s in range(0,n*n+1):
            b=run(n,r,s,iters=1500,restarts=8,cplx=cp)
            if b<1e-6: print(f"n={n} r={r}: min s ~ {s} (res {b:.1e})",flush=True); break
        if s==0: break
