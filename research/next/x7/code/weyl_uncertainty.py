"""Check: for A_f = sum_s f(s) W_s (x) W_s^dag on C^N (x) C^N (W_s Weyl ops), the three pairing ranks of the
4-index tensor A[x,y,u,v] (A as map (u,v)->(x,y)) are
  row  = rank of A as N^2 x N^2 matrix
  col  = operator-Schmidt rank (realignment)            claim: = |supp f|
  third= rank of partial transpose A^Gamma             claim: = |supp of symplectic FT of f|
Donoho-Stark => col*third >= N^2 for every f.  Random sparse f and coset indicators."""
import numpy as np, itertools, sys
rng=np.random.default_rng(1)
def weyl(N):
    w=np.exp(2j*np.pi/N); X=np.roll(np.eye(N),1,axis=0); Z=np.diag(w**np.arange(N))
    return {(a,b):np.linalg.matrix_power(X,a)@np.linalg.matrix_power(Z,b) for a in range(N) for b in range(N)}
def rk(M,tol=1e-8): s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def ranks(A,N):
    T=A.reshape(N,N,N,N)            # T[x,y,u,v]
    row=rk(T.reshape(N*N,N*N))
    col=rk(T.transpose(0,2,1,3).reshape(N*N,N*N))   # (x,u)|(y,v)
    thr=rk(T.transpose(0,3,2,1).reshape(N*N,N*N))   # (x,v)|(u,y)
    return row,col,thr
for N in [2,3,4,5]:
    W=weyl(N); keys=list(W); bad=0; minprod=10**9; out=[]
    for trial in range(60):
        k=rng.integers(1,N*N+1); S=rng.choice(len(keys),k,replace=False)
        f=np.zeros((N,N),complex)
        for i in S: f[keys[i]]=rng.normal()+1j*rng.normal()
        if trial%3==0: f=(np.abs(f)>0).astype(complex)  # indicators
        A=sum(f[s]*np.kron(W[s],W[s].conj().T) for s in keys)
        r,c,t=ranks(A,N)
        F=np.fft.fft2(f); sF=int((np.abs(F)>1e-8).sum())
        if c!=int((np.abs(f)>0).sum()) or t!=sF: bad+=1
        minprod=min(minprod,c*t); out.append((r,c,t))
    print(f"N={N}: identity col=|supp f|, third=|supp FT f| violated in {bad}/60 trials; min col*third={minprod} (N^2={N*N}); sample (row,col,third)={out[:6]}")
