# E1: Hermite-Toeplitz signature inequality on synthetic conjugate-symmetric "zero sets".
# K = sum_g w v_g v_{conj g}^*, v_g(u)=exp(i u g).  Claim: n_+(K) <= r_d + p, n_-(K) <= p,
# hence  (#simple real) >= 2 n_+ - N.
import numpy as np
rng=np.random.default_rng(1)
bad=0
for trial in range(400):
    r=rng.integers(0,12); p=rng.integers(0,8); dbl=rng.integers(0,3)
    real=list(rng.uniform(0,20,r)); 
    dblz=list(rng.uniform(0,20,dbl))
    pairs=[(rng.uniform(0,20), rng.uniform(0.01,0.5)) for _ in range(p)]
    N=r+2*dbl+2*p
    M=rng.integers(2,30); U=rng.uniform(0.5,6); u=np.linspace(0,U,M)
    K=np.zeros((M,M),complex)
    for g in real: v=np.exp(1j*u*g); K+=np.outer(v,v.conj())
    for g in dblz: v=np.exp(1j*u*g); K+=2*np.outer(v,v.conj())
    for x,y in pairs:
        g=x+1j*y; v=np.exp(1j*u*g); vb=np.exp(1j*u*np.conj(g))
        K+=np.outer(v,vb.conj())+np.outer(vb,v.conj())
    ev=np.linalg.eigvalsh((K+K.conj().T)/2); tol=1e-9*max(1,abs(ev).max())
    npos=(ev>tol).sum(); nneg=(ev<-tol).sum()
    if npos>r+dbl+p or nneg>p or r<2*npos-N: bad+=1
print("violations:",bad,"of 400")
