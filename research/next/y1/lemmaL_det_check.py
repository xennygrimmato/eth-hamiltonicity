# Sanity check of Lemma L (reduced case, Sec. 4.2 of notebook.md) on Z(det_N).
# NP-verifier: exists w with X w = 0, c.w = 1 (generically reduced, defect 0).
# Chord-Newton tracking of the d=N branches t_j(A+T*U) of det(A+T*U+t*B)=0 in C[[T]]/T^{d+1}
# (U a random numeric direction; identity is polynomial in U so this tests it), then compare
# det(B)*prod_j(-t_j) with det(A+T*U) mod T^{d+1}. Truncated power series = numpy arrays of length d+1.
import numpy as np
rng=np.random.default_rng(1); N=4; d=N
A,B,U=(rng.standard_normal((N,N))+1j*rng.standard_normal((N,N)) for _ in range(3)); c=rng.standard_normal(N)
def mul(a,b): return np.convolve(a,b)[:d+1]
def ser(const,lin=None):
    s=np.zeros(d+1,complex); s[0]=const
    if lin is not None: s[1]=lin
    return s
X=[[ser(A[i,j],U[i,j]) for j in range(N)] for i in range(N)]
def G(z):  # z = list of series [t, w_1..w_N]
    t=z[0]; w=z[1:]; out=[]
    for i in range(N):
        acc=ser(0)
        for j in range(N): acc=acc+mul(X[i][j]+t*B[i,j],w[j])
        out.append(acc)
    out.append(sum(c[j]*w[j] for j in range(N))-ser(1)); return out
# base points: roots of det(A+tB)=0 <=> eigenvalues of -B^{-1}A
ts=np.linalg.eigvals(-np.linalg.solve(B,A)); prod=ser(1)
for tj in ts:
    M=A+tj*B; w=np.linalg.solve(np.vstack([M[:N-1],c]),np.r_[np.zeros(N-1),1])
    J=np.zeros((N+1,N+1),complex); J[:N,0]=B@w; J[:N,1:]=M; J[N,1:]=c; Ji=np.linalg.inv(J)
    z=[ser(tj)]+[ser(x) for x in w]
    for _ in range(d+1):
        g=G(z); z=[z[k]-sum(Ji[k,l]*g[l] for l in range(N+1)) for k in range(N+1)]
    prod=mul(prod,-z[0])
lhs=np.linalg.det(B)*prod
# exact det(A+T U) coefficients via interpolation in T (degree N)
pts=np.exp(2j*np.pi*np.arange(N+1)/(N+1)); vals=[np.linalg.det(A+p*U) for p in pts]
rhs=np.fft.fft(vals)[::1]/(N+1); rhs=np.array([np.mean([v*p**(-k) for v,p in zip(vals,pts)]) for k in range(N+1)])
print('Lemma L det check, N=%d: max |coef diff| = %.3e (coef sizes ~ %.1e)'%(N,np.max(np.abs(lhs-rhs)),np.max(np.abs(rhs))))
