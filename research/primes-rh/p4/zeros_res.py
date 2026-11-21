# Truncated explicit formula: how short an interval can T zeros certify a prime in?
import mpmath as mp, numpy as np, time, sys
K=int(sys.argv[1]) if len(sys.argv)>1 else 300
t0=time.time(); g=np.array([float(mp.zetazero(k).imag) for k in range(1,K+1)]); 
print("zeros",K,"T=%.1f"%g[-1],"time %.0fs"%(time.time()-t0))
from sympy import primerange
X=10**6
# exact psi via Lambda
N=2*X; lam=np.zeros(N+1)
import sympy
for p in sympy.primerange(2,N+1):
    q=p
    while q<=N: lam[q]+=np.log(p); q*=p
psi=np.cumsum(lam)
rho=0.5+1j*g
def psiT(y, T):
    gg=rho[g<=T]
    # smooth (Fejer) weights to kill Gibbs: (1-gamma/T)
    w=1-gg.imag/T
    return y - 2*np.real(np.sum(w*y**gg/gg)) - np.log(2*np.pi)
for T in [50,200,g[-1]]:
    ys=np.arange(X, X+20000, 50)
    err=np.array([psiT(y,T)-psi[int(y)] for y in ys])
    print("T=%.0f  rms err of smoothed psi_T vs psi on [1e6,1e6+2e4]: %.1f  max %.1f   x/T=%.0f  sqrt(x)=%.0f"%(T,np.sqrt(np.mean(err**2)),np.abs(err).max(),X/T,np.sqrt(X)))
