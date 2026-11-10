# E2: the Hermite-Toeplitz matrix K_M[i,j]=k((i-j)h), k(v)=sum_gamma w(gamma) e^{i v gamma},
# computed (a) from zeros, (b) from primes via the Guinand-Weil explicit formula. Then inertia.
import numpy as np, sys, mpmath
from scipy.special import ndtr, digamma
from scipy.linalg import toeplitz
g=np.load("zeros.npy")
a,b,H=float(sys.argv[1]),float(sys.argv[2]),float(sys.argv[3]); theta=float(sys.argv[4]); delta=0.15
w=lambda t: ndtr((t-a)/H)-ndtr((t-b)/H)
Tm=(a+b)/2; L=np.log(Tm/2/np.pi); U=theta*L
per=(b-a+16*H); h=2*np.pi/per/(1+delta)*1.0; M=int(U/h)
v=np.arange(M)*h
sel=(g>a-8*H)&(g<b+8*H); gz=g[sel]; wz=w(gz)
Nw=wz.sum(); Nhard=((gz>a-6*H)&(gz<b+6*H)).sum()
kz=(wz[None,:]*np.exp(1j*v[:,None]*gz[None,:])).sum(1)
# prime side
def W(xi):
    xi=np.asarray(xi,float); out=np.empty(xi.shape,complex)
    sm=np.abs(xi)<1e-12
    out[~sm]=np.exp(-H*H*xi[~sm]**2/2)*(np.exp(1j*xi[~sm]*b)-np.exp(1j*xi[~sm]*a))/(1j*xi[~sm])
    out[sm]=b-a
    return out
t=np.arange(a-10*H,b+10*H,0.05)
gam=(digamma(0.25+0.5j*t).real-np.log(np.pi))*w(t)
kp=np.array([np.trapezoid(gam*np.exp(1j*vv*t),t) for vv in v])/(2*np.pi)
nmax=int(np.exp(U+8/H))+2
lam=np.zeros(nmax+1)
sieve=np.ones(nmax+1,bool); sieve[:2]=False
for p in range(2,nmax+1):
    if sieve[p]:
        sieve[2*p::p]=False
        q=p
        while q<=nmax: lam[q]=np.log(p); q*=p
for n in np.nonzero(lam)[0]:
    kp-= lam[n]/np.sqrt(n)/(2*np.pi)*(W(v-np.log(n))+W(v+np.log(n)))
print(f"window[{a},{b}] H={H} theta={theta} U={U:.3f} X=e^U={np.exp(U):.0f} primes<= {nmax}  M={M}  Nw={Nw:.2f} Nhard={Nhard}")
print("max|k_zero-k_prime| =",np.abs(kz-kp).max(), "  k(0)=",kz[0].real)
for name,k in (("zeros",kz),("primes",kp)):
    K=toeplitz(k.conj())    # K[i,j]=k((i-j)h): first column k(v_i - 0); Hermitian
    K=(K+K.conj().T)/2
    ev=np.linalg.eigvalsh(K)
    eps=1e-6*ev.max()
    npos=(ev>eps).sum(); nneg=(ev<-eps).sum()
    tr=ev.sum(); hs=(ev**2).sum(); lamn=ev*Nw/tr; print("   normalised moments m2,m3,m4 =",[round(float((lamn**k).sum()/Nw),4) for k in (2,3,4)])
    print(f"{name}: n_+={npos} n_-={nneg} min ev={ev.min():.3e} max={ev.max():.3e}  rank-trace (tr)^2/HS={tr*tr/hs:.1f} ({tr*tr/hs/Nw:.4f} Nw)"
          f"  => simple-on-line >= 2n_+-N = {2*npos-Nhard} ({(2*npos-Nhard)/Nhard:.4f}),  CS version {(2*tr*tr/hs-Nhard)/Nhard:.4f}")
