# CUE model of the "enlarged evaluation family": block1 = z^j (d1 freqs), block2 = P'(z)M_y(z) z^j (d2 freqs),
# M_y = mollifier of length y approximating 1/P.  rho=(E tr G)^2/(N E tr G^2), G = Gram over zeros.
import numpy as np, sys
from scipy.stats import unitary_group
rng=np.random.default_rng(0)
N=int(sys.argv[1]); S=int(sys.argv[2])
def dirich(D,d):
    with np.errstate(divide='ignore',invalid='ignore'):
        k=np.sin(d*D/2)/np.sin(D/2)
    k[np.isclose(np.sin(D/2),0)]=d
    return k
data=[]
for s in range(S):
    U=unitary_group.rvs(N,random_state=rng)
    z=np.linalg.eigvals(U); z=z[np.argsort(np.angle(z))]
    # P(x)=prod(1-x/z_c); 1/P = sum h_k x^k, h = complete homogeneous in 1/z
    e=np.poly(1/z)        # prod (x-1/z) coefficients -> P(x)=prod(1-x/z): coefficients c_k of x^k
    c=np.array([np.prod(1.0)]) ; 
    coef=np.polynomial.polynomial.polyfromroots(z)  # prod (x - z_c)
    coef=coef/coef[0]                               # P(x)=prod(1-x/z_c), coef[k] x^k
    h=np.zeros(N+1,complex); h[0]=1
    for k in range(1,N+1):
        h[k]=-np.sum(coef[1:k+1]*h[k-1::-1][:k])
    dP=np.array([-1/z[a]*np.prod(1-z[a]/np.delete(z,a)) for a in range(N)])  # P'(z_a)
    data.append((z,h,dP))
def rho(th1,th2,thM,c):
    a=b=0; y=int(round(thM*N)); d1=int(round(th1*N)); d2=int(round(th2*N))
    for z,h,dP in data:
        t=np.angle(z); D=t[:,None]-t[None,:]
        G=dirich(D,d1).astype(complex) if d1>0 else np.zeros((N,N),complex)
        if d2>0:
            if y>0:
                k=np.arange(y+1); M=np.array([np.sum(h[:y+1]*(1-k/y)*za**k) for za in z])
            else: M=np.ones(N)
            f=z*dP*M
            G=G+c*np.outer(f,f.conj())*dirich(D,d2)
        a+=np.trace(G).real; b+=np.sum(np.abs(G)**2)
    a/=len(data); b/=len(data)
    return a*a/(N*b)
def best(th1,th2,thM):
    # c scale: normalise by mean |f|^2 computed on first sample
    z,h,dP=data[0]; y=int(round(thM*N)); k=np.arange(y+1)
    M=np.array([np.sum(h[:y+1]*(1-k/max(y,1))*za**k) for za in z]) if y>0 else np.ones(N)
    sc=1/np.mean(np.abs(z*dP*M)**2)
    return max((rho(th1,th2,thM,c*sc),c) for c in [0.05,0.1,0.2,0.4,0.7,1.0,1.5,2.5])
print("N",N,"samples",S)
print("only block2 (th1=0): thM th2 rho")
for thM in [0.25,0.5,1.0]:
    for th2 in [0.25,0.5,1.0]:
        print(thM,th2,round(rho(0,th2,thM,1.0),4))
print("both blocks: th1 th2 thM  rho  c*")
for th1 in [0.5,1.0]:
    for th2,thM in [(0.25,0.25),(0.5,0.25),(0.25,0.5),(0.5,0.5),(0.5,1.0),(1.0,1.0)]:
        r,c=best(th1,th2,thM); print(th1,th2,thM,round(r,4),c)
