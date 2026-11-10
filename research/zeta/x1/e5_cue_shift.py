# CUE: blocks with twist f_a = P(z_a e^{i delta}) M_y(z_a e^{i delta})  (shifted mollified char poly),
# or unmollified P(z_a e^{i delta}) (thM=0).  Gram G = D_{d1} + sum_b c_b f_b f_b^* .* D_{d2}
import numpy as np, sys, itertools
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
    coef=np.polynomial.polynomial.polyfromroots(z); coef=coef/coef[0]
    h=np.zeros(N+1,complex); h[0]=1
    for k in range(1,N+1): h[k]=-np.sum(coef[1:k+1]*h[k-1::-1][:k])
    data.append((z,coef,h))
def fvec(z,coef,h,delta,y):
    x=z*np.exp(1j*delta)
    P=np.polynomial.polynomial.polyval(x,coef)
    if y>0:
        k=np.arange(y+1); M=np.polynomial.polynomial.polyval(x,h[:y+1]*(1-k/y))
    else: M=1
    return P*M
def rho(th1,blocks):  # blocks: list of (delta_in_spacings, thM, th2, c)
    a=b=0
    for z,coef,h in data:
        t=np.angle(z); D=t[:,None]-t[None,:]
        G=dirich(D,int(round(th1*N))).astype(complex)
        for (dl,thM,th2,c) in blocks:
            f=fvec(z,coef,h,2*np.pi*dl/N,int(round(thM*N)))
            G=G+c*np.outer(f,f.conj())*dirich(D,int(round(th2*N)))
        a+=np.trace(G).real; b+=np.sum(np.abs(G)**2)
    a/=len(data); b/=len(data)
    return a*a/(N*b)
print("N",N,"baseline th1=1:",round(rho(1.0,[]),4), " th1=0.5:",round(rho(0.5,[]),4))
for th1 in [1.0,0.5]:
  for thM in [0.0,0.25,0.5]:
    for th2 in [0.25,0.5]:
      best=(0,)
      for dl in [0.25,0.5,0.75,1.0]:
        z,coef,h=data[0]; sc=1/np.mean(np.abs(fvec(z,coef,h,2*np.pi*dl/N,int(round(thM*N))))**2)
        for c in [0.1,0.3,0.6,1.0,2.0]:
            r=rho(th1,[(dl,thM,th2,c*sc),(-dl,thM,th2,c*sc)])
            best=max(best,(r,dl,c))
      print("th1",th1,"thM",thM,"th2",th2,"best rho %.4f at delta=%.2f c=%.1f"%best)
