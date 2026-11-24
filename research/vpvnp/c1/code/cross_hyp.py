# Crossing inequality (Prop B.3) in the hyperbolic plane (curvature -kappa), continuous search.
import numpy as np, sys
from scipy.optimize import minimize
rng=np.random.default_rng(1)
def hd(a,b):  # hyperboloid model from R^2 coords
    A=np.array([np.sqrt(1+a@a),*a]); B=np.array([np.sqrt(1+b@b),*b])
    return np.arccosh(max(A[0]*B[0]-A[1:]@B[1:],1.0))
def viol(z,sc):
    Pt=z[:16].reshape(8,2)*sc; al=z[-1]; p,q=np.cos(al)**2,np.sin(al)**2
    x,v,y,u,o,o2,w,w2=Pt; n=hd
    A=p*n(x,v)+q*n(y,u)
    S1=p*n(x,o)+q*n(y,o)+p*n(v,o2)+q*n(u,o2)
    S2=p*n(x,w)+q*n(u,w)+q*n(y,w2)+p*n(v,w2)
    t1=max(A-S1,0)**2/(n(o,o2)**2+1e-18); t2=max(A-S2,0)**2/(n(w,w2)**2+1e-18)
    return (t1+t2)/(p*p+q*q)-2
best=-9
for sc in [0.3,1,3,10]:
  for t in range(150):
    z0=np.concatenate([rng.normal(size=16),[rng.uniform(0,1.57)]])
    r=minimize(lambda z:-viol(z,sc),z0,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-10,'fatol':1e-13})
    if -r.fun>best: best=-r.fun; print(sc,t,best,flush=True)
print('best',best)
