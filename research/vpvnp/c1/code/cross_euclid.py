# Search for Euclidean violations of the crossing inequality (Prop B.3):
# viol = (A-S1)_+^2/|oo'|^2 + (A-S2)_+^2/|ww'|^2 - 2(p^2+q^2)  (must be <= 0 in any price)
import numpy as np
from scipy.optimize import minimize
rng=np.random.default_rng(0)
def viol(z,d):
    P=z[:8*d].reshape(8,d); al=z[-1]
    p,q=np.cos(al)**2,np.sin(al)**2   # p,q>=0
    x,v,y,u,o,o2,w,w2=P
    n=lambda a,b: np.sqrt(((a-b)**2).sum()+1e-18)
    A=p*n(x,v)+q*n(y,u)
    S1=p*n(x,o)+q*n(y,o)+p*n(v,o2)+q*n(u,o2)
    S2=p*n(x,w)+q*n(u,w)+q*n(y,w2)+p*n(v,w2)
    t1=max(A-S1,0)**2/(n(o,o2)**2); t2=max(A-S2,0)**2/(n(w,w2)**2)
    return (t1+t2)/(p*p+q*q)-2
best=-9
for d in [1,2,3]:
  for trial in range(300):
    z0=np.concatenate([rng.normal(size=8*d),[rng.uniform(0,1.57)]])
    r=minimize(lambda z:-viol(z,d),z0,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-10,'fatol':1e-12})
    if -r.fun>best: best=-r.fun; print(d,trial,best,flush=True)
print('best',best)
