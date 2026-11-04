import numpy as np, sys
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, hstack, vstack, identity, eye
A=np.load('A.npy'); h=np.load('h.npy'); C=np.load('C.npy')
n=len(A); th=float(sys.argv[1]); mode=sys.argv[2] if len(sys.argv)>2 else 'theta'
if mode=='min': w=2.0**np.minimum(C[:,0],C[:,1])
else: w=2.0**(th*C[:,0]+(1-th)*C[:,1])
M=8.0
c=np.concatenate([np.zeros(n),w])
Aeq=hstack([csr_matrix(A.T),csr_matrix((A.shape[1],n))])
I=eye(n)
L1=hstack([I,-M*I]); L2=hstack([-I,-M*I])
cons=[LinearConstraint(Aeq,h,h),LinearConstraint(vstack([L1,L2]),-np.inf,0)]
integ=np.concatenate([np.zeros(n),np.ones(n)])
b=Bounds(np.concatenate([-M*np.ones(n),np.zeros(n)]),np.concatenate([M*np.ones(n),np.ones(n)]))
r=milp(c,constraints=cons,integrality=integ,bounds=b,options={'time_limit':float(sys.argv[3]) if len(sys.argv)>3 else 200,'disp':False})
print(r.status,r.message,'obj',r.fun, 'bound', getattr(r,'mip_dual_bound',None))
if r.x is not None:
    z=r.x[n:]>0.5; al=r.x[:n]
    sel=np.where(z)[0]
    for i in sel: print(i,tuple(C[i]),round(al[i],4),w[i])
    np.save('sol_%s_%s.npy'%(mode,th),sel)
