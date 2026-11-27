import sys, math, numpy as np
sys.path.insert(0,'/home/user/eth-hamiltonicity/research/sat3')
import podprod
from fullplane import plane, nodepods
for q in (3,4,5):
    arms0,rho0,(p,H,E,groups)=nodepods(q); nE=len(E)
    best=(0,None)
    for t in (0,0.2,0.4,0.6,0.8,1.0,1.5,2.5):
        arms=np.vstack([arms0,np.zeros((H,H),dtype=int)]); rho=np.vstack([rho0,t*np.eye(H)])
        v=podprod.value(arms,rho,p,E,groups,'avg')/nE
        best=max(best,(v,('pods+flat',t)))
    # node pods with hubs of lines through node at radius 1 and other hubs at radius r on a common extra arm 0 (centre shift)
    for r in (0.1,0.3,0.6):
        rho=rho0.copy(); rho[rho==0]=r
        v=podprod.value(arms0,rho,p,E,groups,'avg')/nE
        best=max(best,(v,('pods+offcentre',r)))
    print(q, 'node-pods', round(math.sqrt(2*q-2)/(q+1),5), 'best family', best, 'pair-cap', round(q/((q+1)*math.sqrt(2)),5))
