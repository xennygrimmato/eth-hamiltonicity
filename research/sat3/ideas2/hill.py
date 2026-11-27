import sys, math, numpy as np, time
sys.path.insert(0,'/home/user/eth-hamiltonicity/research/sat3')
import podprod
from fullplane import plane, nodepods
q=int(sys.argv[1]); tmax=float(sys.argv[2]); seed=int(sys.argv[3])
rng=np.random.default_rng(seed)
arms0,rho0,(p,H,E,groups)=nodepods(q); nE=len(E)
t0=time.time(); gbest=0
while time.time()-t0<tmax:
    mode=rng.integers(0,3)
    if mode==0:
        J=int(rng.integers(3,9)); arms=rng.integers(0,p+2,size=(J,H)); rho=rng.random((J,H))*(rng.random((J,H))<0.6)
    elif mode==1:
        ex=int(rng.integers(1,4)); arms=np.vstack([arms0,rng.integers(0,p+2,size=(ex,H))]); rho=np.vstack([rho0,0.2*rng.random((ex,H))])
    else:
        arms=arms0.copy(); rho=rho0+0.1*rng.random(rho0.shape)*(rng.random(rho0.shape)<0.3)
    J=arms.shape[0]
    cur=podprod.value(arms,rho,p,E,groups,'avg'); step=0.3; fails=0
    t1=time.time()
    while time.time()-t1<tmax/6 and step>1e-3:
        a2=arms.copy(); r2=rho.copy()
        k=int(rng.integers(1,4))
        for _ in range(k):
            j=rng.integers(0,J); h=rng.integers(0,H)
            if rng.random()<0.3: a2[j,h]=rng.integers(0,p+2)
            r2[j,h]=abs(r2[j,h]+step*rng.normal()) if rng.random()<0.85 else 0.0
        v=podprod.value(a2,r2,p,E,groups,'avg')
        if v>cur+1e-10: arms,rho,cur=a2,r2,v; fails=0
        else:
            fails+=1
            if fails>150: step*=0.6; fails=0
    vmin=podprod.value(arms,rho,p,E,groups,'min')
    gbest=max(gbest,cur/nE)
    print(f"mode {mode} J={J} avg={cur/nE:.5f} min={vmin/nE:.5f} best={gbest:.5f}",flush=True)
