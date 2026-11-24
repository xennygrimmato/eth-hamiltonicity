# Crossing inequality (Prop B.3) for the rank metric rho(a,b)=sqrt(rk(a-b)) on Mat_mu(F2),
# with all 8 points (ends and hubs) taken in Mat_mu(F2).  Hill-climb for a violation.
import numpy as np, itertools, sys
mu=int(sys.argv[1]); N=2**(mu*mu)
def rank2(m):
    rows=[(m>>(mu*i))&((1<<mu)-1) for i in range(mu)]; r=0
    for c in range(mu):
        piv=None
        for i in range(r,mu):
            if rows[i]>>c&1: piv=i;break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        for i in range(mu):
            if i!=r and rows[i]>>c&1: rows[i]^=rows[r]
        r+=1
    return r
RK=np.array([rank2(m) for m in range(N)]); D=np.sqrt(RK)
al=np.linspace(0,np.pi/2,181); P=np.cos(al); Q=np.sin(al)
def viol(t):
    x,v,y,u,o,o2,w,w2=t; d=lambda a,b:D[a^b]
    A=P*d(x,v)+Q*d(y,u)
    S1=P*d(x,o)+Q*d(y,o)+P*d(v,o2)+Q*d(u,o2)
    S2=P*d(x,w)+Q*d(u,w)+Q*d(y,w2)+P*d(v,w2)
    def term(E,h):
        E=np.maximum(E,0)
        if h==0: return np.where(E>1e-12,np.inf,0.)
        return E**2/h**2
    val=term(A-S1,d(o,o2))+term(A-S2,d(w,w2))-2
    return val.max()
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 0)
best=-9
for it in range(int(sys.argv[3]) if len(sys.argv)>3 else 200):
    t=list(rng.integers(0,N,8)); t[0]=0; cur=viol(t)
    improved=True
    while improved:
        improved=False
        for i in range(1,8):
            for m in rng.permutation(N)[:N if N<=512 else 512]:
                t2=t.copy(); t2[i]=int(m); vv=viol(t2)
                if vv>cur+1e-12: t,cur,improved=t2,vv,True
    if cur>best: best=cur; print(it,best,t,[RK[a^b] for a,b in itertools.combinations(t,2)],flush=True)
print('best',best)
