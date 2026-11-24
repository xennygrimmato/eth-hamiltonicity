# R_mu = max_B p_mu(B)/p_1(B), p_r(B)=P_{W rank r}(<B,W>=1): bounds D(mu)^2/D(1)^2 for every
# Hilbert-space (Euclidean) pull-back price on Mat_mu(F2).  Exact enumeration.
import numpy as np, itertools, sys
for mu in [2,3,4]:
    N=2**(mu*mu); M=np.array(list(itertools.product([0,1],repeat=mu*mu)),dtype=np.int64).reshape(N,mu,mu)
    rk=np.array([np.linalg.matrix_rank(m) for m in M]) if mu<4 else None
    if mu==4:
        # GF2 rank
        def r2(m):
            m=m.copy()%2; r=0
            for c in range(mu):
                piv=[i for i in range(r,mu) if m[i,c]]
                if not piv: continue
                m[[r,piv[0]]]=m[[piv[0],r]]
                for i in range(mu):
                    if i!=r and m[i,c]: m[i]^=m[r]
                r+=1
            return r
        rk=np.array([r2(m) for m in M])
    else:
        def r2(m):
            m=m.copy()%2; r=0
            for c in range(mu):
                piv=[i for i in range(r,mu) if m[i,c]]
                if not piv: continue
                m[[r,piv[0]]]=m[[piv[0],r]]
                for i in range(mu):
                    if i!=r and m[i,c]: m[i]^=m[r]
                r+=1
            return r
        rk=np.array([r2(m) for m in M])
    F=M.reshape(N,-1)
    W1=F[rk==1]; Wm=F[rk==mu]
    out=[]
    for j in range(1,mu+1):
        B=F[np.argmax(rk==j)]
        p1=((W1@B)%2).mean(); pm=((Wm@B)%2).mean(); out.append((j,p1,pm,pm/p1))
    print(mu,[(j,round(a,4),round(b,4),round(c,4)) for j,a,b,c in out],'R_mu=',max(o[3] for o in out))
