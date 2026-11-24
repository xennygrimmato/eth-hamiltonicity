# [N] Check of Theorem B (Crofton reduction): for random configurations and random hubs,
#   saving_S/|oo'| <= E_{x in [o,o'] uniform} [ 1/2 u.W~_S(x) - P(x,u) ],
# where W~_S(x) = sum_i (-eps_i) (p_i-x)/|p_i-x| (eps=+1 on S-side ends) and P(x,u) = sum_e Pr[wire e
# not cut by a hyperplane through x with normal theta ~ |theta.u| dtheta]; estimated by Monte Carlo.
# Also checks the exact identity L = E_theta F_S(X).
import numpy as np, itertools
rng=np.random.default_rng(5)
def trial(k,d,nth=20000,nx=40):
    edges=[(a,b) for a in range(k) for b in range(a+1,k)]
    P=rng.normal(size=(2*len(edges),d)); node=np.array([x for e in edges for x in e])
    S=set(rng.choice(k,size=k//2,replace=False).tolist())
    eps=np.array([1 if node[i] in S else -1 for i in range(len(node))])
    o=rng.normal(size=d)*0.5; op=o+rng.normal(size=d)*rng.uniform(0.01,2)
    sav=sum(np.linalg.norm(P[2*e]-P[2*e+1]) for e in range(len(edges)))
    sav-=sum(np.linalg.norm(P[i]-(o if eps[i]==1 else op)) for i in range(len(node)))
    v=op-o; h=np.linalg.norm(v); u=v/h
    th=rng.normal(size=(nth,d)); th/=np.linalg.norm(th,axis=1)[:,None]; w=np.abs(th@u); w/=w.sum()
    sg=np.sign(th@u)
    L1=0; L2=0
    for lam in (np.arange(nx)+0.5)/nx:
        x=o+lam*v
        s=np.sign((P-x)@th.T)*sg            # +1: o'-side
        U=(P-x)/np.linalg.norm(P-x,axis=1)[:,None]
        lin=0.5*u@(-(eps[:,None]*U).sum(0))
        unc=sum((w*(1+s[2*e]*s[2*e+1])/2).sum() for e in range(len(edges)))
        L1+=(lin-unc)/nx
        # direct E F_S(X)
        F=np.zeros(nth)
        for e,(a,b) in enumerate(edges):
            i,j=2*e,2*e+1
            if eps[i]!=eps[j]:
                p,q=(i,j) if eps[i]==1 else (j,i)
                F+=np.where((s[p]<0)&(s[q]>0),1,-1)
            else:
                wrong=1 if eps[i]==1 else -1
                F+=np.where((s[i]==wrong)&(s[j]==wrong),-2,0)
        L2+=(w*F).sum()/nx
    return sav/h,L1,L2
for k in (4,5,6):
    for t in range(4):
        r,L1,L2=trial(k,k)
        print(f"k={k} ratio={r:8.4f}  avg L (formula)={L1:8.4f}  avg E F={L2:8.4f}  ok={r<=L1+0.05}")
