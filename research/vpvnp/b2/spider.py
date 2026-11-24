# Far-regime hub bound on SPIDER (star-tree) metrics: legs at the far ends of arms, hubs at (arm, radius).
# Gain of leg l at hub h = +s if same arm, -s otherwise; hub-pair distance = s1+s2 (diff arms) or |s1-s2|.
import numpy as np, itertools
nodes=[(r,c) for r in range(3) for c in range(3)]
tri={v:(v[0]+v[1])%3 for v in nodes}
legs=[(u,v) for u in nodes for v in nodes if u!=v and tri[u]==tri[v]]
mf=[lambda v:v[0],lambda v:v[1],lambda v:(v[0]-v[1])%3]
def val(la,ha,hs,ks):
    tot=0
    for j,k in enumerate(ks):
        g=0
        for i,(u,v) in enumerate(legs):
            G=mf[k](u); g+= hs[j,G] if la[i]==ha[j,G] else -hs[j,G]
        # edge requires legs on different arms (else edge length not 2A); penalise
        dm=max((hs[j,a]+hs[j,b]) if ha[j,a]!=ha[j,b] else abs(hs[j,a]-hs[j,b]) for a,b in itertools.combinations(range(3),2))
        if dm<1e-9: continue
        tot+=max(0,g/dm)
    # legs of one edge on same arm: edge length shorter -> invalid; enforce
    for i,(u,v) in enumerate(legs):
        if la[i]==la[legs.index((v,u))]: return -1
    return tot
rng=np.random.default_rng(0); ks=[0,1,2]; best=0
for A in (3,4,6,9):
  for t in range(300):
    la=rng.integers(A,size=18); ha=rng.integers(A,size=(3,3)); hs=rng.random((3,3))
    cur=val(la,ha,hs,ks)
    for it in range(3000):
        la2,ha2,hs2=la.copy(),ha.copy(),hs.copy()
        x=rng.integers(3)
        if x==0: la2[rng.integers(18)]=rng.integers(A)
        elif x==1: ha2[rng.integers(3),rng.integers(3)]=rng.integers(A)
        else: hs2[rng.integers(3),rng.integers(3)]=max(0,hs2[0,0]*0+rng.random())
        v=val(la2,ha2,hs2,ks)
        if v>=cur: la,ha,hs,cur=la2,ha2,hs2,v
    if cur>best: best=cur; print(A,t,round(best,4),flush=True)
print('BEST',best)
