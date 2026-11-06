"""Cross-check of the component reduction: full system over all n coordinates vs component system,
mod p vs exact over Q, on random small designs with mixed rows."""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import occ_system, rank_modp, rank_exact, min_R_occ, feasible
def full_feasible(design, e, v, R, n):
    Q=design['Q']; part, alpha, rows = design['part'], design['alpha'], design['rows']
    mu={}
    for t in range(Q):
        for h in range(len(rows[t])):
            if h==alpha[t][e]: continue
            for j in range(len(rows[t][h])): mu[(t,h,j)]=len(mu)
    N=n*R+len(mu); A=[]; b=[]
    for t in range(Q):
        for i in range(n):
            h=part[t][i]
            if h==alpha[t][e]: continue
            row=[0]*N
            for k in range(1,R+1): row[i*R+k-1]=(t+1)**k
            for j,rw in enumerate(rows[t][h]):
                if i in rw: row[n*R+mu[(t,h,j)]]=-rw[i]
            A.append(row); b.append(-1 if i==v else 0)
    if N==0: return all(x==0 for x in b)
    Ab=[r+[bb] for r,bb in zip(A,b)]
    return rank_exact(A)==rank_exact(Ab)
rng=random.Random(5); bad=0; tot=0; hist={}
for trial in range(60):
    n=8; Q=rng.choice([3,4,5]); r=2
    part=[]; 
    for t in range(Q):
        p=list(range(n)); rng.shuffle(p); g=[0]*n
        for k,v in enumerate(p): g[v]=k*r//n
        part.append(g)
    clauses=[(0,1,2),(2,3,4),(4,5,6),(6,7,0)]
    alpha=[[rng.randrange(r) for _ in clauses] for t in range(Q)]
    rows=[]
    for t in range(Q):
        rt=[]
        for h in range(r):
            mem=[v for v in range(n) if part[t][v]==h]
            rl=[]
            for _ in range(rng.choice([0,1,2])):
                rl.append({x:rng.choice([-2,-1,1,2]) for x in mem if rng.random()<0.6} or {mem[0]:1})
            rt.append(rl)
        rows.append(rt)
    des={'Q':Q,'part':part,'alpha':alpha,'rows':rows}
    for e,c in enumerate(clauses):
        for v in c:
            for R in range(0,Q+1):
                a=feasible(des,e,v,R); b2=feasible(des,e,v,R,exact=True); c2=full_feasible(des,e,v,R,n)
                tot+=1
                if not (a==b2==c2): bad+=1
            m=min_R_occ(des,e,v); hist[m]=hist.get(m,0)+1
print("checks",tot,"disagreements",bad,"minR histogram",sorted(hist.items()))
