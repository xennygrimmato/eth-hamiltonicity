import sys, itertools, math, numpy as np
sys.path.insert(0,'/home/user/eth-hamiltonicity/research/sat3')
import podprod
from scipy.optimize import minimize

def gf(q):
    if q in (2,3,5,7):
        return list(range(q)), (lambda a,b:(a+b)%q), (lambda a,b:(a*b)%q)
    if q==4:
        mul=[[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
        return list(range(4)), (lambda a,b:a^b), (lambda a,b:mul[a][b])
    if q==8:
        def mul(a,b):
            r=0
            for i in range(3):
                if (b>>i)&1: r^=a<<i
            for i in (4,3):
                if (r>>i)&1: r^=0b1011<<(i-3)
            return r
        return list(range(8)), (lambda a,b:a^b), mul

def plane(q, ncls=None):
    F,add,mul=gf(q)
    nodes=[(x,y) for x in F for y in F]
    # classes: slope t: line id = y + t*x ; slope inf: x
    cls=[(lambda n,t=t: add(n[1],mul(t,n[0]))) for t in F]+[lambda n:n[0]]
    if ncls: cls=cls[:ncls-1]+[cls[-1]] if ncls<len(cls) else cls
    p=len(cls)
    hub={}
    for k in range(p):
        for g in F: hub[(k,g)]=len(hub)
    E=[]
    for a,b in itertools.combinations(nodes,2):
        E.append(([hub[(k,cls[k](a))] for k in range(p)],[hub[(k,cls[k](b))] for k in range(p)]))
    groups=[[hub[(k,g)] for g in F] for k in range(p)]
    return p,len(hub),E,groups,nodes,cls,hub

def nodepods(q,ncls=None,extra_lines=0):
    p,H,E,groups,nodes,cls,hub=plane(q,ncls)
    J=len(nodes)
    arms=np.zeros((J,H),dtype=int); rho=np.zeros((J,H))
    for j,n in enumerate(nodes):
        for k in range(p):
            h=hub[(k,cls[k](n))]; arms[j,h]=k+1; rho[j,h]=1.0
    return arms,rho,(p,H,E,groups)

if __name__=='__main__':
    q=int(sys.argv[1]); ncls=int(sys.argv[2]) if len(sys.argv)>2 else None
    arms,rho,(p,H,E,groups)=nodepods(q,ncls)
    nE=len(E)
    for mode in ('avg','min'):
        v=podprod.value(arms,rho,p,E,groups,mode)
        print(f"q={q} p={p} E={nE} node-pods {mode}: {v/nE:.5f}")
    # flat symmetric: one line factor per (class, hub) simplex -> use J=H lines: hub h at +1 on arm 0 in factor h
    arms2=np.zeros((H,H),dtype=int); rho2=np.eye(H)
    v=podprod.value(arms2,rho2,p,E,groups,'avg'); print(f"  flat simplex avg: {v/nE:.5f}  formula sqrt(g)/(g+1)={math.sqrt(q)/(q+1):.5f} (full plane) ; 1/sqrt2={1/math.sqrt(2):.5f}; cap={math.sqrt(q/(2*(q+1))):.5f}")
