"""Tropical game for the 3x3 level: can a profile of row/column terms with cost exponent <= KAPPA
satisfy every lossy single-flattening inequality (keep/fix/pair contractions, §7.3)?
Adversary: ILP over edge flows (paths) + end sides; Prover: set cover over bond-exponent triples."""
import itertools, sys, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
KAPPA=int(sys.argv[1]) if len(sys.argv)>1 else 8
G=3
nodes=[(r,c) for r in range(G) for c in range(G)]; nid={v:i for i,v in enumerate(nodes)}
edges=[(nid[(r,c)],nid[(s,d)]) for (r,c) in nodes for (s,d) in nodes if r<s and c!=d]
assert len(edges)==18
rows=[v[0] for v in nodes]; cols=[v[1] for v in nodes]
pairs=[(0,1),(0,2),(1,2)]
# nontrivial labellings of 3 classes -> {0,1}
labs=[l for l in itertools.product([0,1],repeat=3) if len(set(l))==2]
def crossing(l): return [i for i,(p,q) in enumerate(pairs) if l[p]!=l[q]]
# a term: (typ, e) typ 0=row,1=col, e = exponents on pairs
def bound(typ,e,a,b):
    # min over nontrivial labellings of s + e(sigma); s = sum_v [sigma(class v)!=X]*a_v + [sigma!=Y]*b_v  (X=0,Y=1)
    cl=rows if typ==0 else cols
    best=10**9
    for l in labs:
        s=sum((l[cl[v]]!=0)*a[v]+(l[cl[v]]!=1)*b[v] for v in range(9))
        best=min(best,s+sum(e[i] for i in crossing(l)))
    return best
def adversary(P):
    """find (f,a,b) with every term in P failing: for each t exists sigma: s(sigma)+e_t(sigma) <= |E|-1."""
    nE=len(edges); nv=9
    # variables: fp[e], fm[e] (18 each), a[v], b[v] (9 each), y[t,l] (|P|*6)
    nP=len(P); nvar=2*nE+2*nv+nP*6
    def idx_fp(e): return e
    def idx_fm(e): return nE+e
    def idx_a(v): return 2*nE+v
    def idx_b(v): return 2*nE+nv+v
    def idx_y(t,li): return 2*nE+2*nv+t*6+li
    A=[];lo=[];hi=[]
    def add(row,l,h): A.append(row);lo.append(l);hi.append(h)
    for e in range(nE):
        r=np.zeros(nvar); r[idx_fp(e)]=1; r[idx_fm(e)]=1; add(r,0,1)
    for v in range(nv):
        # out - in = a - b ; a <= out ; b <= in ; in+out <= 4
        out=np.zeros(nvar); inn=np.zeros(nvar)
        for ei,(p,q) in enumerate(edges):
            if p==v: out[idx_fp(ei)]+=1; inn[idx_fm(ei)]+=1
            if q==v: out[idx_fm(ei)]+=1; inn[idx_fp(ei)]+=1
        r=out-inn; r[idx_a(v)]-=1; r[idx_b(v)]+=1; add(r,0,0)
        r=out.copy(); r[idx_a(v)]-=1; add(r,0,np.inf)
        r=inn.copy(); r[idx_b(v)]-=1; add(r,0,np.inf)
        add(out+inn,0,4)
    Evec=np.zeros(nvar)
    for v in range(nv): Evec[idx_a(v)]=1
    BIG=100
    for t,(typ,e) in enumerate(P):
        cl=rows if typ==0 else cols
        r=np.zeros(nvar)
        for li in range(6): r[idx_y(t,li)]=1
        add(r,1,np.inf)
        for li,l in enumerate(labs):
            # s(l) + e(l) - |E| + BIG*y <= BIG-1
            r=np.zeros(nvar)
            for v in range(nv):
                if l[cl[v]]!=0: r[idx_a(v)]+=1
                if l[cl[v]]!=1: r[idx_b(v)]+=1
            r-=Evec; r[idx_y(t,li)]=BIG
            add(r,-np.inf,BIG-1-sum(e[i] for i in crossing(l)))
    integrality=np.ones(nvar)
    lb=np.zeros(nvar); ub=np.full(nvar,np.inf); ub[:2*nE]=1; ub[2*nE+2*nv:]=1; ub[2*nE:2*nE+2*nv]=4
    c=-Evec  # maximise |E|
    res=milp(c,constraints=LinearConstraint(np.array(A),lo,hi),integrality=integrality,bounds=Bounds(lb,ub),options={"time_limit":240})
    if res.status not in (0,1) or res.x is None:
        if res.status==1: print("ADVERSARY TIMEOUT without solution: inconclusive",flush=True); return "timeout"
        return None
    x=np.round(res.x).astype(int)
    a=[x[idx_a(v)] for v in range(nv)]; b=[x[idx_b(v)] for v in range(nv)]
    f=[(x[idx_fp(e)],x[idx_fm(e)]) for e in range(nE)]
    return a,b,f
def cands(kappa):
    out=[]
    for typ in (0,1):
        for e in itertools.product(range(kappa+1),repeat=3):
            if sum(e)<=kappa: out.append((typ,e))
    return out
def svec(a,b):
    out=[]
    for typ in (0,1):
        cl=rows if typ==0 else cols
        out.append([sum((l[cl[v]]!=0)*a[v]+(l[cl[v]]!=1)*b[v] for v in range(9)) for l in labs])
    return out
EC=None
def prover(Ms,C):
    """min set cover of Ms by candidate terms C (vectorised)"""
    global EC
    if EC is None:
        EC=np.array([[sum(e[i] for i in crossing(l)) for l in labs] for (typ,e) in C])  # |C| x 6
        Ctyp=np.array([typ for typ,e in C])
    S=np.array([svec(a,b) for a,b in Ms])  # |Ms| x 2 x 6
    E=np.array([sum(a) for a,b in Ms])
    typs=np.array([typ for typ,e in C])
    Ssel=S[:,typs,:]  # |Ms| x |C| x 6
    bnd=(Ssel+EC[None,:,:]).min(axis=2)
    cov=(bnd>=E[:,None]).astype(float)
    if (cov.sum(axis=1)==0).any(): return None
    res=milp(np.ones(len(C)),constraints=LinearConstraint(cov,np.ones(len(Ms)),np.full(len(Ms),np.inf)),
             integrality=np.ones(len(C)),bounds=Bounds(0,1),options={"time_limit":600})
    if res.status!=0: return None
    return [C[j] for j in range(len(C)) if res.x[j]>0.5]
import pickle, os
from itertools import permutations
def images(a,b):
    out=set()
    for pr in permutations(range(3)):
        for pc in permutations(range(3)):
            for tr in (0,1):
                for sw in (0,1):
                    na=[0]*9; nb=[0]*9
                    for v,(r,c) in enumerate(nodes):
                        r2,c2=pr[r],pc[c]
                        if tr: r2,c2=c2,r2
                        w=nid[(r2,c2)]
                        na[w],nb[w]=(a[v],b[v]) if not sw else (b[v],a[v])
                    out.add((tuple(na),tuple(nb)))
    return out
C=cands(KAPPA)
P=[(0,(0,0,0)),(1,(0,0,0))]
Ms=[]
PK='Ms_%d.pkl'%KAPPA
if os.path.exists(PK): Ms=pickle.load(open(PK,'rb')); P=prover(Ms,C); print('resumed',len(Ms),P,flush=True)
for it in range(400):
    adv=adversary(P)
    if adv=="timeout": break
    if adv is None:
        print("PROFILE SURVIVES (kappa=%d):"%KAPPA,P); break
    a,b,f=adv
    print("iter",it,"|P|",len(P),"|Ms|",len(Ms),"adversary |E|",sum(a),"a",[int(x) for x in a],"b",[int(x) for x in b],flush=True)
    a=[int(x) for x in a]; b=[int(x) for x in b]
    for im in images(a,b):
        if im not in Ms: Ms.append(im)
    pickle.dump(Ms,open(PK,'wb'))
    P=prover(Ms,C)
    if P is None:
        print("NO PROFILE with kappa=%d covers these %d contractions => method proves cost >= %d"%(KAPPA,len(Ms),KAPPA+1)); break
