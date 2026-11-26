# finite-size accounting for the 2-bucket level-1 scheme
import numpy as np, itertools, sys
from math import log2
from functools import lru_cache
from scipy.optimize import linprog
vp=[(2,3),(3,4),(2,4)]
def lp(types,P,Q,rho,ret=False):
    """types in {'c','b'}^3 ; P,Q,rho: log-dims (bits). c-bucket: r=rho, r'=P+Q (trivial); b-bucket mirrored."""
    H=list(range(5)); nh=5
    nl=3*2*nh*nh; nv=nl+3+6+1
    def li(e,t,a,b): return ((e*2+t)*nh+a)*nh+b
    FU=nl; FV=nl+3; NN=nl+9
    A_direct=np.zeros((6,nv)); A_uu=np.zeros(nv); A_vv=np.zeros((3,nv))
    def add(col,x,y,delta):
        if x==y or delta==0: return
        x,y=min(x,y),max(x,y)
        if x<2 and y>=2: A_direct[x*3+(y-2),col]+=delta
        elif x<2 and y<2: A_uu[col]+=delta
        else: A_vv[vp.index((x,y)),col]+=delta
    for e,(i,j) in enumerate(vp):
        r,rp=((rho,P+Q) if types[e]=='c' else (P+Q,rho))
        a,c,b,d=0,1,i,j
        for ia,o in enumerate(H):
            for ib,o2 in enumerate(H):
                col=li(e,0,ia,ib)
                add(col,a,o,P);add(col,b,o,Q);add(col,c,o2,P);add(col,d,o2,Q);add(col,o,o2,r)
                col=li(e,1,ia,ib)
                add(col,a,o,P);add(col,d,o,Q);add(col,b,o2,Q);add(col,c,o2,P);add(col,o,o2,rp)
    Aub=[];bub=[]
    for k in range(2):
        for l in range(3):
            row=A_direct[k*3+l].copy(); row[FU+l]+=1
            for pi,(x,y) in enumerate(vp):
                if l+2 in (x,y): row[FV+pi*2+k]+=1
            row[NN]=-1; Aub.append(row);bub.append(0)
    Aeq=[];beq=[]
    row=A_uu.copy(); row[FU:FU+3]-=1; Aeq.append(row);beq.append(0)
    for pi in range(3):
        row=A_vv[pi].copy(); row[FV+pi*2:FV+pi*2+2]-=1; Aeq.append(row);beq.append(0)
    for e in range(3):
        row=np.zeros(nv); row[e*2*nh*nh:(e+1)*2*nh*nh]=1; Aeq.append(row);beq.append(1)
    cvec=np.zeros(nv); cvec[NN]=1
    res=linprog(cvec,A_ub=np.array(Aub),b_ub=bub,A_eq=np.array(Aeq),b_eq=beq,bounds=[(0,None)]*nv,method='highs')
    return res if ret else res.fun
def worst(P,Q,rho):
    return max(lp(('c','c','c'),P,Q,rho),lp(('c','c','b'),P,Q,rho))
# symbol counts: sets S subset N with given size and sum(2i+1)=e  <-> count[size][e]
EM=int(sys.argv[1]) if len(sys.argv)>1 else 400
def setcounts(EM):
    # cnt[n][e] = number of n-subsets of N with sum (2i+1) = e
    nmax=int(EM**0.5)+2
    cnt=[[0]*(EM+1) for _ in range(nmax+1)]; cnt[0][0]=1
    for i in range(0,EM//2+1):
        w=2*i+1
        for n in range(nmax-1,-1,-1):
            row=cnt[n]; nxt=cnt[n+1]
            for e in range(EM-w,-1,-1):
                if row[e]: nxt[e+w]+=row[e]
    return cnt
if __name__=="__main__":
    cnt=setcounts(EM); nmax=len(cnt)-1
    # class size |Sigma(n,e)| = sum_{e1} cnt[n][e1]*cnt[n][e-e1]
    def cls(n,e): return sum(cnt[n][a]*cnt[n][e-a] for a in range(e+1))
    # P(E) = number of symbols with energy <= E
    tot=[0]*(EM+1)
    for n in range(nmax+1):
        for e in range(EM+1):
            c=cls(n,e)
            tot[e]+=c
    Pc=np.cumsum(np.array(tot,dtype=object))
    print("P(0..12)",list(Pc[:13]))
    print("lp check unit:",worst(1/3,1,np.hypot(1/3,1)),worst(1/3,1,4/3))
    best=None
    for e2 in range(20,EM//2,10):
        n2=max(range(nmax+1),key=lambda n:cls(n,e2)); D2=cls(n2,e2)
        # choose (n1,e1) with D1^3 ~ D2 (D1^3>=D2 smallest)
        cand=[]
        for e1 in range(2,e2+1,2):
            n1=max(range(nmax+1),key=lambda n:cls(n,e1)); D1=cls(n1,e1)
            if D1**3>=D2: cand.append((e1,n1,D1)); break
        if not cand: continue
        e1,n1,D1=cand[0]
        Th=2*(e1+e2)
        if Th//2>EM: break
        N0=Th//2
        Rb=sum((N+1)*int(Pc[N]) for N in range(0,N0+1))
        Rc=sum((Np+1)*int(Pc[Np]) for Np in range(0,Th-N0))
        Rm=max(Rb,Rc)
        P=log2(D1);Q=log2(D2);rho=min(log2(Rm),P+Q)
        rho_opt=min(log2(int(Pc[N0])),P+Q)   # optimistic: true rank ~ P(N)
        m=min(3*P,Q)
        n_=worst(P,Q,rho)+3; n_o=worst(P,Q,rho_opt)+3
        print("e1 %d n1 %d log2D1 %.1f | e2 %d n2 %d log2D2 %.1f | Theta %d log2R %.1f (opt %.1f) P+Q %.1f | rate %.4f  (optimistic rank~P(N): %.4f)"%(e1,n1,P,e2,n2,Q,Th,log2(Rm),log2(int(Pc[N0])),P+Q,m/n_,m/n_o),flush=True)
