# Exact (mod p) computation of the crossing-identity tensors Psi_N of [AN] Prop B.2
import numpy as np, itertools, sys
from math import comb
p=2147483629  # prime < 2^31
def symbols(size,energy):
    # pairs (I,J) of size-subsets of N with sum(2i+1)+sum(2j+1)=energy
    out=[]
    mx=energy//2+1
    subs={}
    for I in itertools.combinations(range(mx),size):
        e=sum(2*i+1 for i in I)
        if e<=energy: subs.setdefault(e,[]).append(I)
    for e1,L1 in subs.items():
        for J in subs.get(energy-e1,[]):
            for I in L1: out.append((I,J))
    return sorted(out)
def Bpoly(r,n,y):
    # coeff of t^n in (1+t)^r/(1+yt)^(r+1), evaluated at y (mod p)
    s=0
    for k in range(0,min(r,n)+1):
        m=n-k
        s+=comb(r,k)*comb(r+m,m)*pow(-y,m,p)
    return s%p
def Cpoly(r,n,y):
    s=0
    for k in range(0,min(r,n)+1):
        m=n-k
        s+=comb(r,k)*pow(y,k,p)*comb(r+m,m)*(-1)**m
    return s%p
def detmod(M):
    M=[row[:] for row in M]; n=len(M); det=1
    for c in range(n):
        piv=None
        for r in range(c,n):
            if M[r][c]%p: piv=r;break
        if piv is None: return 0
        if piv!=c: M[c],M[piv]=M[piv],M[c]; det=-det
        det=det*M[c][c]%p
        inv=pow(M[c][c],p-2,p)
        for r in range(c+1,n):
            f=M[r][c]*inv%p
            if f:
                Mr=M[r];Mc=M[c]
                for k in range(c,n): Mr[k]=(Mr[k]-f*Mc[k])%p
    return det%p
def build(sa,sb,sc,sd,X,Bt,Ct):
    y=X*X%p
    rows=[('a',i) for i in sa[0]]+[('d',i) for i in sd[0]]+[('c',i) for i in sc[0]]+[('b',i) for i in sb[0]]
    cols=[('a',j) for j in sa[1]]+[('d',j) for j in sd[1]]+[('c',j) for j in sc[1]]+[('b',j) for j in sb[1]]
    M=[]
    for (P,i) in rows:
        row=[]
        for (Q,j) in cols:
            xi=pow(X,2*i+1,p); xj=pow(X,2*j+1,p); dl=1 if i==j else 0
            k=P+Q
            if P==Q: v=0
            elif k=='ad': v=Ct[i][j]
            elif k=='ac': v=dl*xi
            elif k=='ab': v=(y-1)*xi*Bt[i][j]
            elif k=='da': v=-Ct[j][i]
            elif k=='dc': v=xj*Bt[j][i]
            elif k=='db': v=-dl*xi
            elif k=='ca': v=-dl*xi
            elif k=='cd': v=-xi*Bt[i][j]
            elif k=='cb': v=-(y-1)*Ct[i][j]
            elif k=='ba': v=-(y-1)*xj*Bt[j][i]
            elif k=='bd': v=dl*xi
            elif k=='bc': v=(y-1)*Ct[j][i]
            row.append(v%p)
        M.append(row)
    return M
def rankmod(A):
    A=A.copy()%p; r=0; m,n=A.shape
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i,c]: piv=i;break
        if piv is None: continue
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        inv=pow(int(A[r,c]),p-2,p)
        A[r]=A[r]*inv%p
        nz=np.nonzero(A[:,c])[0]
        for i in nz:
            if i!=r: A[i]=(A[i]-A[i,c]*A[r])%p
        r+=1
        if r==m: break
    return r
def psi(n1,e1,n2,e2):
    S1=symbols(n1,e1); S2=symbols(n2,e2)
    Th=2*(e1+e2); npts=Th+2
    mx=max(e1,e2)//2+1
    d1,d2=len(S1),len(S2)
    vals=np.zeros((npts,d1,d2,d1,d2),dtype=object)  # a,b,c,d
    for t in range(npts):
        X=t+2; y=X*X%p
        Bt=[[Bpoly(r,n,y) for n in range(mx)] for r in range(mx)]
        Ct=[[Cpoly(r,n,y) for n in range(mx)] for r in range(mx)]
        for ia,sa in enumerate(S1):
            for ib,sb in enumerate(S2):
                for ic,sc in enumerate(S1):
                    for id_,sd in enumerate(S2):
                        vals[t,ia,ib,ic,id_]=detmod(build(sa,sb,sc,sd,X,Bt,Ct))
    # interpolate: coefficients c_N with sum c_N X^N = val, degree <= Th+1 (check top coeff zero)
    V=[[pow(t+2,N,p) for N in range(npts)] for t in range(npts)]
    # invert Vandermonde mod p
    n=npts
    A=[V[i][:]+[1 if i==j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        piv=next(r for r in range(c,n) if A[r][c]%p)
        A[c],A[piv]=A[piv],A[c]
        inv=pow(A[c][c],p-2,p); A[c]=[a*inv%p for a in A[c]]
        for r in range(n):
            if r!=c and A[r][c]:
                f=A[r][c]; A[r]=[(a-f*b)%p for a,b in zip(A[r],A[c])]
    Vinv=[row[n:] for row in A]
    coef=np.zeros((npts,d1,d2,d1,d2),dtype=object)
    for N in range(npts):
        acc=0
        for t in range(npts): acc=acc+Vinv[N][t]*vals[t]
        coef[N]=acc%p
    return S1,S2,coef
if __name__=="__main__":
    n1,e1,n2,e2=map(int,sys.argv[1:5])
    S1,S2,coef=psi(n1,e1,n2,e2)
    d1,d2=len(S1),len(S2); Th=2*(e1+e2)
    print("dims",d1,d2,"Theta",Th,"top coeff zero:",not coef[Th+1].any())
    tot=sum(coef[N] for N in range(Th+1))%p
    # compare with identity: [J_c=I_a, I_c=J_a, J_b=I_d, I_b=J_d]
    ok=True;sign=None
    for ia,sa in enumerate(S1):
        for ib,sb in enumerate(S2):
            for ic,sc in enumerate(S1):
                for id_,sd in enumerate(S2):
                    want=(sc[1]==sa[0] and sc[0]==sa[1] and sb[1]==sd[0] and sb[0]==sd[1])
                    v=int(tot[ia,ib,ic,id_]); v=v-p if v>p//2 else v
                    if want:
                        if sign is None: sign=v
                        if v!=sign: ok=False
                    elif v!=0: ok=False
    print("identity (a) holds:",ok,"sign",sign)
    for N in range(Th+1):
        Tn=np.array(coef[N],dtype=object)
        if not Tn.any(): continue
        # rank across ab|cd : rows (a,b), cols (c,d)
        r_ab=rankmod(Tn.reshape(d1*d2,d1*d2))
        r_ad=rankmod(Tn.transpose(0,3,1,2).reshape(d1*d2,d2*d1))
        r_ac=rankmod(Tn.transpose(0,2,1,3).reshape(d1*d1,d2*d2))
        print("N",N,"rank ab|cd",r_ab,"rank ad|bc",r_ad,"rank ac|bd",r_ac)
