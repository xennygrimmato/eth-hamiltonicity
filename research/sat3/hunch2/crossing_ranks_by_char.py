# Ranks of the crossing-identity terms Psi_N ([AN] Prop. B.2) by characteristic.
# Psi_N are INTEGER tensors.  We compute them modulo several 31-bit primes with
# ../../ports/protocol/crossing_identity_modp.py, lift to Z by CRT (checked against one more prime),
# and then compute the three flattening ranks modulo 2,3,5,7 and a large prime (= rank over Q
# unless an unlucky prime; two large primes are compared).
# usage: python3 crossing_ranks_by_char.py n1 e1 n2 e2
import sys, importlib.util, numpy as np
from math import gcd
spec=importlib.util.spec_from_file_location("cim","/home/user/eth-hamiltonicity/research/ports/protocol/crossing_identity_modp.py")
cim=importlib.util.module_from_spec(spec); spec.loader.exec_module(cim)
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primes_below(start,k):
    out=[]; n=start
    while len(out)<k:
        if isprime(n): out.append(n)
        n-=2
    return out
def rank_mod(A,q):
    A=np.array(A,dtype=object)%q
    A=A.astype(np.int64); r=0; m,n=A.shape
    for c in range(n):
        nz=np.nonzero(A[r:,c])[0]
        if len(nz)==0: continue
        piv=r+nz[0]
        if piv!=r: A[[r,piv]]=A[[piv,r]]
        inv=pow(int(A[r,c]),q-2,q)
        A[r]=(A[r]*inv)%q
        rows=np.nonzero(A[:,c])[0]
        for i in rows:
            if i!=r: A[i]=(A[i]-A[i,c]*A[r])%q
        r+=1
        if r==m: break
    return r
def integer_psi(n1,e1,n2,e2,nprimes=4):
    ps=primes_below(2147483629,nprimes+1)
    res=[]
    for q in ps:
        cim.p=q
        S1,S2,coef=cim.psi(n1,e1,n2,e2)
        res.append(coef)
    # CRT on the first nprimes, check on the last
    M=1; X=np.zeros(res[0].shape,dtype=object)
    for q,c in zip(ps[:nprimes],res[:nprimes]):
        # X = X + M * ((c - X) * M^{-1} mod q)
        inv=pow(M%q,q-2,q)
        X=X+M*(((c-X)%q)*inv%q)
        M*=q
    X=np.where(X>M//2,X-M,X)
    ok=bool(((X-res[nprimes])%ps[nprimes]==0).all())
    return S1,S2,X,ok,M
if __name__=="__main__":
    n1,e1,n2,e2=map(int,sys.argv[1:5])
    S1,S2,X,ok,M=integer_psi(n1,e1,n2,e2)
    d1,d2=len(S1),len(S2); Th=2*(e1+e2)
    mx=max(abs(int(v)) for v in X.flatten())
    print("classes",(n1,e1),(n2,e2),"dims",d1,d2,"Theta",Th,"CRT lift consistent with extra prime:",ok,"max|entry|",mx)
    g=0
    chars=[2,3,5,7,2147483629,2147483587]
    print("N | content | (ab|cd, ad|bc, ac|bd) ranks for char "+", ".join(map(str,chars)))
    drops=[]
    for N in range(Th+2):
        T=X[N]
        if not T.any(): continue
        cont=0
        for v in T.flatten(): cont=gcd(cont,abs(int(v)))
        fl=[T.reshape(d1*d2,d1*d2),T.transpose(0,3,1,2).reshape(d1*d2,d2*d1),T.transpose(0,2,1,3).reshape(d1*d1,d2*d2)]
        row=[]
        for q in chars:
            row.append(tuple(rank_mod(F,q) for F in fl))
        print(N,"|",cont,"|"," ".join(str(r) for r in row))
        for q,r in zip(chars,row):
            if r!=row[-1]: drops.append((N,q,r,row[-1]))
    print("rank drops (N, char, ranks, generic ranks):",drops if drops else "none")
