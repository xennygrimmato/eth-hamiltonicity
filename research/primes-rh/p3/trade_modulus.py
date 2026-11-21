"""Detection modulus d_Phi of a feature family: largest d such that 1_P = sum_phi lambda_phi W_phi (mod d)
on all m in [N,2N) (non-prime-power rows). Interval sums of Phi-features then reveal pi(segment) mod d, and
(profile-trade adversary) nothing finer. Tests primes l and prime powers via Z-lattice (sympy smith form on small cases).
Usage: python3 trade_modulus.py b"""
import numpy as np, sys
from collections import defaultdict
b=int(sys.argv[1]); N=2**b; M=2*N
spf=list(range(M+1))
for p in range(2,int(M**.5)+1):
    if spf[p]==p:
        for q in range(p*p,M+1,p):
            if spf[q]==q: spf[q]=p
divs=[[] for _ in range(M+1)]
for d in range(1,M+1):
    for m in range(d,M+1,d): divs[m].append(d)
box=lambda z: 0 if z==1 else z.bit_length()
def ppow(m):
    p=spf[m]
    while m%p==0: m//=p
    return m==1
rows=[m for m in range(N,M) if not(ppow(m) and spf[m]!=m)]
y=np.array([1 if spf[m]==m else 0 for m in rows],dtype=np.int64)
def feats(K):
    cols=defaultdict(lambda: np.zeros(len(rows),dtype=np.int64))
    def rec(m,k,acc):
        if k==1: yield tuple(sorted(acc+(box(m),))); return
        for d in divs[m]: yield from rec(m//d,k-1,acc+(box(d),))
    for i,m in enumerate(rows):
        for key in rec(m,K,()): cols[key][i]+=1
    return np.array([c for c in cols.values() if c.any()]).T
def solvable_mod_p(A,y,p):
    A=np.hstack([A%p,(y%p)[:,None]]).astype(np.int64); r=0; nr,nc=A.shape
    piv=[]
    for c in range(nc):
        rr=next((i for i in range(r,nr) if A[i,c]%p),None)
        if rr is None: continue
        A[[r,rr]]=A[[rr,r]]; A[r]=(A[r]*pow(int(A[r,c]),-1,p))%p
        nz=np.flatnonzero(A[:,c]); 
        for i in nz:
            if i!=r: A[i]=(A[i]-A[i,c]*A[r])%p
        piv.append(c); r+=1
    return (nc-1) not in piv
acc=None
for K in range(2,b):
    F=feats(K); acc=F if acc is None else np.hstack([acc,F])
    res={p:solvable_mod_p(acc,y,p) for p in [2,3,5,7]}
    print(f"K<={K}: features {acc.shape[1]}: 1_P in span mod p: {res}",flush=True)
