"""Minimal K for which 1_P on [N,2N) is an exact combination of K-fold dyadic-box counts,
plain vs mu on SMALL factors only (z <= 2^s, node-sized), vs mu on any factor. Usage: python3 nonlin_K.py b s"""
import numpy as np, sys
from collections import defaultdict
b=int(sys.argv[1]); s=int(sys.argv[2]); N=2**b; M=2*N
spf=list(range(M+1))
for p in range(2,int(M**.5)+1):
    if spf[p]==p:
        for q in range(p*p,M+1,p):
            if spf[q]==q: spf[q]=p
def mu(n):
    r=1
    while n>1:
        p=spf[n]; n//=p
        if n%p==0: return 0
        r=-r
    return r
divs=[[] for _ in range(M+1)]
for d in range(1,M+1):
    for m in range(d,M+1,d): divs[m].append(d)
box=lambda z: 0 if z==1 else z.bit_length()
y=np.array([1.0 if spf[m]==m else 0.0 for m in range(N,M)])
def feats(K,mode):
    cols=defaultdict(lambda: np.zeros(N))
    def rec(m,k,acc,w):
        if k==1:
            yield tuple(sorted(acc+((box(m),),))),w; return
        for d in divs[m]:
            if d==m and k>1 and False: pass
            sm = mode=='any' or (mode=='small' and d<=2**s)
            if sm and mode!='plain':
                for sign,tag in ((mu(d),1),):
                    if sign: yield from rec(m//d,k-1,acc+((box(d),'mu'),),w*sign)
            yield from rec(m//d,k-1,acc+((box(d),),),w)
    for i,m in enumerate(range(N,M)):
        for key,w in rec(m,K,(),1): cols[key][i]+=w
    return np.array([c for c in cols.values() if c.any()]).T
for mode in ['plain','small','any']:
    for K in range(2,b+2):
        A=feats(K,mode)
        x,*_=np.linalg.lstsq(A,y,rcond=None); r=np.abs(y-A@x).max()
        print(mode,'K=',K,'feat',A.shape[1],'max resid %.2e'%r, flush=True)
        if r<1e-6 or A.shape[1]>2500: break
