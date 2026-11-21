#!/usr/bin/env python3
"""Conjecture PR, exhaustive test: for EVERY N in [2^k,2^(k+1)), k<=KMAX-1, the least j>=0 with
pi([N,N+2^j)) odd, restricted to j<=k (so the interval stays inside [N,2N)).
Output per dyadic block: histogram tail, max least j, number of N with NO odd j<=k ("doubling fails")."""
import numpy as np, sys, math, time
KMAX=int(sys.argv[1]) if len(sys.argv)>1 else 30
LIM=1<<KMAX
t=time.time()
half=LIM//2                      # index i <-> odd number 2i+1
s=np.ones(half,dtype=np.bool_); s[0]=False
for i in range(1,(math.isqrt(LIM)+1)//2+1):
    if s[i]:
        p=2*i+1; s[(p*p)//2::p]=False
# P[n] = #primes < n  mod 2, n=0..LIM
ind=np.zeros(LIM+1,dtype=np.uint8); ind[1::2][:half]=s; ind[2]=1; del s
P=np.empty(LIM+1,dtype=np.uint8); P[0]=0
np.bitwise_xor.accumulate(ind[:-1],out=P[1:]); del ind
print("sieve+prefix",round(time.time()-t,1),"s; pi(2^%d) parity check:"%KMAX,int(P[LIM]),flush=True)
print("k  count  maxleastj  fails(no odd j<=k)  mean  tail: #N with leastj>=J for J=k-8..k")
CH=1<<24
for k in range(4,KMAX-1):
    lo,hi=1<<k,1<<(k+1)
    hist=np.zeros(k+2,dtype=np.int64)   # hist[j]=#N with least j ==j ; hist[k+1]=fail
    for a in range(lo,hi,CH):
        b=min(hi,a+CH)
        idx=np.arange(a,b,dtype=np.int64)
        for j in range(0,k+1):
            if idx.size==0: break
            odd=(P[idx+(1<<j)]^P[idx]).astype(bool)
            hist[j]+=int(odd.sum()); idx=idx[~odd]
        hist[k+1]+=idx.size
        if k>=20 and idx.size and idx.size<=8: print("   fail N:",idx.tolist())
    tot=hist.sum(); cum=tot-np.cumsum(hist)+hist   # cum[J]=#N with least j>=J
    mx=max(j for j in range(k+2) if hist[j]); mean=(hist[:k+1]*np.arange(k+1)).sum()/max(1,hist[:k+1].sum())
    print(k,tot,mx if mx<=k else "FAIL",int(hist[k+1]),round(float(mean),3),[int(cum[J]) for J in range(max(0,k-8),k+2)],flush=True)
