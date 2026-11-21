#!/usr/bin/env python3
"""PR* family: blocks B_i(N)=[N+(i-1)L, N+iL), i=1,2,...  For EVERY N in [2^k,2^(k+1)) the least i with pi(B_i) odd.
Prediction (fair coins): max over the 2^k values of N  ~  k + O(1), so K=2k blocks should never fail."""
import numpy as np, sys, math
KMAX=int(sys.argv[1]); L=int(sys.argv[2]); LIM=1<<KMAX
half=LIM//2; s=np.ones(half,dtype=np.bool_); s[0]=False
for i in range(1,(math.isqrt(LIM)+1)//2+1):
    if s[i]: p=2*i+1; s[(p*p)//2::p]=False
ind=np.zeros(LIM+1,dtype=np.uint8); ind[1::2][:half]=s; ind[2]=1; del s
P=np.empty(LIM+1,dtype=np.uint8); P[0]=0; np.bitwise_xor.accumulate(ind[:-1],out=P[1:]); del ind
print("L=%d;  k  max_N(least odd block index i)  #N with i>k  #N with i>2k"%L)
CH=1<<24
for k in range(12,KMAX-1):
    lo,hi=1<<k,1<<(k+1); mx=0; c1=c2=0
    for a in range(lo,hi,CH):
        idx=np.arange(a,min(hi,a+CH),dtype=np.int64); i=0
        while idx.size:
            i+=1
            if i*L>lo: break                      # stay inside [N,2N)
            odd=(P[idx+i*L]^P[idx+(i-1)*L]).astype(bool); idx=idx[~odd]
            if i==k: c1+=idx.size
            if i==2*k: c2+=idx.size
        mx=max(mx,i)
    print(k,mx,c1,c2,flush=True)
