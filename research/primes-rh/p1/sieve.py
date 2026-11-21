# segmented numpy sieve; writes primes <= LIM as uint32 .npy to scratch
import numpy as np, sys, math
LIM=int(float(sys.argv[1])); out=sys.argv[2]
r=int(math.isqrt(LIM))+1
s=np.ones(r+1,bool); s[:2]=False
for i in range(2,int(r**.5)+1):
    if s[i]: s[i*i::i]=False
small=np.nonzero(s)[0]
chunks=[]; SEG=10**7
for lo in range(0,LIM+1,SEG):
    hi=min(lo+SEG,LIM+1); seg=np.ones(hi-lo,bool)
    if lo==0: seg[:2]=False
    for p in small:
        if p*p>=hi: break
        st=max(p*p,((lo+p-1)//p)*p); seg[st-lo::p]=False
    chunks.append((np.nonzero(seg)[0]+lo).astype(np.uint32))
P=np.concatenate(chunks); np.save(out,P); print(len(P))
