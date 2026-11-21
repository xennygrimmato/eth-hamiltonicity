"""For windows [N,2N] (N<=5e5): how many cheap queries (total; then classes mod 2^j, j=1..4, in order) until one is odd?"""
import numpy as np, random
X=10**6; isp=np.ones(X+1,bool); isp[:2]=False
for i in range(2,1001):
    if isp[i]: isp[i*i::i]=False
random.seed(2); idx=np.arange(X+1); hist={}
for N in random.sample(range(1000,X//2),2000):
    seg=isp[N:2*N+1]; ii=idx[N:2*N+1]; qn=0; found=None
    qs=[(1,0)]+[(2**j,r) for j in range(1,6) for r in range(2**j)]
    for (q,r) in qs:
        qn+=1
        if seg[ii%q==r].sum()%2: found=qn; break
    hist[found]=hist.get(found,0)+1
print(sorted(hist.items(), key=lambda t:(t[0] is None, t[0])))
