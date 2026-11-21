# Idea 1/6 test: deterministic schedules for finding y with pi((x,y]) odd (then bisect to a prime).
# Schedules: (A) y_j = x + 2^j ; (B) y_j = 2x - 2^j (suffix) ; (C) y_j = x + j*floor(x/64).
# Also mod-M analogue: first j with pi((x, x+j*h]) != 0 mod M along a scan with step h.
import numpy as np, sys
from sieve import isprime_table
N=2*10**8
s=isprime_table(N); pi=np.cumsum(s,dtype=np.int32)
rng=np.random.default_rng(0)
xs=rng.integers(10**7,10**8,200000)
def first_odd(ys):
    # ys: array (len(xs), J) of y values; return first j with (pi[y]-pi[x]) odd, -1 if none
    par=((pi[ys]-pi[xs][:,None])&1).astype(bool)
    f=np.where(par.any(1),par.argmax(1),-1); return f
J=27
A=xs[:,None]+(1<<np.arange(J))[None,:]
fA=first_odd(A)
print("schedule A (x+2^j): first odd j  distribution of j - j0 where 2^j0 ~ log^2 x? max:",fA.max(), " none:",(fA<0).sum())
print(" hist", np.bincount(fA[fA>=0])[:J])
B=2*xs[:,None]-(1<<np.arange(J))[None,:]
fB=first_odd(B); print("schedule B (2x-2^j): max",fB.max(),"none",(fB<0).sum(), "hist",np.bincount(fB[fB>=0])[:12])
C=xs[:,None]+np.arange(1,65)[None,:]*(xs[:,None]//64)
fC=first_odd(C); print("schedule C (x+j x/64): max",fC.max(),"none",(fC<0).sum(),"P(j>=k):",[(fC>=k).mean().round(5) for k in range(0,12)])
# exhaustive worst case for schedule A over all x in [10^7, 10^7+5*10^6]
X=np.arange(10**7,10**7+5*10**6)
best=np.full(len(X),-1)
par0=pi[X]
for j in range(J-1,-1,-1):
    odd=((pi[X+(1<<j)]-par0)&1).astype(bool); best[odd]=j
print("exhaustive A on 5e6 consecutive x near 1e7: max first-odd j =",best.max(),"(2^j=",1<<best.max(),")  none:",(best<0).sum())
# independence: correlation of parities of pi on consecutive dyadic blocks (x, x+2^j] for large j
for j in [10,14,18,22]:
    p1=((pi[xs+(1<<j)]-pi[xs])&1); p2=((pi[xs+(2<<j)]-pi[xs+(1<<j)])&1)
    print(f"j={j}: P(odd)={p1.mean():.4f}  corr(next block)={np.corrcoef(p1,p2)[0,1]:+.4f}")
# mod-M scan: step h, first k with pi((x,x+kh]) - pi((x,x+(k-1)h]) not 0 mod M   (i.e. block count != 0 mod M)
for M,h in [(2,1),(6,20),(30,200),(210,2500)]:
    K=200; ys=xs[:,None]+h*np.arange(0,K+1)[None,:]
    cnt=np.diff(pi[ys],axis=1); good=(cnt%M)!=0
    f=np.where(good.any(1),good.argmax(1),-1)
    print(f"M={M} h={h} (mean count/block {h/np.log(5e7):.1f}): max blocks scanned={f.max()+1} none={ (f<0).sum()} mean={f.mean()+1:.2f}")
