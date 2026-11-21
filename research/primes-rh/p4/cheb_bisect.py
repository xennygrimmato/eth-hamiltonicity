# Chebyshev-certificate prime finder (weak goal): brute-force simulation of the counting oracle.
# w(n) >= log2(u-smooth part of n) for every n; F(I) = sum_{n in I} (floor(log2 n) - w(n)), additive, integer (scaled).
# F(I)>0 => bisect to n with F(n)>0 => n has a prime factor > u; factor n.
import numpy as np, sympy, math, sys
u=int(sys.argv[1]); rho=float(sys.argv[2]); A=float(sys.argv[3]); H=int(sys.argv[4])
R=int(u**rho); x=int(u**A); C=64
L=[0]+[int(C*math.log(R/e)) for e in range(1,R+1)]   # integer log weights, L[1]=C log R
L1=L[1]
# Lambda'_R(d) for d<=u
lam=np.zeros(u+1,dtype=np.int64)
for e in range(1,R+1):
    m=int(sympy.mobius(e))
    if m: lam[e::e]+=m*L[e]
cl=np.array([0]+[math.ceil(math.log2(d)) if d>1 else 0 for d in range(1,u+1)],dtype=np.int64)
W=lam**2*cl            # scaled by L1^2
W[:R+1]=0
smallp=list(sympy.primerange(2,R+1))
lo=x; hi=x+H
w=np.zeros(H,dtype=np.int64)   # scaled by L1^2
for d in range(R+1,u+1):
    if W[d]==0: continue
    st=(-lo)%d
    w[st::d]+=W[d]
    # higher powers m^k, k>=2
    q=d*d
    while q<hi:
        st=(-lo)%q; w[st::q]+=W[d]; q*=d
for p in smallp:
    q=p
    while q<hi:
        st=(-lo)%q; w[st::q]+=math.ceil(math.log2(p))*L1*L1; q*=p
fl=np.array([ (n).bit_length()-1 for n in range(lo,hi)],dtype=np.int64)
f=fl*L1*L1-w
print("u=%d R=%d x=%d A=%.2f H=%d  F(I)=%.3g  margin per n (bits)=%.3f  (1+rho^2)/(2rho)*log2u=%.2f log2x=%.2f"%(u,R,x,A,H,f.sum(),f.mean()/L1**2,(1+rho**2)/(2*rho)*math.log2(u),math.log2(x)))
# correctness: every n with f>0 has P+(n)>u
pos=np.nonzero(f>0)[0]
bad=0
for i in pos[:2000]:
    n=lo+int(i)
    if max(sympy.factorint(n))<=u: bad+=1
print("n with F(n)>0: %d of %d (fraction %.3f); smooth violators among first 2000: %d"%(len(pos),H,len(pos)/H,bad))
# bisection
pre=np.concatenate([[0],np.cumsum(f)])
a,b=0,H
assert pre[b]-pre[a]>0
steps=0
while b-a>1:
    mid=(a+b)//2; steps+=1
    if pre[mid]-pre[a]>0: b=mid
    else: a=mid
n=lo+a; p=max(sympy.factorint(n))
print("bisection: %d steps -> n=%d, largest prime factor %d > u=%d: %s"%(steps,n,p,u,p>u))
