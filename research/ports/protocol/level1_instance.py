"""Exact-integer accounting for one instance of the two-bucket level-1 crossing protocol on K_{2,3}.
Usage: python3 level1_instance.py n1 e1 n2 e2
Classes Sigma_i = symbols (I,J), |I|=|J|=n_i, energy e_i ([AN] B.1/B.2).  Per block the demand is
u1u2: |Sigma1|^3, each v_iv_j: |Sigma2|.  Rank bounds are those of [AN] Prop. B.2(b),(c), summed over a bucket.
Outputs D1,D2, the bucket rank bound R, and the K->infinity rate  min(3P,Q)/(n*(P,Q,rho)+3)  (bits)."""
import sys, numpy as np
from math import log2, floor, ceil
from level1_lp import lp
n1,e1,n2,e2=map(int,sys.argv[1:5])
def distinct_odd(nmax,E):
    # c[n][e] = number of n-subsets of {1,3,5,...} with sum e  (exact ints)
    c=np.zeros((nmax+1,E+1),dtype=object); c[0,0]=1
    w=1
    while w<=E:
        c[1:,w:]+=c[:-1,:E+1-w].copy(); w+=2
    return c
def cls(n,e):
    c=distinct_odd(n,e)[n]
    return int(sum(c[a]*c[e-a] for a in range(e+1)))
def partitions(M):
    p=[1]+[0]*M
    for n in range(1,M+1):
        s=0;k=1
        while True:
            g1=k*(3*k-1)//2; g2=k*(3*k+1)//2
            if g1>n: break
            s+=(-1)**(k+1)*p[n-g1]
            if g2<=n: s+=(-1)**(k+1)*p[n-g2]
            k+=1
        p[n]=s
    return p
D1=cls(n1,e1); D2=cls(n2,e2)
Th=2*(e1+e2); N0=Th//2
p=partitions(N0//2+1)
# P(E) = #symbols of energy <= E = sum_{m<=E/2} p(m)
Pc=[0]*(Th+1); acc=0
for E in range(Th+1):
    if E%2==0 and E//2<len(p): acc+=p[E//2]
    Pc[E]=acc
Rb=sum((N+1)*Pc[N] for N in range(0,N0+1))            # bucket b: N<=N0, cut ad|bc
Rc=sum((Np+1)*Pc[Np] for Np in range(0,Th-N0))        # bucket c: N>N0, N'=Theta-N<=Theta-N0-1, cut ab|cd
R=max(Rb,Rc)
P=log2(D1);Q=log2(D2);rho=min(log2(R),P+Q)
print("D1 = |Sigma(%d,%d)| has %d bits (log2 %.3f); D2 = |Sigma(%d,%d)| log2 %.3f"%(n1,e1,D1.bit_length(),P,n2,e2,Q))
print("Theta %d, bucket threshold N0 %d, log2 R_b %.3f, log2 R_c %.3f, trivial log2(D1 D2) %.3f, saving %.3f bits"%(Th,N0,log2(Rb),log2(Rc),P+Q,P+Q-rho))
na=lp(('c','c','c'),P,Q,rho); nc=lp(('c','c','b'),P,Q,rho)
m=min(3*P,Q)
print("per-block demand bits m_blk = %.3f ; LP loads: acyclic %.4f cyclic %.4f ; +3 bits cover"%(m,na,nc))
print("rate (K->inf) = %.5f   [routing: 0.75 ; asymptotic 2-bucket: 0.83132 ; fine buckets: 0.83772]"%(m/(max(na,nc)+3)))
