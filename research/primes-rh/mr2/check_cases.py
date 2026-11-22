# Brute-force check of the structural lemma behind Theorem A: for every odd composite n<=NMAX
# the strong liars lie in the subgroup H selected by the case analysis, and H is as claimed.
import sys
from sympy import factorint, jacobi_symbol
from math import gcd, isqrt
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 40000
def liars(n):
    d=n-1; s=0
    while d%2==0: d//=2; s+=1
    L=[]
    for a in range(1,n):
        x=pow(a,d,n)
        if x==1 or x==n-1: L.append(a); continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: L.append(a); break
    return L
def v2(x):
    k=0
    while x%2==0: x//=2; k+=1
    return k
stats={}
for n in range(9,NMAX,2):
    f=factorint(n)
    if len(f)==1 and list(f.values())[0]==1: continue
    L=liars(n); ps=sorted(f)
    if max(f.values())>=2:
        case='N'; p=[p for p in ps if f[p]>=2][0]
        ok=all(pow(a,p-1,p*p)==1 for a in L)            # H={a^(p-1)=1 mod p^2}, |H|=p-1<sqrt(p^2)
    else:
        q=ps[-1]; m=n//q; g=gcd(n-1,q-1)
        assert g==gcd(m-1,q-1) and g<=m-1
        if q>m*m:
            case='Q1'; ok=all(pow(a,g,q)==1 for a in L) and g*g<q
        elif q>m:
            case='Q2'; ok=all(pow(a,g,q)==1 for a in L) and (q-1)//g>=2 and (q-1)//g>=(q-1)/(m-1)
        else:
            bad=[p for p in ps if (n-1)%(p-1)]
            if bad:
                case='Q3a'; p=bad[0]; gp=gcd(n-1,p-1); ok=all(pow(a,gp,p)==1 for a in L) and p*p<n
            else:
                assert len(ps)>=3 and all(p*p<n for p in ps)
                vs=[v2(p-1) for p in ps]
                if len(set(vs))>1:
                    case='Carm-uneq'; p=ps[vs.index(max(vs))]; ok=all(jacobi_symbol(a,p)==1 for a in L)
                elif len(ps)>=4:
                    case='Carm-eq-k>=4'; ok=all(jacobi_symbol(a,ps[0])==jacobi_symbol(a,ps[1]) for a in L) and (ps[0]*ps[1])**2<=n
                else:
                    case='Carm3-eq'; ok=all(len({jacobi_symbol(a,p) for p in ps})==1 for a in L)
    assert ok,(n,case)
    stats[case]=stats.get(case,0)+1
print("all odd composite n <",NMAX,"OK; case counts:",stats)
